/*-
 * SPDX-License-Identifier: LicenseRef-scancode-bsd-unchanged
 *
 * Copyright (c) 2011-2025 Baptiste Daroussin <bapt@FreeBSD.org>
 * Copyright (c) 2011-2012 Julien Laffaye <jlaffaye@FreeBSD.org>
 * Copyright (c) 2011 Will Andrews <will@FreeBSD.org>
 * Copyright (c) 2011-2012 Marin Atanasov Nikolov <dnaeon@gmail.com>
 * Copyright (c) 2014 Vsevolod Stakhov <vsevolod@FreeBSD.org>
 * Copyright (c) 2015 Matthew Seaman <matthew@FreeBSD.org>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer
 *    in this position and unchanged.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR(S) ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR(S) BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifdef HAVE_CONFIG_H
#include "pkg_config.h"
#endif

#include <sys/resource.h>
#include <sys/types.h>
#ifdef HAVE_LIBJAIL
#include <sys/sysctl.h>
#endif
#include <sys/wait.h>
#include <sys/socket.h>
#include <sys/ioctl.h>

#include <err.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <time.h>
#include <signal.h>
#if __has_include(<libutil.h>)
#include <libutil.h>
#endif

#include <bsd_compat.h>

#include "pkg.h"
#include "pkgcli.h"
#include "xmalloc.h"

xstring *messages = NULL;
xstring *conflicts = NULL;

struct cleanup {
	void *data;
	void (*cb)(void *);
};

static char *progress_message = NULL;
static xstring *msg_buf = NULL;
static int last_progress_percent = -1;
static bool progress_started = false;
static bool progress_interrupted = false;
static bool progress_debit = false;
static int64_t last_tick = 0;
static int add_deps_depth;
static vec_t(struct cleanup *) cleanup_list = vec_init();
static bool signal_handler_installed = false;
static size_t nbactions = 0;
static size_t nbdone = 0;
static const char *action_verb = NULL;
static double progress_rate = 0;
static int64_t progress_last_ms = 0;
static int64_t progress_last_draw_ms = 0;

static void draw_progressbar(int64_t current, int64_t total);
static int pkgcli_getcols(void);
static int64_t pkgcli_now_ms(void);
static double pkgcli_humanize(int64_t bytes, const char **label);
static void pkgcli_fill_progress(int percent, int proglen);

static void
cleanup_handler(int sig)
{
	static const char msg[] = "\nsignal received, cleaning up\n";
	struct cleanup *ev;

	if (cleanup_list.len == 0) {
		signal(sig, SIG_DFL);
		kill(getpid(), sig);
		_exit(128 + sig);
	}
	write(STDERR_FILENO, msg, sizeof(msg) - 1);
	vec_foreach(cleanup_list, i) {
		ev = cleanup_list.d[i];
		ev->cb(ev->data);
	}
	signal(sig, SIG_DFL);
	kill(getpid(), sig);
	_exit(128 + sig);
}

void
job_status_end(xstring *msg)
{
	xstring_flush(msg);
	printf("%s\n", msg->buf);
	xstring_reset(msg);
}

void
job_status_begin(xstring *msg)
{
	int n;

	xstring_reset(msg);
#ifdef HAVE_LIBJAIL
	static char hostname[MAXHOSTNAMELEN] = "";
	static int jailed = -1;
	size_t intlen;

	if (jailed == -1) {
		intlen = sizeof(jailed);
		if (sysctlbyname("security.jail.jailed", &jailed, &intlen,
		    NULL, 0) == -1)
			jailed = 0;
	}

	if (jailed == 1) {
		if (hostname[0] == '\0')
			gethostname(hostname, sizeof(hostname));

		xstring_printf(msg, "[%s] ", hostname);
	}
#endif

	/* Only used for pkg-add right now. */
	if (add_deps_depth) {
		if (add_deps_depth > 1) {
			for (n = 0; n < (2 * add_deps_depth); ++n) {
				if (n % 4 == 0 && n < (2 * add_deps_depth))
					xstring_printf(msg, "|");
				else
					xstring_printf(msg, " ");
			}
		}
		xstring_printf(msg, "`-- ");
	}

	if ((nbtodl > 0 || nbactions > 0) && nbdone > 0) {
		xstring_printf(msg, "(%zu/%zu) ", nbdone, (nbtodl) ? (size_t)nbtodl : nbactions);
	}
	if (nbtodl > 0 && (size_t)nbtodl == nbdone) {
		nbtodl = 0;
		nbdone = 0;
	}
}

void
progressbar_start(const char *pmsg)
{
	if (progress_message) {
		free(progress_message);
		progress_message = NULL;
	}

	if (quiet)
		return;
	if (pmsg != NULL)
		progress_message = xstrdup(pmsg);
	else {
		xstring_flush(msg_buf);
		progress_message = xstrdup(msg_buf->buf);
	}
	last_progress_percent = -1;
	last_tick = 0;

	progress_started = true;
	progress_interrupted = false;
	progress_rate = 0;
	progress_last_ms = 0;
	progress_last_draw_ms = 0;
	if (!isatty(STDOUT_FILENO))
		printf("%s: ", progress_message);
	else
		draw_progressbar(0, 0);
}

void
progressbar_tick(int64_t current, int64_t total)
{
	int percent;

	if (!quiet && progress_started) {
		if (isatty(STDOUT_FILENO))
			draw_progressbar(current, total);
		else {
			if (progress_interrupted) {
				printf("%s...", progress_message);
			} else if (!getenv("NO_TICK")){
				percent = (total != 0) ? (current * 100. / total) : 100;
				if (last_progress_percent / 10 < percent / 10) {
					last_progress_percent = percent;
					putchar('.');
					fflush(stdout);
				}
			}
			if (current >= total)
				progressbar_stop();
		}
	}
	progress_interrupted = false;
}

void
progressbar_stop(void)
{
	if (progress_started) {
		if (!isatty(STDOUT_FILENO))
			printf(" done");
		putchar('\n');
	}
	last_progress_percent = -1;
	progress_started = false;
	progress_interrupted = false;
	action_verb = NULL;
}

static void
draw_progressbar(int64_t current, int64_t total)
{
	int percent, cols, infolen, filenamelen, barwidth;
	int64_t now;
	double xh, rh;
	const char *xl, *rl;
	unsigned int eta_h, eta_m, eta_s;

	if (!progress_started) {
		progressbar_stop();
		return;
	}

	percent = (total > 0) ? (int)((double)current * 100.0 / total) : 0;
	if (percent > 100)
		percent = 100;

	cols = pkgcli_getcols();
	infolen = cols * 6 / 10;
	if (infolen < 50)
		infolen = 50;

	now = pkgcli_now_ms();

	/* Redraw on completion, after an interruption, on percent change
	 * (transactions) or at most every 200ms (downloads). */
	if (!progress_interrupted && !(total > 0 && current >= total) &&
	    (progress_debit ? (now - progress_last_draw_ms < 200) :
	    (percent == last_progress_percent)))
		return;
	last_progress_percent = percent;
	progress_last_draw_ms = now;

	if (progress_debit) {
		if (progress_last_ms == 0) {
			progress_last_ms = now;
			last_tick = current;
		} else if (now > progress_last_ms) {
			progress_rate = (double)(current - last_tick) /
			    (double)(now - progress_last_ms) * 1000.0;
			last_tick = current;
			progress_last_ms = now;
		}

		filenamelen = infolen - 30;
		barwidth = cols - infolen - 1;

		printf("\r %-*s ", filenamelen, progress_message);

		xh = pkgcli_humanize(current, &xl);
		printf("%6.1f %3s  ", xh, xl);

		rh = pkgcli_humanize((int64_t)progress_rate, &rl);
		if (rh < 9.995)
			printf("%4.2f %3s/s ", rh, rl);
		else if (rh < 99.95)
			printf("%4.1f %3s/s ", rh, rl);
		else
			printf("%4.0f %3s/s ", rh, rl);

		if (total > 0 && progress_rate > 0) {
			eta_s = (unsigned int)((total - current) / progress_rate);
			eta_h = eta_s / 3600;
			eta_s -= eta_h * 3600;
			eta_m = eta_s / 60;
			eta_s -= eta_m * 60;
			if (eta_h == 0)
				printf("%02u:%02u", eta_m, eta_s);
			else if (eta_h == 1 && eta_m < 40)
				printf("%02u:%02u", eta_m + 60, eta_s);
			else
				fputs("--:--", stdout);
		} else {
			fputs("--:--", stdout);
		}

		pkgcli_fill_progress(percent, barwidth);
	} else {
		barwidth = cols - infolen - 2;
		printf("\r%-*s ", infolen, progress_message);
		pkgcli_fill_progress(percent, barwidth);
	}
	printf("\033[K");
	fflush(stdout);

	if (total > 0 && current >= total)
		progressbar_stop();
}

/* -------------------------------------------------------------------------
 * Parallel fetch progress, pacman style.
 *
 * The workers behind PKG_PARALLEL_JOBS report their progress through a
 * pipe (see pkg_parallel_fetch_child_init() in libpkg).  This renderer runs
 * in the parent, reads those records and draws one permanent line per
 * package, updated in place, exactly like pacman's download display.
 * ------------------------------------------------------------------------- */

struct pkgcli_dl {
	char *name;
	int64_t current;
	int64_t total;
	int64_t last_current;
	double rate;
	int64_t last_time;
	bool started;
	bool done;
};

static int64_t
pkgcli_now_ms(void)
{
	struct timespec ts;

	clock_gettime(CLOCK_MONOTONIC, &ts);
	return ((int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000);
}

/* Terminal width in columns (falling back to $COLUMNS or 80). */
static int
pkgcli_getcols(void)
{
	struct winsize ws;
	const char *env;
	char *end;
	long n;

	if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
		return ((int)ws.ws_col);
	if ((env = getenv("COLUMNS")) != NULL) {
		n = strtol(env, &end, 10);
		if (*end == '\0' && n > 0 && n < 10000)
			return ((int)n);
	}
	return (80);
}

/* Humanize a byte count like pacman's humanize_size() (base 1024). */
static double
pkgcli_humanize(int64_t bytes, const char **label)
{
	static const char *units[] = { "B", "KiB", "MiB", "GiB", "TiB", "PiB" };
	double v = (double)bytes;
	int i = 0;

	while (v >= 1024.0 && i < (int)NELEM(units) - 1) {
		v /= 1024.0;
		i++;
	}
	*label = units[i];
	return (v);
}

/* Draw the [####----] NNN% tail of a line, filling `proglen` columns. */
static void
pkgcli_fill_progress(int percent, int proglen)
{
	const int hashlen = proglen > 8 ? proglen - 8 : 0;
	const int hash = percent * hashlen / 100;
	int i;

	if (hashlen > 0) {
		fputs(" [", stdout);
		for (i = hashlen; i > 0; --i)
			putchar(i > hashlen - hash ? '#' : '-');
		putchar(']');
	}
	if (proglen >= 5)
		printf(" %3d%%", percent);
}

static void
pkgcli_dl_draw(struct pkgcli_dl *dl, int filenamelen, int barwidth)
{
	double xh, rh;
	const char *xl, *rl;
	unsigned int eta_h, eta_m, eta_s;
	int percent;

	percent = (dl->total > 0) ?
	    (int)((double)dl->current * 100.0 / dl->total) : 0;
	if (percent > 100)
		percent = 100;

	if (dl->total > 0 && dl->rate > 0) {
		eta_s = (unsigned int)((dl->total - dl->current) / dl->rate);
		eta_h = eta_s / 3600;
		eta_s -= eta_h * 3600;
		eta_m = eta_s / 60;
		eta_s -= eta_m * 60;
	} else {
		eta_h = eta_m = eta_s = 0;
	}

	printf("\r %-*s ", filenamelen, dl->name);

	xh = pkgcli_humanize(dl->current, &xl);
	printf("%6.1f %3s  ", xh, xl);

	rh = pkgcli_humanize((int64_t)dl->rate, &rl);
	if (rh < 9.995)
		printf("%4.2f %3s/s ", rh, rl);
	else if (rh < 99.95)
		printf("%4.1f %3s/s ", rh, rl);
	else
		printf("%4.0f %3s/s ", rh, rl);

	if (dl->total > 0 && dl->rate > 0) {
		if (eta_h == 0)
			printf("%02u:%02u", eta_m, eta_s);
		else if (eta_h == 1 && eta_m < 40)
			printf("%02u:%02u", eta_m + 60, eta_s);
		else
			fputs("--:--", stdout);
	} else {
		fputs("--:--", stdout);
	}

	pkgcli_fill_progress(percent, barwidth);
}

static void
pkgcli_dl_redraw(struct pkgcli_dl *slots, int nslots, int *lines_drawn)
{
	int64_t now = pkgcli_now_ms();
	int cols = pkgcli_getcols();
	int infolen = cols * 6 / 10;
	int filenamelen, barwidth;
	int ndrawn = 0, last = -1, i, pass;

	if (infolen < 50)
		infolen = 50;
	filenamelen = infolen - 30;
	barwidth = cols - infolen - 1;

	for (i = 0; i < nslots; i++)
		if (slots[i].started) {
			ndrawn++;
			last = i;
		}
	if (ndrawn == 0)
		return;

	/* Move up to the top of the previously drawn block.  The cursor sits
	 * on the last drawn line, so it is `lines_drawn - 1` rows above the
	 * block start; moving up `lines_drawn` rows would leave a ghost line
	 * behind on every redraw. */
	if (*lines_drawn > 1)
		printf("\033[%dA", *lines_drawn - 1);

	/* Completed downloads first, so they accumulate at the top of the
	 * block like pacman; the still-running ones stay at the bottom and
	 * never get mixed in with the finished lines. */
	for (pass = 0; pass < 2; pass++) {
		for (i = 0; i < nslots; i++) {
			struct pkgcli_dl *dl = &slots[i];

			if (!dl->started || dl->done != (pass == 0))
				continue;

			if (dl->last_time == 0) {
				dl->last_time = now;
				dl->last_current = dl->current;
			} else if (now > dl->last_time) {
				dl->rate = (double)(dl->current - dl->last_current) /
				    (double)(now - dl->last_time) * 1000.0;
				dl->last_current = dl->current;
				dl->last_time = now;
			}

			pkgcli_dl_draw(dl, filenamelen, barwidth);
			printf("\033[K");
			if (i != last)
				printf("\n");
		}
	}
	fflush(stdout);
	*lines_drawn = ndrawn;
}

int
pkgcli_parallel_fetch_render(int fd, int nslots, void *data __unused)
{
	struct pkgcli_dl *slots;
	FILE *fp;
	char *line = NULL, *p;
	size_t cap = 0;
	ssize_t len;
	int lines_drawn = 0;
	int64_t last_redraw = 0;
	bool tty = isatty(STDOUT_FILENO) != 0;
	int i;

	slots = xcalloc(nslots, sizeof(*slots));

	fp = fdopen(fd, "r");
	if (fp == NULL) {
		/* Extremely unlikely; at least make sure the workers never
		 * block on a full pipe. */
		char buf[4096];
		while (read(fd, buf, sizeof(buf)) > 0)
			;
		free(slots);
		return (EPKG_FATAL);
	}

	while ((len = getline(&line, &cap, fp)) != -1) {
		int slot;

		if (len < 3 || line[1] != ' ')
			continue;
		slot = atoi(line + 2);
		if (slot < 0 || slot >= nslots)
			continue;
		switch (line[0]) {
		case 'B':
			p = strchr(line + 2, ' ');
			if (p == NULL)
				break;
			p++;
			p[strcspn(p, "\r\n")] = '\0';
			free(slots[slot].name);
			slots[slot].name = xstrdup(p);
			slots[slot].current = 0;
			slots[slot].total = 0;
			slots[slot].last_current = 0;
			slots[slot].last_time = 0;
			slots[slot].rate = 0.0;
			slots[slot].started = true;
			slots[slot].done = false;
			if (tty && !quiet)
				pkgcli_dl_redraw(slots, nslots, &lines_drawn);
			break;
		case 'T':
			p = strchr(line + 2, ' ');
			slots[slot].current = (p != NULL) ? strtoll(p + 1, NULL, 10) : 0;
			p = (p != NULL) ? strchr(p + 1, ' ') : NULL;
			slots[slot].total = (p != NULL) ? strtoll(p + 1, NULL, 10) : 0;
			if (tty && !quiet &&
			    (pkgcli_now_ms() - last_redraw >= 100 ||
			    slots[slot].current >= slots[slot].total)) {
				last_redraw = pkgcli_now_ms();
				pkgcli_dl_redraw(slots, nslots, &lines_drawn);
			}
			break;
		case 'E':
			slots[slot].done = true;
			if (!tty && !quiet)
				printf(" %s\n", slots[slot].name != NULL ?
				    slots[slot].name : "unknown");
			else if (tty && !quiet)
				pkgcli_dl_redraw(slots, nslots, &lines_drawn);
			break;
		}
	}

	/* Finish whatever is still on screen. */
	if (tty && !quiet && lines_drawn > 0)
		printf("\n");
	else if (!tty && !quiet) {
		/* Report any package that never got a completion record (its
		 * worker failed partway through). */
		for (i = 0; i < nslots; i++)
			if (slots[i].started && !slots[i].done && slots[i].name != NULL)
				printf(" %s (failed)\n", slots[i].name);
	}

	/* The parallel fetch already accounted for the downloads, so the
	 * following install/upgrade steps restart their counters. */
	nbtodl = 0;
	nbdone = 0;

	free(line);
	for (i = 0; i < nslots; i++)
		free(slots[i].name);
	free(slots);
	fclose(fp);

	return (EPKG_OK);
}

static const char *
str_or_unknown(const char *str)
{
	if (str == NULL || str[0] == '\0')
		return "???";
	return str;
}

typedef int (*event_handler_fn)(struct pkg_event *ev, int *debug);

static int
event_cb_errno(struct pkg_event *ev, int *debug __unused)
{
	warnx("%s(%s): %s", ev->e_errno.func, ev->e_errno.arg,
	    strerror(ev->e_errno.no));
	return (0);
}

static int
event_cb_error(struct pkg_event *ev, int *debug __unused)
{
	warnx("%s", ev->e_pkg_error.msg);
	return (0);
}

static int
event_cb_notice(struct pkg_event *ev, int *debug __unused)
{
	if (!quiet)
		printf("%s\n", ev->e_pkg_notice.msg);
	return (0);
}

static int
event_cb_developer_mode(struct pkg_event *ev, int *debug __unused)
{
	warnx("DEVELOPER_MODE: %s", ev->e_pkg_error.msg);
	return (0);
}

static int
event_cb_update_add(struct pkg_event *ev, int *debug __unused)
{
	if (quiet || updating_catalogues || !isatty(STDOUT_FILENO))
		return (0);
	printf("\rPushing new entries %d/%d", ev->e_upd_add.done, ev->e_upd_add.total);
	if (ev->e_upd_add.total == ev->e_upd_add.done)
	        putchar('\n');
	return (0);
}

static int
event_cb_update_remove(struct pkg_event *ev, int *debug __unused)
{
	if (quiet || updating_catalogues || !isatty(STDOUT_FILENO))
		return (0);
	printf("\rRemoving entries %d/%d", ev->e_upd_remove.done, ev->e_upd_remove.total);
	if (ev->e_upd_remove.total == ev->e_upd_remove.done)
		putchar('\n');
	return (0);
}

static int
event_cb_fetch_begin(struct pkg_event *ev, int *debug __unused)
{
	const char *filename, *tmp;

	if (nbtodl > 0)
		nbdone++;
	if (quiet || updating_catalogues)
		return (0);
	filename = strrchr(ev->e_fetching.url, '/');
	if (filename != NULL) {
		filename++;
	} else {
		/*
		 * We failed at being smart, so display
		 * the entire url.
		 */
		filename = ev->e_fetching.url;
	}
	job_status_begin(msg_buf);
	progress_debit = true;
	tmp = strrchr(filename, '~');
	if (tmp != NULL)
		xstring_printf(msg_buf, "Fetching %.*s",
				(int)(tmp - filename), filename);
	else {
		tmp = strrchr(filename, '.');
		if (tmp != NULL && strcmp(tmp, ".pkg") == 0)
			xstring_printf(msg_buf, "Fetching %.*s",
					(int)(tmp - filename), filename);
		else
			xstring_printf(msg_buf, "Fetching %s",
					filename);
	}
	return (0);
}

static int
event_cb_fetch_finished(struct pkg_event *ev __unused, int *debug __unused)
{
	progress_debit = false;
	return (0);
}

static int
event_cb_install_begin(struct pkg_event *ev __unused, int *debug __unused)
{
	if (quiet)
		return (0);
	action_verb = "installing";
	return (0);
}

static int
event_cb_extract_begin(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	if (quiet)
		return (0);
	job_status_begin(msg_buf);
	pkg = ev->e_install_begin.pkg;
	if (action_verb != NULL) {
		fputs(action_verb, msg_buf->fp);
		fputc(' ', msg_buf->fp);
		pkg_fprintf(msg_buf->fp, "%n", pkg);
	} else
		pkg_fprintf(msg_buf->fp, "Extracting %n-%v", pkg, pkg);
	xstring_flush(msg_buf);
	return (0);
}

static int
event_cb_add_deps_begin(struct pkg_event *ev __unused, int *debug __unused)
{
	++add_deps_depth;
	return (0);
}

static int
event_cb_add_deps_finished(struct pkg_event *ev __unused, int *debug __unused)
{
	--add_deps_depth;
	return (0);
}

static int
event_cb_integritycheck_begin(struct pkg_event *ev __unused, int *debug __unused)
{
	if (quiet)
		return (0);
	printf("Checking integrity...");
	return (0);
}

static int
event_cb_integritycheck_finished(struct pkg_event *ev, int *debug __unused)
{
	if (quiet)
		return (0);
	printf(" done (%d conflicting)\n", ev->e_integrity_finished.conflicting);
	if (conflicts != NULL) {
		xstring_flush(conflicts);
		printf("%s", conflicts->buf);
		xstring_free(conflicts);
		conflicts = NULL;
	}
	return (0);
}

static int
event_cb_integritycheck_conflict(struct pkg_event *ev, int *debug)
{
	struct pkg_event_conflict *cur_conflict;

	if (*debug == 0)
		return (0);
	printf("\nConflict found on path %s between %s and ",
	    ev->e_integrity_conflict.pkg_path,
	    ev->e_integrity_conflict.pkg_uid);
	cur_conflict = ev->e_integrity_conflict.conflicts;
	while (cur_conflict) {
		if (cur_conflict->next)
			printf("%s, ", cur_conflict->uid);
		else
			printf("%s", cur_conflict->uid);

		cur_conflict = cur_conflict->next;
	}
	printf("\n");
	return (0);
}

static int
event_cb_deinstall_begin(struct pkg_event *ev __unused, int *debug __unused)
{
	if (quiet)
		return (0);
	action_verb = "removing";
	return (0);
}

static int
event_cb_delete_files_begin(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	if (quiet)
		return (0);
	job_status_begin(msg_buf);
	pkg = ev->e_install_begin.pkg;
	if (action_verb != NULL) {
		fputs(action_verb, msg_buf->fp);
		fputc(' ', msg_buf->fp);
		pkg_fprintf(msg_buf->fp, "%n", pkg);
	} else
		pkg_fprintf(msg_buf->fp, "Deleting files for %n-%v",
		    pkg, pkg);
	return (0);
}

static int
event_cb_upgrade_begin(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg_new, *pkg_old;

	if (quiet)
		return (0);
	pkg_new = ev->e_upgrade_begin.n;
	pkg_old = ev->e_upgrade_begin.o;

	switch (pkg_version_change_between(pkg_new, pkg_old)) {
	case PKG_DOWNGRADE:
		action_verb = "downgrading";
		break;
	case PKG_REINSTALL:
		action_verb = "reinstalling";
		break;
	case PKG_UPGRADE:
		action_verb = "upgrading";
		break;
	}
	return (0);
}

static int
event_cb_locked(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	pkg = ev->e_locked.pkg;
	pkg_printf("\n%n-%v is locked and may not be modified\n", pkg, pkg);
	return (0);
}

static int
event_cb_required(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	pkg = ev->e_required.pkg;
	pkg_printf("\n%n-%v is required by: %r%{%rn-%rv%| %}", pkg, pkg, pkg);
	if (ev->e_required.force == 1)
		fprintf(stderr, ", deleting anyway\n");
	else
		fprintf(stderr, "\n");
	return (0);
}

static int
event_cb_already_installed(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	if (quiet)
		return (0);
	pkg = ev->e_already_installed.pkg;
	pkg_printf("the most recent version of %n-%v is already installed\n",
			pkg, pkg);
	return (0);
}

static int
event_cb_not_found(struct pkg_event *ev, int *debug __unused)
{
	printf("Package '%s' was not found in "
	    "the repositories\n", ev->e_not_found.pkg_name);
	return (0);
}

static int
event_cb_missing_dep(struct pkg_event *ev, int *debug __unused)
{
	warnx("Missing dependency '%s'",
	    pkg_dep_name(ev->e_missing_dep.dep));
	return (0);
}

static int
event_cb_noremotedb(struct pkg_event *ev, int *debug __unused)
{
	fprintf(stderr, "Unable to open remote database \"%s\". "
	    "Try running '%s update' first.\n", ev->e_remotedb.repo,
	    getprogname());
	return (0);
}

static int
event_cb_nolocaldb(struct pkg_event *ev __unused, int *debug __unused)
{
	fprintf(stderr, "Local package database nonexistent!\n");
	return (0);
}

static int
event_cb_newpkgversion(struct pkg_event *ev __unused, int *debug __unused)
{
	newpkgversion = true;
	printf("New version of pkg detected; it needs to be "
	    "installed first.\n");
	return (0);
}

static int
event_cb_file_mismatch(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	pkg = ev->e_file_mismatch.pkg;
	pkg_fprintf(stderr, "%n-%v: checksum mismatch for %Fn\n", pkg,
	    pkg, ev->e_file_mismatch.file);
	return (0);
}

static int
event_cb_file_missing(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;

	pkg = ev->e_file_missing.pkg;
	pkg_fprintf(stderr, "%n-%v: missing file %Fn\n", pkg, pkg,
	    ev->e_file_missing.file);
	return (0);
}

static int
event_cb_dir_meta_mismatch(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;
	struct pkg_dir *dir;

	pkg = ev->e_file_meta_mismatch.pkg;
	dir = ev->e_dir_meta_mismatch.dir;
	pkg_fprintf(stderr, "%n-%v: %Dn [%S] %S -> %S\n", pkg, pkg, dir,
		    pkg_meta_attribute_tostring(ev->e_dir_meta_mismatch.attrib),
		    str_or_unknown(ev->e_dir_meta_mismatch.db_val),
		    str_or_unknown(ev->e_dir_meta_mismatch.fs_val));
	return (0);
}

static int
event_cb_file_meta_mismatch(struct pkg_event *ev, int *debug __unused)
{
	struct pkg *pkg;
	struct pkg_file *file;

	pkg = ev->e_file_meta_mismatch.pkg;
	file = ev->e_file_meta_mismatch.file;
	pkg_fprintf(stderr, "%n-%v: %Fn [%S] %S -> %S\n", pkg, pkg, file,
		    pkg_meta_attribute_tostring(ev->e_file_meta_mismatch.attrib),
		    str_or_unknown(ev->e_file_meta_mismatch.db_val),
		    str_or_unknown(ev->e_file_meta_mismatch.fs_val));
	return (0);
}

static int
event_cb_plugin_errno(struct pkg_event *ev, int *debug __unused)
{
	warnx("%s: %s(%s): %s",
	    pkg_plugin_get(ev->e_plugin_errno.plugin, PKG_PLUGIN_NAME),
	    ev->e_plugin_errno.func, ev->e_plugin_errno.arg,
	    strerror(ev->e_plugin_errno.no));
	return (0);
}

static int
event_cb_plugin_error(struct pkg_event *ev, int *debug __unused)
{
	warnx("%s: %s",
	    pkg_plugin_get(ev->e_plugin_error.plugin, PKG_PLUGIN_NAME),
	    ev->e_plugin_error.msg);
	return (0);
}

static int
event_cb_plugin_info(struct pkg_event *ev, int *debug __unused)
{
	if (quiet)
		return (0);
	printf("%s: %s\n",
	    pkg_plugin_get(ev->e_plugin_info.plugin, PKG_PLUGIN_NAME),
	    ev->e_plugin_info.msg);
	return (0);
}

static int
event_cb_incremental_update(struct pkg_event *ev, int *debug __unused)
{
	if (!quiet)
		printf("%s repository update completed. %d packages processed.\n",
		    ev->e_incremental_update.reponame,
		    ev->e_incremental_update.processed);
	return (0);
}

static int
event_cb_debug(struct pkg_event *ev, int *debug __unused)
{
	fprintf(stderr, "DBG(%d)[%d]> %s\n", ev->e_debug.level,
		(int)getpid(), ev->e_debug.msg);
	return (0);
}

static int
event_cb_query_yesno(struct pkg_event *ev, int *debug __unused)
{
	return (ev->e_query_yesno.deft ?
		query_yesno(true, ev->e_query_yesno.msg, "[Y/n]") :
		query_yesno(false, ev->e_query_yesno.msg, "[y/N]"));
}

static int
event_cb_query_select(struct pkg_event *ev, int *debug __unused)
{
	return query_select(ev->e_query_select.msg, ev->e_query_select.items,
		ev->e_query_select.ncnt, ev->e_query_select.deft);
}

static int
event_cb_sandbox_call(struct pkg_event *ev, int *debug __unused)
{
	return (pkg_handle_sandboxed_call(ev->e_sandbox_call.call,
			ev->e_sandbox_call.fd,
			ev->e_sandbox_call.userdata));
}

static int
event_cb_sandbox_get_string(struct pkg_event *ev, int *debug __unused)
{
	return (pkg_handle_sandboxed_get_string(ev->e_sandbox_call_str.call,
			ev->e_sandbox_call_str.result,
			ev->e_sandbox_call_str.len,
			ev->e_sandbox_call_str.userdata));
}

static int
event_cb_progress_start(struct pkg_event *ev, int *debug __unused)
{
	if (updating_catalogues)
		return (0);
	progressbar_start(ev->e_progress_start.msg);
	return (0);
}

static int
event_cb_progress_tick(struct pkg_event *ev, int *debug __unused)
{
	progressbar_tick(ev->e_progress_tick.current,
	    ev->e_progress_tick.total);
	return (0);
}

static int
event_cb_backup(struct pkg_event *ev __unused, int *debug __unused)
{
	xstring_printf(msg_buf, "Backing up");
	return (0);
}

static int
event_cb_restore(struct pkg_event *ev __unused, int *debug __unused)
{
	xstring_printf(msg_buf, "Restoring");
	return (0);
}

static int
event_cb_new_action(struct pkg_event *ev, int *debug __unused)
{
	nbactions = ev->e_action.total;
	nbdone = ev->e_action.current;
	return (0);
}

static int
event_cb_message(struct pkg_event *ev, int *debug __unused)
{
	if (messages == NULL)
		messages = xstring_new();
	xstring_printf(messages, "%s", ev->e_pkg_message.msg);
	return (0);
}

static int
event_cb_cleanup_callback_register(struct pkg_event *ev, int *debug __unused)
{
	struct cleanup *evtmp;

	if (!signal_handler_installed) {
		signal(SIGINT, cleanup_handler);
		signal_handler_installed = true;
	}
	evtmp = xmalloc(sizeof(struct cleanup));
	evtmp->cb = ev->e_cleanup_callback.cleanup_cb;
	evtmp->data = ev->e_cleanup_callback.data;
	vec_push(&cleanup_list, evtmp);
	return (0);
}

static int
event_cb_cleanup_callback_unregister(struct pkg_event *ev, int *debug __unused)
{
	struct cleanup *evtmp;

	if (!signal_handler_installed)
		return (0);
	vec_foreach(cleanup_list, i) {
		evtmp = cleanup_list.d[i];
		if (evtmp->cb == ev->e_cleanup_callback.cleanup_cb &&
		    evtmp->data == ev->e_cleanup_callback.data) {
			vec_remove_and_free(&cleanup_list, i, free);
			break;
		}
	}
	return (0);
}

static int
event_cb_conflicts(struct pkg_event *ev, int *debug __unused)
{
	const char *reponame = NULL;

	if (conflicts == NULL) {
		conflicts = xstring_new();
	}
	pkg_fprintf(conflicts->fp, "  - %n-%v",
	    ev->e_conflicts.p1, ev->e_conflicts.p1);
	if (pkg_repos_total_count() > 1) {
		pkg_get(ev->e_conflicts.p1, PKG_ATTR_REPONAME, &reponame);
		xstring_printf(conflicts, " [%s]",
		    reponame == NULL ? "installed" : reponame);
	}
	pkg_fprintf(conflicts->fp, " conflicts with %n-%v",
	    ev->e_conflicts.p2, ev->e_conflicts.p2);
	if (pkg_repos_total_count() > 1) {
		pkg_get(ev->e_conflicts.p2, PKG_ATTR_REPONAME, &reponame);
		xstring_printf(conflicts, " [%s]",
		    reponame == NULL ? "installed" : reponame);
	}
	xstring_printf(conflicts, " on %s\n",
	    ev->e_conflicts.path);
	return (0);
}

static int
event_cb_trigger(struct pkg_event *ev, int *debug __unused)
{
	if (!quiet) {
		if (ev->e_trigger.cleanup)
			printf("==> Cleaning up trigger: %s\n", ev->e_trigger.name);
		else
			printf("==> Running trigger: %s\n", ev->e_trigger.name);
	}
	return (0);
}

static int
event_cb_rc_script(struct pkg_event *ev, int *debug __unused)
{
	if (!quiet) {
		switch (ev->e_rc_script.action) {
		case PKG_RC_START:
			printf("Starting %s\n", ev->e_rc_script.name);
			break;
		case PKG_RC_STOP:
			printf("Stopping %s\n", ev->e_rc_script.name);
			break;
		case PKG_RC_RESTART:
			printf("Restarting %s\n", ev->e_rc_script.name);
			break;
		default:
			printf("Restarting %s\n", ev->e_rc_script.name);
			break;
		}
	}
	return (0);
}

static const event_handler_fn event_handlers[PKG_EVENT_LAST] = {
	[PKG_EVENT_INSTALL_BEGIN]                = event_cb_install_begin,
	[PKG_EVENT_DEINSTALL_BEGIN]              = event_cb_deinstall_begin,
	[PKG_EVENT_UPGRADE_BEGIN]                = event_cb_upgrade_begin,
	[PKG_EVENT_EXTRACT_BEGIN]                = event_cb_extract_begin,
	[PKG_EVENT_DELETE_FILES_BEGIN]            = event_cb_delete_files_begin,
	[PKG_EVENT_ADD_DEPS_BEGIN]               = event_cb_add_deps_begin,
	[PKG_EVENT_ADD_DEPS_FINISHED]            = event_cb_add_deps_finished,
	[PKG_EVENT_FETCH_BEGIN]                  = event_cb_fetch_begin,
	[PKG_EVENT_FETCH_FINISHED]               = event_cb_fetch_finished,
	[PKG_EVENT_UPDATE_ADD]                   = event_cb_update_add,
	[PKG_EVENT_UPDATE_REMOVE]                = event_cb_update_remove,
	[PKG_EVENT_INTEGRITYCHECK_BEGIN]         = event_cb_integritycheck_begin,
	[PKG_EVENT_INTEGRITYCHECK_FINISHED]      = event_cb_integritycheck_finished,
	[PKG_EVENT_INTEGRITYCHECK_CONFLICT]      = event_cb_integritycheck_conflict,
	[PKG_EVENT_NEWPKGVERSION]                = event_cb_newpkgversion,
	[PKG_EVENT_NOTICE]                       = event_cb_notice,
	[PKG_EVENT_DEBUG]                        = event_cb_debug,
	[PKG_EVENT_INCREMENTAL_UPDATE]           = event_cb_incremental_update,
	[PKG_EVENT_QUERY_YESNO]                  = event_cb_query_yesno,
	[PKG_EVENT_QUERY_SELECT]                 = event_cb_query_select,
	[PKG_EVENT_SANDBOX_CALL]                 = event_cb_sandbox_call,
	[PKG_EVENT_SANDBOX_GET_STRING]           = event_cb_sandbox_get_string,
	[PKG_EVENT_PROGRESS_START]               = event_cb_progress_start,
	[PKG_EVENT_PROGRESS_TICK]                = event_cb_progress_tick,
	[PKG_EVENT_BACKUP]                       = event_cb_backup,
	[PKG_EVENT_RESTORE]                      = event_cb_restore,
	[PKG_EVENT_ERROR]                        = event_cb_error,
	[PKG_EVENT_ERRNO]                        = event_cb_errno,
	[PKG_EVENT_ALREADY_INSTALLED]            = event_cb_already_installed,
	[PKG_EVENT_LOCKED]                       = event_cb_locked,
	[PKG_EVENT_REQUIRED]                     = event_cb_required,
	[PKG_EVENT_MISSING_DEP]                  = event_cb_missing_dep,
	[PKG_EVENT_NOREMOTEDB]                   = event_cb_noremotedb,
	[PKG_EVENT_NOLOCALDB]                    = event_cb_nolocaldb,
	[PKG_EVENT_FILE_MISMATCH]                = event_cb_file_mismatch,
	[PKG_EVENT_DEVELOPER_MODE]               = event_cb_developer_mode,
	[PKG_EVENT_PLUGIN_ERRNO]                 = event_cb_plugin_errno,
	[PKG_EVENT_PLUGIN_ERROR]                 = event_cb_plugin_error,
	[PKG_EVENT_PLUGIN_INFO]                  = event_cb_plugin_info,
	[PKG_EVENT_NOT_FOUND]                    = event_cb_not_found,
	[PKG_EVENT_NEW_ACTION]                   = event_cb_new_action,
	[PKG_EVENT_MESSAGE]                      = event_cb_message,
	[PKG_EVENT_FILE_MISSING]                 = event_cb_file_missing,
	[PKG_EVENT_CLEANUP_CALLBACK_REGISTER]    = event_cb_cleanup_callback_register,
	[PKG_EVENT_CLEANUP_CALLBACK_UNREGISTER]  = event_cb_cleanup_callback_unregister,
	[PKG_EVENT_CONFLICTS]                    = event_cb_conflicts,
	[PKG_EVENT_TRIGGER]                      = event_cb_trigger,
	[PKG_EVENT_FILE_META_MISMATCH]           = event_cb_file_meta_mismatch,
	[PKG_EVENT_DIR_META_MISMATCH]            = event_cb_dir_meta_mismatch,
	[PKG_EVENT_RC_SCRIPT]                    = event_cb_rc_script,
};
_Static_assert(NELEM(event_handlers) == PKG_EVENT_LAST,
    "event_handlers table size does not match pkg_event_t enum");

int
event_callback(void *data, struct pkg_event *ev)
{
	int *debug = data;

	if (msg_buf == NULL)
		msg_buf = xstring_new();

	/* Interrupt progressbar for most event types */
	if (progress_started && ev->type != PKG_EVENT_PROGRESS_TICK &&
	    ev->type != PKG_EVENT_FILE_META_OK &&
	    ev->type != PKG_EVENT_DIR_META_OK &&
	    !progress_interrupted) {
		putchar('\n');
		progress_interrupted = true;
	}

	if (ev->type < PKG_EVENT_LAST && event_handlers[ev->type] != NULL)
		return (event_handlers[ev->type](ev, debug));

	return (0);
}
