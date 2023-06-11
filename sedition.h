#line 2 "sedition.h"

#define _GNU_SOURCE
#define NDEBUG

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <malloc.h>
#include <regex.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>

#define NOINLINE __attribute__((noinline))
#define FORCE_INLINE __attribute__((alwaysinline))
#define UNUSED __attribute__((unused))

// TODO Rename to YYTRACE use YYDEBUG for e.g. statistics collection.
#if ENABLE_YYDEBUG
#define YYDEBUG(fmt,...) fprintf(stderr, "%s: " fmt, __PRETTY_FUNCTION__, ## __VA_ARGS__)
#else
#define YYDEBUG(...) (void)0
#endif

#if ENABLE_YYSTATS
static struct {
    size_t retries;
    size_t matched_chars, visited_chars;
    size_t regops;
    size_t matched, failed;
    size_t early_out;
    size_t goto_nocheck;
} yystats;

#define YYSTATS(field, incr) (yystats.field += (incr))
#else
#define YYSTATS(field, incr) (void)0
#endif

struct string { char* buf; size_t len; size_t alloc; };
typedef struct string string;

#define MAXGROUP 9
#define MAXTAGS (2 * (MAXGROUP + 1))
struct match_t {
    ptrdiff_t tags[MAXTAGS];
};
typedef struct match_t match_t;
typedef match_t* tags_t;
typedef bool regex_match_fun_t(match_t*, string*, size_t);
typedef regex_t re_t;

static int lineNumber;
static int inputFileIndex;

//
// String functions
//

static size_t grow(size_t prev, size_t min)
{
    const size_t plus10 = prev + prev / 8;
    // Grow 12.5% or directly to the given size
    return min > plus10 ? min : plus10;
}

static void ensure_len_discard(string* s, size_t n)
{
    if (n > s->alloc) {
        n = grow(s->alloc, n);
        if (s->alloc) {
            free(s->buf);
        }
        s->buf = malloc(n);
        if (!s->buf) abort();
        s->alloc = malloc_usable_size(s->buf);
        s->len = 0;
    }
}

static void ensure_len(string* s, size_t n)
{
    if (n > s->alloc) {
        n = grow(s->alloc, n);
        if (s->alloc == 0) {
            // Copy static string to new heap buffer.
            char *new_buf = malloc(n);
            memcpy(new_buf, s->buf, s->len);
            s->buf = new_buf;
        } else {
            s->buf = realloc(s->buf, n);
        }
        if (!s->buf) abort();
        s->alloc = malloc_usable_size(s->buf);
    }
}

static size_t string_len(string* s)
{
    return s->len;
}

static void free_string(string* s)
{
    if (s->alloc > 0) {
        free(s->buf);
    }
    s->alloc = s->len = 0;
    s->buf = 0;
}

static void clear_string(string* s)
{
    s->len = 0;
}

// src must be a statically allocated string that we can keep a reference to
// without copying.
static void set_str_const(string* dst, const char* src, size_t n)
{
    if (dst->alloc) {
        free(dst->buf);
    }
    dst->alloc = 0;
    dst->buf = (char*)src;
    dst->len = n;
}

static void set_cstr(string* dst, const char* src, size_t n)
{
    ensure_len_discard(dst, n);
    memcpy(dst->buf, src, n);
    dst->len = n;
}

static void append_cstr(string* dst, const char *str, size_t n)
{
    assert(dst->buf + dst->len < str || dst->buf > str + n);
    ensure_len(dst, dst->len + n);
    memcpy(dst->buf + dst->len, str, n);
    dst->len += n;
}

static void append_char(string* dst, char c)
{
    ensure_len(dst, dst->len + 1);
    dst->buf[dst->len++] = c;
}

static void set_str(string* dst, string* src)
{
    assert(dst != src);
    ensure_len_discard(dst, src->len);
    memcpy(dst->buf, src->buf, src->len);
    dst->len = src->len;
}

static void concat_newline(string* dst, string* a, string* b)
{
    assert(dst != a && dst != b);
    const size_t n = a->len + 1 + b->len;
    ensure_len_discard(dst, n);

    char *p = mempcpy(dst->buf, a->buf, a->len);
    *p++ = '\n';
    memcpy(p, b->buf, b->len);
    dst->len = n;
}

static void concat(string* dst, string* a, string* b)
{
    assert(dst != a && dst != b);
    const size_t n = a->len + b->len;
    ensure_len_discard(dst, n);

    char *p = mempcpy(dst->buf, a->buf, a->len);
    memcpy(p, b->buf, b->len);
    dst->len = n;
}

static void append_str(string* dst, string* b)
{
    assert(dst != b);
    append_cstr(dst, b->buf, b->len);
}

static void append_substr(string* dst, string* src, ptrdiff_t i1, ptrdiff_t i2)
{
    assert(dst != src);
    // TODO Only necessary when the index refers to a group that could be
    // missing. Do this check at the call site, and only for matchstart/end
    // where it's possible to have missing values.
    if (i1 < 0 && i2 < 0) {
        return;
    }
    assert(0 <= i1);
    assert(0 <= i2);
    assert(i1 <= src->len);
    assert(i2 <= src->len);
    assert(i1 <= i2);

    append_cstr(dst, src->buf + i1, i2 - i1);
}

static void append_trans(string* dst, const char* from, const char* to, string* src)
{
    ensure_len(dst, dst->len + src->len);
    assert(strlen(to) == strlen(from));
    for (size_t i = 0; i < src->len; i++) {
        char c = src->buf[i];
        const char *p = strchr(from, c);
        if (p) {
            c = to[p - from];
        }
        dst->buf[dst->len++] = c;
    }
}

static void trans(string* dst, const char* from, const char* to, string* src)
{
    clear_string(dst);
    append_trans(dst, from, to, src);
}

static void append_random_string(string* dst)
{
    uint8_t temp[16];
    ssize_t res = getrandom(temp, sizeof(temp), 0);
    assert(res == sizeof(temp));

    char buf[33];
    for (size_t i = 0; i < sizeof(temp); i++) {
        snprintf(buf + 2 * i, 3, "%02x", temp[i]);
    }
    append_cstr(dst, buf, 32);
}

static void random_string(string* dst)
{
    clear_string(dst);
    append_random_string(dst);
}

static void format_literal(string* dst, int width, string* s)
{
    int col = 0;
    dst->len = 0;
    for (size_t i = 0; i < s->len; i++) {
        uint8_t c = s->buf[i];
        if (c == '\n') {
            append_cstr(dst, "$\n", 2);
            col = 0;
        } else if (c == '\\') {
            append_cstr(dst, "\\\\", 2);
            col += 2;
        } else if (!isprint(c) || c >= 128) {
            // one more here to have room for a NUL from snprintf
            append_cstr(dst, "\\ooo", 5);
            dst->len--;
            snprintf(dst->buf + dst->len - 3, 4, "%03o", c);
            col += 4;
        } else {
            append_cstr(dst, (const char *)&c, 1);
            col++;
        }
        // TODO Should be breaking before output? I think the haskell also gets
        // this wrong if e.g. an octal escape would straddle a line break.
        if (col >= width - 1) {
            append_cstr(dst, "\\\n", 2);
            col = 0;
        }
    }
    append_cstr(dst, "$", 1);
}

static void format_int(string* dst, int i)
{
    char temp[32];
    snprintf(temp, sizeof(temp), "%d", i);
    set_cstr(dst, temp, strlen(temp));
}

//
// Regex functions
//

static void compile_regexp(regex_t* re, const char* regexp, bool ere)
{
    int res = regcomp(re, regexp, ere ? REG_EXTENDED : 0);
    if (res) {
        fprintf(stderr, "regcomp: error %d in %s\n", res, regexp);
        abort();
    }
}

static void free_regexp(regex_t* re)
{
    regfree(re);
}

static void compare_regexp_matches(
        bool ref_match, match_t* ref,
        bool match, match_t* m,
        string* s, size_t offset,
        const char *function, const char *original_re)
{
    bool diff = false;
    if (ref_match != match) {
        fprintf(stderr, "%s: should %s, but did %s\n",
                function,
                ref_match ? "match" : "not match",
                match ? "match" : "not");
        diff = true;
    } else if (ref_match) {  // Only compare groups on match
        for (int i = 0; i < MAXTAGS; i += 2) {
            if (ref->tags[i] != m->tags[i] || ref->tags[i + 1] != m->tags[i + 1]) {
                fprintf(stderr, "%s: group %d should be %td..%td, not %td..%td\n",
                        function, i / 2,
                        ref->tags[i], ref->tags[i + 1],
                        m->tags[i], m->tags[i + 1]);
                diff = true;
            }
        }
    }
    if (diff) {
        fprintf(stderr, "%s: diff for regexp \"%s\"\n", function, original_re);
        fprintf(stderr, "%s: on input \"%.*s\"\n",
                function,
                (int)(s->len - offset), s->buf + offset);
    }
    assert(!diff);
}

static void tdfa2c_statistics() {
#if ENABLE_YYSTATS
    fprintf(stderr, "%zu retried matches\n", yystats.retries);
    fprintf(stderr, "%zu matched chars, %zu visited\n", yystats.matched_chars, yystats.visited_chars);
    fprintf(stderr, "%zu register operations performed\n", yystats.regops);
    fprintf(stderr, "%zu matches, %zu failed matches\n", yystats.matched, yystats.failed);
    fprintf(stderr, "%zu early outs due to string length\n", yystats.early_out);
    fprintf(stderr, "%zu EOF checks skipped thanks to minLength\n", yystats.goto_nocheck);
#endif
}

#if ENABLE_YYSTATS
void sigint_handler(int sig) {
    tdfa2c_statistics();
    exit(0);
}
#endif

static void enable_stats_on_sigint() {
#if ENABLE_YYSTATS
    signal(SIGINT, sigint_handler);
#endif
}

static void clear_match(match_t* m)
{
    // Since regexec seems to set all unused matches to -1, do the same for
    // compare_regexp_matches.
    memset(&m->tags, 0xff, sizeof(m->tags));
}

static void copy_match(match_t* dst, match_t* src)
{
    memcpy(dst, src, sizeof(match_t));
}

static bool match_regexp(match_t* m, string* s, size_t offset, re_t* regex)
{
    // Stop matching when we've consumed the whole string, but allow a zero
    // length match if it comes first?
    if (offset && offset >= s->len) {
        return false;
    }
    if (sizeof(regoff_t) < sizeof(ptrdiff_t)) {
        assert(s->len <= INT_MAX);
    }

    regmatch_t tmp_matches[MAXGROUP + 1];
    tmp_matches[0].rm_so = offset;
    tmp_matches[0].rm_eo = s->len;
    // REG_STARTEND with non-zero offset seems to imply REG_NOTBOL in glibc.
    const int flags = REG_STARTEND | (offset ? REG_NOTBOL : 0);
    int res = regexec(regex, s->buf, MAXGROUP + 1, tmp_matches, flags);
    if (res != 0 && res != REG_NOMATCH) {
        fprintf(stderr, "regexec: error %d\n", res);
        abort();
    }
    for (int i = 0; i <= MAXGROUP; i++) {
        m->tags[2 * i + 0] = tmp_matches[i].rm_so;
        m->tags[2 * i + 1] = tmp_matches[i].rm_eo;
    }
    return res == 0;
}

static bool next_match(match_t* dst, match_t* src, regex_match_fun_t fun, string* s)
{
    size_t offset = src->tags[1];
    // Try to handle regexpes that match the empty string. We should try every
    // position and also try at the end of the string.
    if (src->tags[0] == offset && offset < s->len) {
        offset++;
    }
    return fun(dst, s, offset);
}

static void print_match(bool res, match_t* m, string* s)
{
    if (!res) {
        printf("\"%.*s\": NO MATCH\n", (int)s->len, s->buf);
        return;
    }
    printf("\"%.*s\" MATCHED:\n", (int)s->len, s->buf);
    for (int i = 0; i < MAXTAGS; i += 2) {
        if (i == 0 || (m->tags[i] >= 0 && m->tags[i + 1] >= 0)) {
            printf("\t%d: %td..%td\n", i / 2, m->tags[i], m->tags[i + 1]);
            if (m->tags[i] > m->tags[i + 1]) {
                printf("ERROR! starts after end?\n");
            }
            if (m->tags[i] > s->len) {
                printf("ERROR! match starts outside string?\n");
            }
            if (m->tags[i + 1] > s->len) {
                printf("ERROR! match ends outside string?\n");
            }
        }
    }
}

//
// File and I/O functions
//

static void print(FILE* fp, string* s)
{
    assert(fp);
    fwrite(s->buf, 1, s->len, fp);
    fprintf(fp, "\n");
}

static bool is_eof(FILE* fp)
{
    if (fp == NULL) return true;

    int c = getc(fp);
    if (c == EOF) {
        return true;
    }
    ungetc(c, fp);
    return false;
}

static void strip_trailing_newline(string* s)
{
    if (s->buf[s->len - 1] == '\n') {
        s->len--;
    }
}

static bool read_line(string* s, FILE* fp)
{
    if (fp == NULL) return false;

    ssize_t res = getline(&s->buf, &s->alloc, fp);
    if (res < 0) return false;
    s->len = res;

    // TODO Only increment on fd 0?
    lineNumber++;
    strip_trailing_newline(s);
    return true;
}

static void read_file(string* s, FILE* fp)
{
    assert(fp);

    s->len = 0;
    ensure_len(s, 1024);
    while (true) {
        if (s->len == s->alloc) {
            ensure_len(s, s->alloc + 1);
        }
        ssize_t res = fread(s->buf + s->len, 1, s->alloc - s->len, fp);
        if (res <= 0) break;

        s->len += res;
    }

    strip_trailing_newline(s);
}

static FILE* next_input(int argc, const char *argv[])
{
    // Starts at 0, first input file is at argv[1]
    inputFileIndex++;
    if (inputFileIndex == 1 && argc == 1) {
        // No input files - use stdin
        return stdin;
    }
    if (argc > inputFileIndex) {
        return fopen(argv[inputFileIndex], "r");
    }
    // EOF
    return NULL;
}

static FILE* open_file(const char *path, bool write)
{
    return fopen(path, write ? "w" : "r");
}

static void close_file(FILE* fp)
{
    if (fp && fp != stdin) {
        fclose(fp);
    }
}

static bool is_all_eof(FILE** pfp, int argc, const char *argv[])
{
    FILE* fp = *pfp;
    while (fp && is_eof(fp)) {
        close_file(fp);
        fp = next_input(argc, argv);
    }
    *pfp = fp;
    return fp == NULL;
}

//
// IPC Functions: unimplemented mostly
//

static void wait_or_event(FILE* fp)
{
    // With IPC: check for either pending messages or a input on fp.
    // (I guess we should be looking for complete lines on fp, but as a cheat
    // we could also assume that seeing the start of a line means we will
    // eventually get the whole thing).
    // Without IPC: no-op, reading from a file will simply block instead.
}

static void get_message(string* s)
{
    fprintf(stderr, "UNIMPL: IPC get_message\n");
    abort();
}
