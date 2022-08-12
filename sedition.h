#line 2 "sedition.h"

#define _GNU_SOURCE
#undef NDEBUG

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

struct match_t;
typedef struct match_t match_t;

typedef bool regex_match_fun_t(match_t*, string*, size_t);
typedef regex_t re_t;

#define MAXGROUP 9
struct match_t {
    regex_match_fun_t *fun;
    struct {
        ptrdiff_t rm_so, rm_eo;
    } matches[MAXGROUP + 1];
};

static int lineNumber;
static int inputFileIndex;

//
// String functions (using only the public API from stringlib.h)
//

static void random_string(string* dst)
{
    uint8_t temp[16];
    ssize_t res = getrandom(temp, sizeof(temp), 0);
    assert(res == sizeof(temp));
    char buf[2 * sizeof(temp) + 1];

    for (size_t i = 0; i < sizeof(temp); i++) {
        snprintf(buf + 2 * i, 3, "%02x", temp[i]);
    }
    copy_cstr(dst, buf, 2 * sizeof(temp));
}

// Can be done more efficiently... An output buffer can be allocated on the
// string heap and added to the string, and when we reach the end of the input
// we can cut the last fragment down to size.
static void format_literal(string* dst, int width, string* s)
{
    int col = 0;
    free_string(dst);
    for (size_t i = 0; i < s->n_frags; i++) {
        const fragment *f = &s->frag[i];
        for (size_t j = f->start; j < f->end; j++) {
            uint8_t c = f->base[j];
            if (c == '\n') {
                append_str(dst, "$\n", 2);
                col = 0;
            } else if (c == '\\') {
                append_str(dst, "\\\\", 2);
                col += 2;
            } else if (!isprint(c) || c >= 128) {
                char buf[5];
                snprintf(buf, sizeof(buf), "\\%03o", c);
                append_str(dst, buf, 4);
                col += 4;
            } else {
                append_str(dst, (const char *)&c, 1);
                col++;
            }
            // TODO Should be breaking before output? I think the haskell also
            // gets this wrong if e.g. an octal escape straddles a line break.
            if (col >= width - 1) {
                append_str(dst, "\\\n", 2);
                col = 0;
            }
        }
    }
    append_str(dst, "$", 1);
}

static void format_int(string* dst, int i)
{
    char temp[32];
    snprintf(temp, sizeof(temp), "%d", i);
    copy_cstr(dst, temp, strlen(temp));
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
        for (int i = 0; i <= MAXGROUP; i++) {
            if (ref->matches[i].rm_so != m->matches[i].rm_so ||
                    ref->matches[i].rm_eo != m->matches[i].rm_eo) {
                fprintf(stderr, "%s: group %d should be %td..%td, not %td..%td\n",
                        function, i,
                        ref->matches[i].rm_so, ref->matches[i].rm_eo,
                        m->matches[i].rm_so, m->matches[i].rm_eo);
                diff = true;
            }
        }
    }
    if (diff) {
        size_t len;
        const char *str = get_compact_string(s, &len);
        fprintf(stderr, "%s: diff for regexp \"%s\"\n", function, original_re);
        fprintf(stderr, "%s: on input \"%.*s\"\n",
                function,
                (int)(len - offset), str + offset);
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
    m->fun = NULL;
    // Since regexec seems to set all unused matches to -1, do the same for
    // compare_regexp_matches.
    memset(&m->matches, 0xff, sizeof(m->matches));
}

__attribute__((noinline)) static bool copy_match(match_t* dst, match_t* src, bool src_result)
{
    memcpy(dst, src, sizeof(match_t));
    return src_result;
}

static bool match_regexp(match_t* m, string* s, size_t offset, re_t* regex,
                         regex_match_fun_t* fun)
{
    size_t len;
    const char *src = get_compact_string(s, &len);

    // Stop matching when we've consumed the whole string, but allow a zero
    // length match if it comes first?
    if (offset && offset >= len) {
        return false;
    }
    if (sizeof(regoff_t) < sizeof(ptrdiff_t)) {
        assert(len <= INT_MAX);
    }

    // May need to convert since glibc is dumb and uses 'int' for regoff_t...
    regmatch_t tmp_matches[MAXGROUP + 1];
    m->fun = fun;
    tmp_matches[0].rm_so = offset;
    tmp_matches[0].rm_eo = len;
    // REG_STARTEND with non-zero offset seems to imply REG_NOTBOL in glibc.
    const int flags = REG_STARTEND | (offset ? REG_NOTBOL : 0);
    int res = regexec(regex, src, MAXGROUP + 1, tmp_matches, flags);
    if (res != 0 && res != REG_NOMATCH) {
        fprintf(stderr, "regexec: error %d\n", res);
        abort();
    }
    for (int i = 0; i <= MAXGROUP; i++) {
        m->matches[i].rm_so = tmp_matches[i].rm_so;
        m->matches[i].rm_eo = tmp_matches[i].rm_eo;
    }
    return res == 0;
}

static bool next_match(match_t* dst, match_t* src, string* s)
{
    size_t offset = src->matches[0].rm_eo;
    // Try to handle regexpes that match the empty string. We should try every
    // position and also try at the end of the string.
    if (src->matches[0].rm_so == offset && offset < string_len(s)) {
        offset++;
    }
    return src->fun(dst, s, offset);
}

static void print_match(bool res, match_t* m, string* s)
{
    size_t len;
    const char *src = get_compact_string(s, &len);

    if (!res) {
        printf("\"%.*s\": NO MATCH\n", (int)len, src);
        return;
    }
    printf("\"%.*s\" MATCHED:\n", (int)len, src);
    for (int i = 0; i <= MAXGROUP; i++) {
        if (!i || (m->matches[i].rm_so >= 0 && m->matches[i].rm_eo >= 0)) {
            printf("\t%d: %td..%td\n",
                   i, m->matches[i].rm_so, m->matches[i].rm_eo);
            if (m->matches[i].rm_so > m->matches[i].rm_eo) {
                printf("ERROR! starts after end?\n");
            }
            if (m->matches[i].rm_so > len) {
                printf("ERROR! match starts outside string?\n");
            }
            if (m->matches[i].rm_eo > len) {
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
    size_t len;
    const char *buf = get_compact_string(s, &len);
    fwrite(buf, 1, len, fp);
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

static bool read_line(string* s, FILE* fp)
{
    if (fp == NULL) return false;

    // TODO Avoid the C-heap roundtrip for this...
    size_t alloc = 0;
    char* buf = NULL;
    ssize_t res = getline(&buf, &alloc, fp);
    if (res < 0) return false;

    // TODO Only increment on fd 0?
    lineNumber++;
    copy_cstr(s, buf, res);
    free(buf);
    strip_trailing_newline(s);
    return true;
}

static void read_file(string* s, FILE* fp)
{
    assert(fp);

    char buf[1024];
    free_string(s);
    while (true) {
        ssize_t res = fread(buf, 1, sizeof(buf), fp);
        if (res <= 0) break;
        append_str(s, buf, res);
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
