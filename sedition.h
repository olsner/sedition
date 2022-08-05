// START OF RTS

#define _GNU_SOURCE
#undef NDEBUG

#include <assert.h>
#include <regex.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>

struct string { char* buf; size_t len; size_t alloc; };
typedef struct string string;

#define MAXGROUP 9
struct match_t {
    // State for next_match
    const char *regexp;
    int cflags;

    bool result;
    regmatch_t matches[MAXGROUP + 1];
};
typedef struct match_t match_t;

static int lineNumber;
static int inputFileIndex;

//
// String functions
//

static void ensure_len_discard(string* s, size_t n)
{
    if (n > s->alloc) {
        free(s->buf);
        s->buf = malloc(n);
        if (!s->buf) abort();
        s->alloc = n;
        s->len = 0;
    }
}

static void free_string(string* s)
{
    free(s->buf);
    s->alloc = s->len = 0;
    s->buf = 0;
}

static void store_cstr(string* dst, const char* src, size_t n)
{
    ensure_len_discard(dst, n);
    memcpy(dst->buf, src, n);
    dst->len = n;
}

static void copy(string* dst, string* src)
{
    ensure_len_discard(dst, src->len);
    memcpy(dst->buf, src->buf, src->len);
    dst->len = src->len;
}

static void concat_newline(string* dst, string* a, string* b)
{
    const size_t n = a->len + 1 + b->len;
    ensure_len_discard(dst, n);

    char *p = mempcpy(dst->buf, a->buf, a->len);
    *p++ = '\n';
    memcpy(p, b->buf, b->len);
    dst->len = n;
}

static void concat(string* dst, string* a, string* b)
{
    const size_t n = a->len + b->len;
    ensure_len_discard(dst, n);

    char *p = mempcpy(dst->buf, a->buf, a->len);
    memcpy(p, b->buf, b->len);
    dst->len = n;
}

static void substring(string* dst, string* src, size_t i1, size_t i2)
{
    assert(i1 <= src->len && i2 <= src->len);
    assert(i1 <= i2);
    const size_t n = i2 - i1;
    ensure_len_discard(dst, n);
    memcpy(dst->buf, src->buf + i1, n);
    dst->len = n;
}

static void trans(string* dst, const char* from, const char* to, string* src)
{
    ensure_len_discard(dst, src->len);
    assert(strlen(to) >= strlen(from));
    for (size_t i = 0; i < src->len; i++) {
        char c = src->buf[i];
        const char *p = strchr(from, c);
        if (p) {
            c = to[p - from];
        }
        dst->buf[i] = c;
    }
    dst->len = src->len;
}

static void random_string(string* dst)
{
    uint8_t temp[16];
    getrandom(temp, sizeof(temp), 0);

    ensure_len_discard(dst, 2 * sizeof(temp) + 1);
    for (size_t i = 0; i < sizeof(temp); i++) {
        snprintf(dst->buf + 2 * i, 3, "%02x", temp[i]);
    }
    dst->len = 2 * sizeof(temp);
}

//
// Regex functions
//

static void match_regexp(match_t* m, string* s, const char* regexp, int cflags,
                         size_t offset)
{
    memset(m, 0, sizeof(*m));

    if (offset >= s->len) {
        return;
    }

    regex_t re;
    int res = regcomp(&re, regexp, cflags);
    if (res) {
        fprintf(stderr, "regcomp: error %d in %s\n", res, regexp);
        abort();
    }

    m->regexp = regexp;
    m->cflags = cflags;
    m->matches[0].rm_so = offset;
    m->matches[0].rm_eo = s->len;
    res = regexec(&re, s->buf, MAXGROUP, m->matches, REG_STARTEND);
    if (res != 0 && res != REG_NOMATCH) {
        fprintf(stderr, "regexec: error %d in %s\n", res, regexp);
        abort();
    }
    regfree(&re);
    m->result = (res == 0);
}

static void copy_match(match_t* dst, match_t* src)
{
    memcpy(dst, src, sizeof(match_t));
}

static void next_match(match_t* dst, match_t* src, string* s)
{
    match_regexp(dst, s, src->regexp, src->cflags, src->matches[0].rm_eo);
}

//
// File and I/O functions
//

static void file_printf(FILE* fp, const char* fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    assert(fp);
    vfprintf(fp, fmt, ap);
    va_end(ap);
}

static void print(FILE* fp, string* s)
{
    assert(fp);
    fwrite(s->buf, 1, s->len, fp);
    fprintf(fp, "\n");
}

static void write_file(const char* path, string* s)
{
    // TODO Should generate code to open a file, keep it open and write to it
    // instead.
    FILE* fp = fopen(path, "a");
    print(fp, s);
    fclose(fp);
}

static void print_lit(FILE* fp, int width, string* s)
{
    print(fp, s);
}

static bool is_eof(FILE* fp)
{
    assert(fp);
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

    ssize_t res = getline(&s->buf, &s->alloc, fp);
    if (res < 0) return false;

    lineNumber++;
    if (s->buf[res-1] == '\n') {
        res--;
    }
    s->len = res;
    return true;
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

// END OF RTS
