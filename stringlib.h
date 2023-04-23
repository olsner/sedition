#line 2 "stringlib.h"

#define _GNU_SOURCE

#include <assert.h>
#include <sys/mman.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct fragment {
    // buffer base
    const char *base;
    // Offsets from base.
    size_t start, end;
};
typedef struct fragment fragment;

#define NFRAG 16
struct string {
    fragment frag[NFRAG];
    uint8_t n_frags;
};
typedef struct string string;

// Public API. The "string" type is also by necessity public, but should be
// treated as opaque so we are free to modify the internal representation.
static void append_str(string* dst, const char *str, size_t n);
static void concat(string* dst, string* a, string* b);
static void concat_inplace(string* dst, string* b);
static void concat_newline(string* dst, string* a, string* b);
static void copy(string* dst, string* src);
static void copy_cstr(string* dst, const char* src, size_t n);
static void free_string(string* s);
static void set_str_const(string* dst, const char* src, size_t n);
static void substring(string* dst, string* src, size_t i1, size_t i2);
static void trans(string* dst, const char* from, const char* to, string* src);
static void strip_trailing_newline(string* s);

static void init_string_heap(string* strings, size_t n);
static void string_heap_stats();
static const char* get_compact_string(string* s, size_t *length);
static size_t string_len(const string* s);
// End of "public API"

struct header {
    // Does a bit of double duty:
    // - idle phase: NULL
    // - mark phase: NULL for unmarked, 1 for marked
    // - sweep: new address instead of 1
    // - compact: reset back to NULL when moved to new address
    char* gcdata;
    size_t length;
};
typedef struct header header;

#define GC_MARK (char*)1

static string* all_strings;
static size_t n_strings;

// Start of heap
static char *string_heap_start;
// Current position of heap
static char *string_heap_cur;
// End of current heap size
static char *string_heap_end;
// Absolute max heap size
static char *string_heap_maxend;

void init_string_heap(string* strings, size_t n)
{
    all_strings = strings;
    n_strings = n;
    memset(all_strings, 0, sizeof(string) * n);

    const size_t heap_vsize = (size_t)1 << 30;
    const size_t first_gc = heap_vsize;
    string_heap_start = mmap(NULL, heap_vsize, PROT_READ | PROT_WRITE,
            MAP_ANONYMOUS | MAP_PRIVATE | MAP_NORESERVE, -1, 0);
    string_heap_cur = string_heap_start;
    string_heap_end = string_heap_start + first_gc;
    string_heap_maxend = string_heap_start + heap_vsize;
}

static void gc_mark_frag(char* base)
{
    header* const headerp = (header *)base - 1;
    if (headerp->gcdata == NULL)
        headerp->gcdata = GC_MARK;
}

static char* gc_get_new_addr(const char* base)
{
    const header* const headerp = (const header *)base - 1;
    assert(headerp->gcdata);
    assert(headerp->gcdata != GC_MARK);
    return headerp->gcdata;
}

__attribute__((noinline)) static void gc_string_heap(const size_t need)
{
    char* const start = string_heap_start;
    char* const old_cur = string_heap_cur;
    char* const old_end = string_heap_end;

    // Iterate all_strings and mark all used fragments
    for (size_t i = 0; i < n_strings; i++) {
        const string* s = &all_strings[i];
        for (size_t j = 0; j < s->n_frags; j++) {
            gc_mark_frag((char*)s->frag[j].base);
        }
    }

    // Assign new addresses to all marked fragments
    char *new_address = start;
    for (char *cur = start; cur < old_cur;) {
        header* const headerp = (header *)cur;
        const size_t len = headerp->length + sizeof(header);
        cur += len;
        if (headerp->gcdata) {
            headerp->gcdata = new_address + sizeof(header);
            new_address += len;
        }
    }
    char* const new_cur = new_address;

    // Update: change all strings to reference the new fragment addresses
    for (size_t i = 0; i < n_strings; i++) {
        string* s = &all_strings[i];
        for (size_t j = 0; j < s->n_frags; j++) {
            fragment* f = &s->frag[j];
            f->base = gc_get_new_addr(f->base);
        }
    }
    // Compact: move all used fragments to their new places
    new_address = start;
    for (char *cur = start; cur < old_cur;) {
        header* const headerp = (header *)cur;
        const size_t len = headerp->length + sizeof(header);
        cur += len;
        if (headerp->gcdata) {
            assert(headerp->gcdata == new_address + sizeof(header));
            header* const new_headerp = (header *)new_address;
            memmove(new_address, headerp, len);
            new_headerp->gcdata = NULL;
            new_address += len;
        }
    }
    assert(new_address == new_cur);

    string_heap_cur = new_cur;

    // Expand the heap to double the used size.
    const size_t used_size = need + string_heap_cur - start;
    if (used_size > string_heap_end - string_heap_cur) {
        string_heap_end = string_heap_cur + used_size;
        // Limit the heap size to the actually allocated size.
        if (string_heap_end > string_heap_maxend) {
            string_heap_end = string_heap_maxend;
        }
        if (string_heap_cur + need > string_heap_maxend) {
            fprintf(stderr, "Out of memory :(\n");
            abort();
        }
    }

#if STRINGHEAP_DEBUG
    fprintf(stderr, "GC: %zu bytes [of %zu] -> %zu bytes [of %zu]\n",
            old_cur - string_heap_start, old_end - string_heap_start,
            used_size, string_heap_end - string_heap_start);
    string_heap_stats();
#endif
}

static char* new_fragment(size_t n)
{
    const size_t need = n + sizeof(header);
    assert(need < string_heap_maxend - string_heap_start);
    if (string_heap_cur + need > string_heap_end) {
#if STRINGHEAP_DEBUG
        fprintf(stderr, "Need %zu bytes but only %zu bytes left\n",
                need, string_heap_end - string_heap_cur);
#endif
        gc_string_heap(need);
    }
    header* const headerp = (header*)string_heap_cur;
    string_heap_cur += need;
    headerp->gcdata = NULL;
    headerp->length = n;
    return (char*)(headerp + 1);
}

size_t string_len(const string* s)
{
    size_t n = 0;
    for (size_t i = 0; i < s->n_frags; i++) {
        n += s->frag[i].end - s->frag[i].start;
    }
    return n;
}

static void set_frag(string* s, char *frag, size_t start, size_t end);

static void compact_string(string* s)
{
    if (s->n_frags > 1) {
        const size_t len = string_len(s);
        char *new_frag = new_fragment(len);
        char *p = new_frag;
        for (size_t i = 0; i < s->n_frags; i++) {
            fragment* f = &s->frag[i];
            p = mempcpy(p, f->base + f->start, f->end - f->start);
        }
        set_frag(s, new_frag, 0, len);
    }
}

const char* get_compact_string(string* s, size_t *length)
{
    compact_string(s);
    if (s->n_frags == 0) {
        *length = 0;
        return NULL;
    }
    assert(s->n_frags == 1);
    const fragment* f = &s->frag[0];
    *length = f->end - f->start;
    return f->base + f->start;
}

static void add_frag(string* s, char *frag, size_t start, size_t end)
{
    assert(s->n_frags < NFRAG);
    const size_t i = s->n_frags++;
    s->frag[i] = (fragment){frag, start, end};
}

static char* add_new_frag(string* s, size_t n)
{
    if (s->n_frags == NFRAG) {
        // TODO Since this kills any sharing from s anyway, we could allocate
        // space directly for the added 'n' bytes and return a pointer into the
        // buffer.
        compact_string(s);
    }
    char *frag = new_fragment(n);
    add_frag(s, frag, 0, n);
    return frag;
}

static void set_frag(string* s, char *frag, size_t start, size_t end)
{
    s->n_frags = 1;
    s->frag[0] = (fragment){frag, start, end};
}

void free_string(string* s)
{
    s->n_frags = 0;
    memset(s->frag, 0, sizeof(s->frag));
}

void set_str_const(string* dst, const char* src, size_t n)
{
    // No static-string optimization yet. Decide on a flag/something to allow
    // references to static strings.
    copy_cstr(dst, src, n);
}

void copy_cstr(string* dst, const char* src, size_t n)
{
    char *frag = new_fragment(n);
    memcpy(frag, src, n);
    set_frag(dst, frag, 0, n);
}

void append_str(string* dst, const char *src, size_t n)
{
    char *frag = add_new_frag(dst, n);
    memcpy(frag, src, n);
}

void copy(string* dst, string* src)
{
    dst->n_frags = src->n_frags;
    memcpy(dst->frag, src->frag, sizeof(fragment) * dst->n_frags);
}

void concat_newline(string* dst, string* a, string* b)
{
    // TODO Check if we'll need to compact the inputs to fit in dst, and be
    // a bit clever.
    copy(dst, a);
    append_str(dst, "\n", 1);
    concat_inplace(dst, b);
}

void concat(string* dst, string* a, string* b)
{
    if (b->n_frags > NFRAG - 1) {
        compact_string(b);
    }
    if (a->n_frags > NFRAG - b->n_frags) {
        compact_string(a);
    }
    size_t i = 0;
    for (size_t j = 0; j < a->n_frags; j++) {
        dst->frag[i++] = a->frag[j];
    }
    for (size_t j = 0; j < b->n_frags; j++) {
        dst->frag[i++] = b->frag[j];
    }
    assert(i <= NFRAG);
    dst->n_frags = i;
}

void concat_inplace(string* dst, string* b)
{
    assert(dst != b);
    if (dst->n_frags > NFRAG - b->n_frags) {
        compact_string(dst);
    }
    if (b->n_frags > NFRAG - dst->n_frags) {
        compact_string(b);
    }
    assert(dst->n_frags + b->n_frags <= NFRAG);
    size_t i = dst->n_frags;
    for (size_t j = 0; j < b->n_frags; j++) {
        dst->frag[i++] = b->frag[j];
    }
    assert(i <= NFRAG);
    dst->n_frags = i;
}

void substring(string* dst, string* src, const size_t i1, const size_t i2)
{
    assert(i1 <= i2);
    size_t i = 0;
    for (size_t j = 0, pos = 0; j < src->n_frags; j++) {
        const fragment* f = &src->frag[j];
        const size_t fstart = pos, fend = pos + (f->end - f->start);
        const size_t use_start = fstart > i1 ? fstart : i1;
        const size_t use_end = fend < i2 ? fend : i2;

        if (use_start < use_end) {
            dst->frag[i++] = (fragment){
                f->base,
                f->start + (use_start - fstart),
                f->start + (use_end - fstart) };
        }
        pos = fend;
    }
    assert(i <= NFRAG);
    dst->n_frags = i;
}

void trans(string* dst, const char* from, const char* to, string* src)
{
    const size_t len = string_len(src);
    char *frag = new_fragment(len);
    char *dstp = frag;
    for (size_t i = 0; i < src->n_frags; i++) {
        const fragment* f = &src->frag[i];
        for (size_t j = f->start; j < f->end; j++) {
            char c = f->base[j];
            const char *p = strchr(from, c);
            if (p) {
                c = to[p - from];
            }
            *dstp++ = c;
        }
    }
    assert(dstp == frag + len);
    set_frag(dst, frag, 0, len);
}

void strip_trailing_newline(string* s)
{
    if (s->n_frags > 0) {
        fragment* f = &s->frag[s->n_frags - 1];
        if (f->base[f->end - 1] == '\n') {
            f->end--;
        }
    }
}

void string_heap_stats()
{
    const size_t heap_bytes = string_heap_cur - string_heap_start;
    size_t live_strings = 0, bytes = 0, frags = 0;
    for (size_t i = 0; i < n_strings; i++) {
        const string* s = &all_strings[i];
        if (s->n_frags) {
            live_strings++;
            bytes += string_len(s);
            frags += s->n_frags;
        }
    }
    double compression = 100.0 * heap_bytes / bytes;

    fprintf(stderr, "%zu live strings with %zu bytes in %zu fragments\n",
            live_strings, bytes, frags);
    fprintf(stderr, "%zu bytes on heap (%.1f%%)\n", heap_bytes, compression);
}
