/*
 * Runtime for x86.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <memory.h>
#include <string.h>

#define INITIAL_HEAP_SIZE       (1 << 20)

/*
 * All blocks have the same format:
 *    1. there is a one-word header { size : 30; tag : 2 }
 *    2. a sequence of fields
 *
 * The size is in words.  The tags have the following
 * meanings:
 *    NORMAL_TAG: the fields are either pointers, or 31-bit integers
 *    STRING_TAG: the block is filled with opaque data
 *    FORWARD_TAG: the header is actually a forwarding pointer
 *
 * Block pointers always refer to the first field of the block,
 * not the header.
 */

/*
 * Basic size parameters.
 * The header is the width of a field.
 */
#define SIZEOF_FIELD    (sizeof(void *))
#define HEADER_SIZE     SIZEOF_FIELD
#define ALIGNUP(i)      (((i) + SIZEOF_FIELD - 1) & ~(SIZEOF_FIELD - 1))
#define MIN(i, j)       ((i) < (j) ? (i) : (j))

/*
 * Integers vs. pointers.
 */
#define IS_INT(i)       ((unsigned long) (i) & 1)

#define Val_int(i)       (((i) << 1) | 1)

/*
 * Block tags.
 */
#define NORMAL_TAG      0
#define STRING_TAG      1
#define FORWARD_TAG     2

/*
 * Header operations.
 */
#define GET_HEADER_SIZE(h)      ((h) >> 2)
#define GET_HEADER_TAG(h)       ((h) & 3)
#define GET_HEADER_FORWARD(h)   ((void *) ((h) & ~3))

#define MAKE_HEADER(s, t)       (((s) << 2) | (t))
#define MAKE_STRING_HEADER(s)   ((s) | STRING_TAG)
#define MAKE_FORWARD_HEADER(p)  (((unsigned long) (p)) | FORWARD_TAG)

/*
 * Get the value in a field of the block.
 */
#define FIELD(b, i)     (((void **) (b))[i])

#define HEADER_INDEX                    (-1)
#define GET_BLOCK_HEADER(b)             ((unsigned long) FIELD(b, HEADER_INDEX))
#define SET_BLOCK_HEADER(b, h)          (FIELD(b, HEADER_INDEX) = (void *) (h))

/************************************************************************
 * HEAP PARAMETERS
 ************************************************************************/

/*
 * Two memory areas: from/to space.
 */
static void *to_space;
static void *to_scan;
static void *to_next;

/*
 * From space.
 */
static unsigned long mem_size;
static unsigned long mem_live;
void *__mem_base;
void *__mem_next;
void *__mem_limit;

/*
 * Temporary spill space.
 */
void *__m_spills[100];

/*
 * Type of the exit continuation.
 */
typedef void (*VoidFunction)();

/*
 * Program functions.
 */
extern void __exit();
extern int __main(void *frame, void *exit);

/*
 * Debugging.
 */
static int trace_gc = 1;

/************************************************************************
 * ALLOCATION
 ************************************************************************/

/*
 * Allocate a block with the given number of words.
 * We assume there is space.
 */
static void *alloc_block(int tag, int i)
{
    void *blockp;

    /* Allocate the block */
    blockp = __mem_next + HEADER_SIZE;
    SET_BLOCK_HEADER(blockp, MAKE_HEADER(i, tag));
    memset(blockp, 0, i * SIZEOF_FIELD);

    /* Allocate */
    __mem_next += i * SIZEOF_FIELD + HEADER_SIZE;
    assert(__mem_next <= __mem_limit);

    return blockp;
}

/*
 * Allocate a closure with an empty environment.
 */
static void *alloc_closure(VoidFunction funp)
{
    void *blockp;

    blockp = alloc_block(NORMAL_TAG, 2);
    FIELD(blockp, 0) = funp;
    FIELD(blockp, 1) = 0;
    return blockp;
}

/*
 * Allocate a string.
 */
static char *alloc_string(char *s)
{
    char *blockp;
    int len;

    /* Copy it */
    len = ALIGNUP(strlen(s) + 1);
    blockp = __mem_next + HEADER_SIZE;
    SET_BLOCK_HEADER(blockp, MAKE_STRING_HEADER(len));
    strcpy(blockp, s);

    /* Allocate */
    __mem_next += len + HEADER_SIZE;
    assert(__mem_next <= __mem_limit);

    /* Return it */
    return blockp;
}

/*
 * Main function initializes the memory areas, then jumps.
 */
int main(int argc, char **argv)
{
    void *exitp;
	 int ret;

    /* Print GC messages */
    trace_gc = getenv("TRACE_GC") != 0;

    /* Allocate memory */
    mem_size = INITIAL_HEAP_SIZE;
    to_space = malloc(mem_size);
    __mem_base = malloc(mem_size);
    if(__mem_base == 0 || to_space == 0) {
        fprintf(stderr, "%s: no memory\n", argv[0]);
        return 1;
    }

    /* Initialize the memory area */
    __mem_next = __mem_base;
    __mem_limit = __mem_base + mem_size;

    /* Allocate a closure for the exit continuation */
    exitp = alloc_closure(__exit);

    /* Now execute the program */
    ret = __main(0, exitp);
	 printf("Return value: %i\n", ret >> 1);
	 exit(0);
}

/************************************************************************
 * UTILITIES
 ************************************************************************/

/*
 * Walk through the string and print the parts.
 */
static void print_string(void *blockp)
{
    unsigned long tag, header;

    if(blockp) {
        header = GET_BLOCK_HEADER(blockp);
        tag = GET_HEADER_TAG(header);
        switch(tag) {
        case STRING_TAG:
            printf("%s", (char *) blockp);
            break;
        default:
            fprintf(stderr, "print_string: illegal string\n");
            abort();
        }
    }
}

/*
 * Build a string from the integer.
 * Guaranteed this won't cause a garbage collection.
 */
void *__itoa(long i)
{
    char buffer[20];
    sprintf(buffer, "%ld", i);
    return alloc_string(buffer);
}

/*
 * Printing a string buffer.
 */
int __println(void *blockp)
{
    print_string(blockp);
    putchar('\n');
    return 0;
}

/*
 * Concat the string buffer.
 */
int __atoi(void *blockp)
{
    unsigned long header, tag;

    if(blockp == 0) {
        fprintf(stderr, "__atoi: nil pointer exception\n");
        abort();
    }

    header = GET_BLOCK_HEADER(blockp);
    tag = GET_HEADER_TAG(header);
    switch(tag) {
    case STRING_TAG:
        return Val_int(atoi(blockp));
        break;
    default:
        fprintf(stderr, "print_string: illegal string\n");
        abort();
    }
}

/*
 * Seg fault handler.
 */
int __seg_fault()
{
    fprintf(stderr, "M: uncaught runtime exception\n");
    exit(1);
}

/*
 * Uncaught exception handler.
 */
void __uncaught_exception()
{
    fprintf(stderr, "M: uncaught exception\n");
    exit(1);
}

/************************************************************************
 * GARBAGE COLLECTION
 ************************************************************************/

/*
 * Copy a block from the from_space to the to_space.
 * Leave a forwarding pointer.
 */
static void *copy_block(void *blockp)
{
    unsigned long size, header;
    void *top;
    int tag;

    /* Ignore blocks outside the from space */
    if(IS_INT(blockp) || blockp < __mem_base || blockp >= __mem_limit)
        return blockp;

    /* Check for a forwarding pointer */
    header = GET_BLOCK_HEADER(blockp);
    tag = GET_HEADER_TAG(header);
    if(tag == FORWARD_TAG)
        return GET_HEADER_FORWARD(header);

    /* Copy the block */
    size = GET_HEADER_SIZE(header) * SIZEOF_FIELD + HEADER_SIZE;
    top = to_next + HEADER_SIZE;
    memcpy(to_next, blockp - HEADER_SIZE, size);
    to_next += size;
    SET_BLOCK_HEADER(blockp, MAKE_FORWARD_HEADER(top));
    return top;
}

/*
 * When a block is scanned, look through it
 * for valid pointers, and copy the blocks.
 */
static void scan_block()
{
    unsigned long header, size;
    void *blockp, *ptrp;
    long i, tag;

    /* Get the size and the data space */
    blockp = to_scan + HEADER_SIZE;
    header = GET_BLOCK_HEADER(blockp);
    tag = GET_HEADER_TAG(header);
    size = GET_HEADER_SIZE(header);
    to_scan = blockp + size * SIZEOF_FIELD;

    /* Now look for pointers */
    switch(tag) {
    case NORMAL_TAG:
        /* Every field is a pointer */
        for(i = 0; i != size; i++) {
            ptrp = FIELD(blockp, i);
            if(IS_INT(ptrp) == 0)
                FIELD(blockp, i) = copy_block(ptrp);
        }
        break;

    case STRING_TAG:
        /* Strings can be ignored */
        break;

    default:
        fprintf(stderr, "illegal block in scan_block");
        exit(2);
    }
}

/*
 * Now scan all the copied blocks.
 */
static void scan()
{
    while(to_scan != to_next)
        scan_block();
}

/*
 * Register indexes.
 */
#define EAX             0
#define EBX             1
#define ECX             2
#define EDX             3
#define ESI             4
#define EDI             5
#define EBP             6
#define MAX_REGS        7

#define CALLER          7
#define MASK            8
#define REQUEST         9

/*
 * Garbage collector.
 * The argument is an array containing the registers.
 */
void gc(void **regs)
{
    void *from_space, *spills, *blockp, **blockpp;
    unsigned long request;
    int i, resize_flag;
    long *maskp, mask;
    unsigned long mem_free;

    /* Get the parameters */
    maskp = (long *) regs[MASK];
    request = (unsigned long) regs[REQUEST];

    /* If more than 50% used, increase the heap size */
    resize_flag = 0;
    if(mem_live + request > mem_size / 2) {
        free(to_space);
        resize_flag = 1;
        mem_size = mem_size * 2 + request;
        to_space = malloc(mem_size);
        if(to_space == 0) {
            fprintf(stderr, "Out of memory\n");
            exit(1);
        }
    }

    /* Set up the memory areas */
    to_scan = to_space;
    to_next = to_space;

    /* Print out the GC info */
    if(trace_gc) {
        fprintf(stderr, "Garbage collection from 0x%08x:\n", (unsigned int) regs[CALLER]);
        fprintf(stderr, "\tHeap size: %ld bytes\n", mem_size);
        fprintf(stderr, "\tRequest size: %ld bytes\n", request);
    }
    mask = *maskp++;
    for(i = 0; i != MAX_REGS; i++) {
        if(mask & (1 << i))
            regs[i] = copy_block(regs[i]);
    }
    spills = regs[EBP];
    while(1) {
        mask = *maskp++;
        if(mask == -1)
            break;
        blockp = to_next + HEADER_SIZE;
        blockpp = (void **) (spills + mask);
        *blockpp = copy_block(*blockpp);
    }

    /* Now scan the to_space */
    scan();

    /* Swap from/to space */
    from_space = __mem_base;
    __mem_base = to_space;
    __mem_next = to_next;
    __mem_limit = __mem_base + mem_size;
    to_space = from_space;

    /* Increase size of space? */
    if(resize_flag) {
        free(to_space);
        to_space = malloc(mem_size);
        if(to_space == 0) {
            fprintf(stderr, "Out of memory\n");
            exit(1);
        }
    }

    /* Print stats */
    mem_live = __mem_next - __mem_base;
    mem_free = mem_size - mem_live;
    if(trace_gc) {
        fprintf(stderr, "\tLive bytes: %ld\n", mem_live);
        fprintf(stderr, "\tHeap size: %ld bytes\n", mem_size);
        fprintf(stderr, "\tRequest size: %ld bytes\n", request);
        fprintf(stderr, "\tFree bytes: %ld\n", mem_size - mem_live);
    }
    if(mem_free < request) {
        if(trace_gc)
            fprintf(stderr, "\tNot enough free space, restarting collector\n");
        gc(regs);
    }
}
