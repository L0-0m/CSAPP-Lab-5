/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/

team_t team = {
    /* Team name */

    /* First member's full name */

    /* First member's email address */
    "rzwang@mail.ustc.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)  ((void *)(bp) - WSIZE)
#define FTRP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLK(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLK(bp)  ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/* 计算free_list中指针的next和prev */
/* 讲最小free块中空余的两个words用于维护空闲指针信息
*/
#define GET_NEXT_PTR(bp)  (*(char **)(bp + WSIZE))
#define GET_PREV_PTR(bp)  (*(char **)(bp))

/* 空闲指针中放元素 */
#define SET_NEXT_PTR(bp, qp) (GET_NEXT_PTR(bp) = qp)
#define SET_PREV_PTR(bp, qp) (GET_PREV_PTR(bp) = qp)

static char *heap_listp = 0; 
static char *free_list_start = 0;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 维护free_list*/
static void insert_in_free_list(void *bp); 
static void remove_from_free_list(void *bp); 


/**
 * Initialize the memory manager.
 * 初始创建大小为4提高空间利用率
 */
int mm_init(void) {
  
  /* Create the initial empty heap. */
  if ((heap_listp = mem_sbrk(8*WSIZE)) == NULL) 
    return -1;

  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  free_list_start = heap_listp + 2*WSIZE; 

  /* Extend the empty heap with a free block of minimum possible block size */
  if (extend_heap(4) == NULL){ 
    return -1;
  }
  return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) 
{
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  void *bp;

  /* Ignore spurious requests. */
  if (size == 0)
    return (NULL);

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

  /* Search the free list for a fit. */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return (bp);
  }

  /* No fit found.  Get more memory and place the block. */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
    return (NULL);
  place(bp, asize);
  return (bp);
} 

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp){
  size_t size;
  /* Ignore spurious requests. */
  if (bp == NULL)
    return;
  /* Free and coalesce the block. */
  size = GET_SIZE(HDRP(bp));
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * 再分配
 */
void *mm_realloc(void *bp, size_t size){
  if((int)size < 0) 
    return NULL; 
  else if((int)size == 0){ 
    mm_free(bp); 
    return NULL; 
  } 
  else if(size > 0){ 
      size_t oldsize = GET_SIZE(HDRP(bp)); 
      size_t newsize = size + 2 * WSIZE; // header + footer
      
      if(newsize <= oldsize){ 
          return bp; 
      }
      /* newsize > oldsize */ 
      else { 
          size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLK(bp))); 
          size_t csize;

          /* 下一块free且合并后能用于开新空间 */  
          if(!next_alloc && ((csize = oldsize + GET_SIZE(  HDRP(NEXT_BLK(bp))  ))) >= newsize){ 
            remove_from_free_list(NEXT_BLK(bp)); 
            PUT(HDRP(bp), PACK(csize, 1)); 
            PUT(FTRP(bp), PACK(csize, 1)); 
            return bp; 
          }
          else {  
            void *new_ptr = mm_malloc(newsize);  
            place(new_ptr, newsize);
            memcpy(new_ptr, bp, newsize); 
            mm_free(bp); 
            return new_ptr; 
          } 
      }
  }else 
    return NULL;
} 


/*
 * 回收
 */
static void *coalesce(void *bp){

  size_t NEXT_ALLOC = GET_ALLOC(  HDRP(NEXT_BLK(bp))  );
  size_t PREV_ALLOC = GET_ALLOC(  FTRP(PREV_BLK(bp))  ) || PREV_BLK(bp) == bp;
  size_t size = GET_SIZE(HDRP(bp));
    
  if (PREV_ALLOC && !NEXT_ALLOC) {                  
    size += GET_SIZE( HDRP(NEXT_BLK(bp))  );
    remove_from_free_list(NEXT_BLK(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else if (!PREV_ALLOC && NEXT_ALLOC) {               
    size += GET_SIZE( HDRP(PREV_BLK(bp))  );
    bp = PREV_BLK(bp);
    remove_from_free_list(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else if (!PREV_ALLOC && !NEXT_ALLOC) {                
    size += GET_SIZE( HDRP(PREV_BLK(bp))  ) + GET_SIZE( HDRP(NEXT_BLK(bp))  );
    remove_from_free_list(PREV_BLK(bp));
    remove_from_free_list(NEXT_BLK(bp));
    bp = PREV_BLK(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  
  /* 最后要插入 */
  insert_in_free_list(bp);
  return bp;
}

/* 
 * 扩展
 */

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  // 最小块 4 word
  if (size < 4 * WSIZE){
    size = 4 * WSIZE;
  }

  if ((int)(bp = mem_sbrk(size)) == -1){ 
    return NULL;
  }

  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLK(bp)), PACK(0, 1)); /* new epilogue header */

  return coalesce(bp);
}

/*
 * 从free list中找free块
 */
static void *find_fit(size_t asize){
  void *bp;
  static int last_malloced_size = 0;
  
  for (bp = free_list_start; GET_ALLOC(HDRP(bp)) == 0; bp = GET_NEXT_PTR(bp) ){
    if (asize <= (size_t)GET_SIZE(HDRP(bp)) ) {
      last_malloced_size = asize;
      return bp;
    }
  }
  return NULL;
}

/* 
 * 分配块
 */
static void place(void *bp, size_t asize){
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= 4 * WSIZE) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    remove_from_free_list(bp);
    bp = NEXT_BLK(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    coalesce(bp);
  }
  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    remove_from_free_list(bp);
  }
}

/* 插入free_list元素 */
static void insert_in_free_list(void *bp){
  SET_NEXT_PTR(bp, free_list_start); 
  SET_PREV_PTR(free_list_start, bp); 
  SET_PREV_PTR(bp, NULL); 
  free_list_start = bp; 
}
/* 去掉free_list元素 */
static void remove_from_free_list(void *bp){
  if (GET_PREV_PTR(bp))
    SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));
  else
    free_list_start = GET_NEXT_PTR(bp);
  SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}