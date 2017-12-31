/*Aditya Bhushan andrewid :abhushan
 * I am creating a list of free blocks by placing the next and previous 
 *pointers in the payload ofthe free blocks. I am implementing a doubly 
 *linked list since dequeue is faster. In order to improve memory utilisation 
 *I have removed footers from allocated blocks and instead save that 
 *information in the lower order bit of the next block. Also to improve 
 *performance I have used Segregated list
  */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"


//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__) 
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16


/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size =2* dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;

static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
static block_t *free_list[5];//For holding the heads of all the segregated lists.
static block_t *tail[5];//For Holding the tails of all the segregated lists.
static int free_blocks=0;
static block_t *epilogue=NULL;
static block_t *prologue=NULL;

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize,int index);
static block_t *coalesce(block_t *block);
static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);
static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);
static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);
static void set_previous_allocated(block_t *block);
static void set_previous_free(block_t *block);
static bool is_previous_allocated(block_t*block_t);
static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static int get_index(size_t size);
static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static void enqueue(block_t * block,int index);
static void dequeue(block_t * block,int index);
bool mm_checkheap(int lineno);
static void print_list(void);
/*
 * mm_init: initializes the heap; it is run once when heap_start == NULL.
 *          prior to any extend_heap operation, this is the heap:
 *              start            start+8           start+16
 *          INIT: | PROLOGUE_FOOTER | EPILOGUE_HEADER |
 * heap_listp ends up pointing to the epilogue header.
 */
bool mm_init(void) 
{   

    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }
    prologue=(block_t *) start;
    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) &(start[1]);
    epilogue=heap_listp;
    set_previous_allocated(epilogue);
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    free_list[get_index(chunksize)]=heap_listp;
    tail[get_index(chunksize)]=heap_listp;
    ((word_t *)heap_listp->payload)[0]=0;
    ((word_t *)heap_listp->payload)[1]=0;
    free_blocks++;
    return true;
}

/*
 * malloc: allocates a block with size at least (size + dsize), rounded up to
 *         the nearest 16 bytes, with a minimum of 2*dsize. Seeks a
 *         sufficiently-large unallocated block on the heap to be allocated.
 *         If no such block is found, extends heap by the maximum between
 *         chunksize and (size + dsize) rounded up to the nearest 16 bytes,
 *         and then attempts to allocate all, or a part of, that memory.
 *         Returns NULL on failure, otherwise returns a pointer to such block.
 *         The allocated block will not be used for further allocations until
 *         freed.
 */
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap(__LINE__));    
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size+wsize,dsize);
    if(asize<min_block_size)
        asize=min_block_size;

    // Search the free list for a fit
    int index=get_index(asize);
    block = find_fit(asize,index);


    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {   
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
    }
    place(block, asize);
    bp = header_to_payload(block);
    dbg_printf("Malloc size %zd on address %p.\n", size, bp);
    dbg_ensures(mm_checkheap(__LINE__));
    

   return bp;
} 

/*
 * free: Frees the block such that it is no longer allocated while still
 *       maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
   if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    write_header(block, size, false);
    write_footer(block, size, false);
    coalesce(block);

}

/*
 * realloc: returns a pointer to an allocated region of at least size bytes:
 *          if ptrv is NULL, then call malloc(size);
 *          if size == 0, then call free(ptr) and returns NULL;
 *          else allocates new region of memory, copies old data to new memory,
 *          and then free old block. Returns old block if realloc fails or
 *          returns new pointer on success.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc: Allocates a block with size at least (elements * size + dsize)
 *         through malloc, then initializes all bits in allocated memory to 0.
 *         Returns NULL on failure.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;
    bool epilogue_prev=is_previous_allocated(epilogue);
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);
    if(epilogue_prev)
        {set_previous_allocated(block);   
	 }

    epilogue=block_next;
    set_previous_free(epilogue);
    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalesce: Coalesces current block with previous and next blocks if either
 *           or both are unallocated; otherwise the block is not modified.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block) 
{ 
    block_t *block_next = find_next(block);
    block_t * block_prev=NULL;
    bool prev_alloc = is_previous_allocated(block);
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);
 
    if (prev_alloc && next_alloc)              // Case 1
    {   enqueue(block,get_index(get_size(block)));
        set_previous_free(block_next);
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    { 
        dequeue(block_next,get_index(get_size(block_next)));
        size += get_size(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
        enqueue(block,get_index(size));
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {  
        block_prev=find_prev(block);
	    dequeue(block_prev,get_index(get_size(block_prev)));
        size += get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
        enqueue(block,get_index(size));
        set_previous_free(block_next);
    }

    else                                        // Case 4
    {  
        block_prev=find_prev(block);
        dequeue(block_prev,get_index(get_size(block_prev)));
        dequeue(block_next,get_index(get_size(block_next)));
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
        enqueue(block,get_index(size));
    }

   return block;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {  
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);
        block_next = find_next(block);
        dequeue(block,get_index(csize));       
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        set_previous_allocated(block_next);
        enqueue(block_next,get_index(csize-asize));
    }

    else
    {   block_t *block_next;
        block_next = find_next(block);
        write_header(block, csize, true);
        write_footer(block, csize, true);
        dequeue(block,get_index(csize));
        set_previous_allocated(block_next);       
    }
}

/*
 * find_fit: Looks for a free block with at least asize bytes with
 * first-fit policy(Traversing the list from the tail to head)
 * Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize,int index)
{
    block_t *block,*ret_block=NULL;

while(ret_block==NULL&&index<5){
    if(tail[index]!=NULL)
      { 
	for (block = tail[index];block!=NULL;block = (block_t *)(((word_t *) block->payload)[0]))
           {
              if (asize <= get_size(block))
               { 
	         return block;
               }  
        } 
   }     
     
 index++;

}

 return ret_block; // no fit found
}

/*Enqueue is used to add block to the segregated lists
 *It takes index number as an input to decide which segregated
 *list to add it to.
 */
static void enqueue(block_t * block,int index){
      
      if(block==NULL)
         return;
      
      word_t *ptr=(word_t *) block->payload;
      
      if(free_list[index]==NULL){
        free_list[index]=block;
        tail[index]=block;
        ptr[1]=0;
        ptr[0]=0;
     }

 else{
      ptr[1]=(word_t)free_list[index];
      ptr[0]=0;
      ptr=(word_t *)free_list[index]->payload;
      ptr[0]=(word_t)block;
      free_list[index]=block;
      }

    free_blocks++;
  return ;
}
/*Dequeue is used to remove block from the segregated lists
 *It takes index number as an input to decide which segregated
 *list to remove from.
 */

static void dequeue(block_t * block,int index){
 
    block_t * previous=NULL,*next=NULL;  
    if(block==NULL)
        return;   
   
    previous=(block_t *)(((word_t *)block->payload)[0]);
    next=(block_t *)(((word_t *)block->payload)[1]);

    if(previous==NULL&&next==NULL){
        ((word_t *)block->payload)[0]=0;
        ((word_t *)block->payload)[1]=0;
        free_list[index]=NULL;
        tail[index]=NULL;

    }

    if(previous==NULL&&next!=NULL){
         ((word_t *)block->payload)[0]=0;
         ((word_t *)block->payload)[1]=0;
         ((word_t *)next->payload)[0]=0;
         free_list[index]=next; 
    }

    if(previous!=NULL&&next==NULL){
         tail[index]=(block_t*)(((word_t *)block->payload)[0]);
         ((word_t *)block->payload)[0]=0;
         ((word_t *)block->payload)[1]=0;
         ((word_t *)previous->payload)[1]=0;

    }
    if(previous!=NULL&&next!=NULL){
         ((word_t *)block->payload)[0]=0;
         ((word_t *)block->payload)[1]=0;
         ((word_t *)next->payload)[0]=(word_t)previous;
         ((word_t *)previous->payload)[1]=(word_t)next;

    }
 free_blocks--;
return;

}

/*set_previous_allocated sets the previous allocated 
 * bit to one
 *
 */

static void set_previous_allocated(block_t* block){

block->header=block->header|prev_alloc_mask;

}

/*set_previous_free sets the previous allocated 
 * bit to zero
 *
 */


static void set_previous_free(block_t* block){


block->header=block->header&(~prev_alloc_mask);

}
/*is_previous_allocated return true if previous 
 * block is allocated
 *
 */
static bool is_previous_allocated(block_t* block){

bool ret=false;


if(block->header&prev_alloc_mask)
 ret=true;

return ret;
}

/* get_index: it is used to calculate
 * the list to which a block should be
 *added. I keep size<32 in index 0,
 * and flocks of size>2^8 in index 4
 * and reamining in the intermediate indexe
 * based on the log value(to the base 2).
 */

static int get_index(size_t size)
{

int count=0;
while(size>1){
size=size/2;
count++;
}

if (count<=5)
return 0;


if(count>8)
return 4;

else
return count-5;


}


/* * max: returns x if x > y, and y otherwise.
 */

static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    

    return alloc ? (size | 1) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{   
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{   bool previousAlloc=false;
    if((block->header)&2)
        previousAlloc=true;
    block->header = pack(size, alloc);
    if(previousAlloc)
        block->header=block->header|2;
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int lineno)  
{
 
  if(heap_listp==NULL)
   return true;
  block_t *block=NULL,*next=NULL,*prev=NULL;
  int index=0,blocks_in_list=0,blocks_in_heap=0;
  block=heap_listp;
  //int count_traversing_reverse=0;//blocks_in_heap;
  word_t header,footer;
  bool present_alloc,prev_alloc_bit,next_alloc;


    while(get_size(block)>0){
         next=find_next(block);
         present_alloc=extract_alloc(block->header);
         next_alloc=extract_alloc(find_next(block)->header);
         prev_alloc_bit=is_previous_allocated(find_next(block));
         if(!present_alloc)
            blocks_in_heap++;
 //Checking if size of the block is greater than the minimum size
         if(get_size(block)<min_block_size)
         {
            dbg_printf("\nThe block size is lesser than the minimum");
            return false;
         }
 

//Checking if the Header and footer have the same size field, 
//I am not updating footer's previous alloc bit I do that only 
//for the Header        
     
        if(!present_alloc)
          { header=block->header;
            footer= *((word_t *)((block->payload) + get_size(block) - dsize));
           if((header&size_mask)!=(footer&size_mask)){
              dbg_printf("\nLine Number %d : The header and footer dont match at address %p, Header is %lu, Footer is %lu, Size is %lu\n",lineno,block,header&size_mask,footer&size_mask,get_size(block));
              return false;
             }
         }

//Checking if the blocks are in the valid address range

	if(!(block>=heap_listp&&block<=epilogue)){
         dbg_printf("\nThe block lies at an invalid address: %p whereas the prologue is %p and epilogue is %p",block,prologue,epilogue);
         return false;
	 }
//Checking if the prev_alloc bit is correct in the next block
       if((present_alloc&&(!prev_alloc_bit))||((!present_alloc)&&(prev_alloc_bit)))
        {
          dbg_printf("\nThe previous allocated bit is set incorrect the present block is %p and the next block is %p",block,next);
          return false;  

        }
//Checking if no two consecutive blocks are free
        if(!present_alloc&&!next_alloc){
            dbg_printf("\nThere are two consecutive free blocks: Block 1 -> %p Block 2 -> %p",block,next);
            return false;
        }

//Checking if the alignment is correct
        if(!(block)%ALIGNMENT){
            dbg_printf("\nThere is a block which is disaligned");
            return false;
        }
//Checking the prologue and epilogue
        if(block==epilogue)
          {
            dbg_printf("\nThe size of epilogue is non Zero");
            return false;
          }     

          if(block==prologue)
          {
            dbg_printf("\nThe size of prologue is non Zero");
            return false;
          }  


    //   Checking for the free_list pointers to be lying 
    //     between mem_heap_lo() and mem_heap_high()
         for(int i=0;i<5;i++){

            if(free_list[i]!=NULL){
                if(!((void *)free_list[i]>mem_heap_lo()&&(void *)free_list[i]<mem_heap_hi()))
                    {
                        dbg_printf("The free list pointer is out of heap bounds %p",free_list[i]);
                        return false;
                    }
              }
             if(tail[i]!=NULL){    
                 if(!((void *)tail[i]>mem_heap_lo()&&(void *)tail[i]<mem_heap_hi()))
                    {
                         dbg_printf("The tail pointer is out of heap bounds %p",tail[i]);
                         return false;
                    }   
             
                }
          

        }

      
      next=find_next(block);
     block=next;
    }

//Checking if the number of free blocks in the list match 
//the number of free blocks in the Heap and if the free 
//blocks are in the correct list(Bucket). 
     index=0;
     while(index<5){
        if(tail[index]!=NULL)
            { 
            for (block = tail[index];block!=NULL;block = (block_t *)(((word_t *) block->payload)[0]))
                {
                    blocks_in_list++;
                    if(get_index(get_size(block))!=index){
                        dbg_printf("\nThe block at address %p is not in the correct list",block);
                        return false;
                    }

                } 
            }         
      index++;

    }   
        if(blocks_in_heap!=blocks_in_list)
            {dbg_printf("\nThe value of list count is %d and value of blocks in heap is %d",
                blocks_in_list,blocks_in_heap);
              return false;
            }

//Checking for pointers consistency in the heap checker  
index=0;
while(index<5){
        if(tail[index]!=NULL)
            { prev=NULL;
            for (block = tail[index];block!=NULL;block = (block_t *)(((word_t *) block->payload)[0]))
                {
                   prev=block; 
                    
                }
                if(prev!=free_list[index])
                {
                    dbg_printf("\nHeader not reachable from tail in the the list at index %d",index);
                    return false;
                }

            } 
        if(free_list[index]!=NULL)
            { next=NULL;
            for (block = tail[index];block!=NULL;block = (block_t *)(((word_t *) block->payload)[1]))
                {
                   next=block; 
                    
                }
                if(next!=tail[index])
                {
                    dbg_printf("\nTail not reachable from head in the the list at index %d",index);
                    return false;
                }

            } 


                     
      index++;

    }   
return true;
}





