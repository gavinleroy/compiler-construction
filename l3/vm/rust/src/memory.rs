/**
 * Garbage Collector and Memory Manager for the L3 language.
 *
 * Gavin Gray, 05.2022
 * ETH Zuerich
 * */
use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES};
use either::{Either, Left, Right};
use std::cmp;
use std::collections::HashSet;
use unfold::Unfold;

const HEADER_SIZE: usize = 1;
const TAG_NONE: L3Value = 0xFF;
const LIST_END: L3Value = -1;
const MIN_BLOCK_SIZE: L3Value = 1;

/* NOTE by default std::dbg is not removed when
 * compiling in release mode. Annoying, but I get it.
 * This is a HACK which will turn dbg into the "identity macro"
 * in release mode but otherwise output to stderr.
 * */
// #[cfg(not(debug_assertions))]
macro_rules! dbg {
    ($val:expr) => {
        $val
    };
}

fn ix_to_addr(index: usize) -> L3Value {
    (index << LOG2_VALUE_BYTES) as L3Value
}

fn addr_to_ix(addr: L3Value) -> usize {
    debug_assert!(
        addr & ((1 << LOG2_VALUE_BYTES) - 1) == 0,
        "invalid address: {} (16#{:x})",
        addr,
        addr
    );
    (addr >> LOG2_VALUE_BYTES) as usize
}

fn valid_address(addr: L3Value) -> bool {
    (addr & ((1 << LOG2_VALUE_BYTES) - 1)) == 0
}

/* @item: `content`: The entire memory space for the program
 * @item: `list_starts`: The ith index represents the start to the free
 *               list of nodes of size i.
 * @item: `free_ix`: TODO XXX REMOVE
 * */
pub struct Memory {
    content: Vec<L3Value>,
    // list_starts: Vec<usize>, // NOTE initialize with vec![0; 32]
    list_addr: L3Value,
    // The start of the bitmap region.
    bitmap_ix: usize,
    // The start of the heap, this will point to the first
    // free list sentinel.
    heap_ix: usize,
    // The start of actual free memory. This points to the first
    // block after the free list sentinel heads.
    free_ix: usize,
}

/* -- FREE MEMORY BLOCK
 * +-----------------------------------+----
 * | HEADER [1] | BLOCK START [size]   |...
 * | <size>     | <next free index>    |..
 * |            | NOTE index points    |.
 * |            | to the block start   |
 * +-----------------------------------+-
 *
 * NOTE the <size> stored in the header is the number
 * of indices to jump forward to get to the next contiguous
 * memory block (at the header). Similarly, the <next free index>
 * is the index of the block start.
 *
 * -- ALLOCATED MEMORY BLOCK
 * +----------------------------------------
 * | HEADER [1]      | USER DATA [size] ...
 * | <size> [24 MSB] |                  ..
 * | <tag>  [8 LSB]  |                  .
 * +-------------------------------------
 *
 *
 * */

fn div_up(a: usize, b: usize) -> usize {
    // We *know* that the hint is exact,
    // this is thus precisely the amount of
    // chunks of length `b` each
    (0..a).step_by(b).size_hint().0
}

/* Partition a size into two sizes, the `bigger` and the `smaller`,
 * where `smaller = ceil((1 / ratio) * bigger)`.
 * @param: `total`: the total size to split.
 * @param: `ratio`: fraction of size dedicated to `smaller`.
 * @returns: `(smaller, bigger)`
 * @ensures: `smaller + bigger = total`.
 * */
fn partition_by_ratio(total: usize, ratio: usize) -> (usize, usize) {
    let mut smaller = div_up(total, ratio);
    let mut bigger = total - smaller;
    let mut old_s;

    // FIXME this fixpoint method is a hack.
    loop {
        old_s = smaller;
        smaller = div_up(bigger, ratio);
        bigger = total - smaller;
        if smaller >= old_s {
            break;
        }
    }

    (smaller, bigger)
}

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            list_addr: LIST_END,
            bitmap_ix: 0,
            heap_ix: 0,
            free_ix: 0,
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());

        let remaining_size = self.content.len() - heap_start_index;
        let (bitmap_size, heap_size) = partition_by_ratio(remaining_size, 32);

        debug_assert_eq!(bitmap_size + heap_size, remaining_size);
        debug_assert!(bitmap_size >= heap_size / 32);

        self.heap_ix = heap_start_index + bitmap_size;
        self.bitmap_ix = heap_start_index;

        // FIXME HACK!
        // self.mem_clear(heap_start_index, bitmap_size);
        for i in &mut self.content[heap_start_index..(heap_start_index + bitmap_size)] {
            *i = 0;
        }

        // The free list will have a sentinal that starts at the beginning
        // of the heap. It will be unallocated memory, but not part of the
        // heap.

        let list_start_ix = self.heap_ix + HEADER_SIZE;
        // set the start of the list

        self.consq(list_start_ix);

        // set the size of the sentinel list head
        self.set_block_header(list_start_ix, TAG_NONE, HEADER_SIZE);

        // Set up the first unallocated block of memory

        /* | - heap start
         * v
         * +-----------------+-------------------------
         * | list   | list   | block   | LIST      ...
         * | start  | start o------------>      o  ..
         * | header | body   | header  | END PTR   .
         * +-----------------+----------------------
         * */

        let unallocated_block_ix = list_start_ix + 2 * HEADER_SIZE;
        let unallocated_block_size = heap_size - 3 * HEADER_SIZE;

        self.free_ix = unallocated_block_ix;
        self[list_start_ix] = ix_to_addr(unallocated_block_ix);
        self.set_block_header(unallocated_block_ix, TAG_NONE, unallocated_block_size);
        self[unallocated_block_ix] = LIST_END;

        log::info!("Bitmap memory IX {}", self.bitmap_ix);
        log::info!("Heap memory IX {}", self.heap_ix);
        log::info!("Free List IX {}", self.list_addr);
        log::info!("First Heap IX {}", self.free_ix);

        debug_assert!(self.validate_memory());
    }

    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize) -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);
        debug_assert!(self.validate_memory());

        // NOTE we cannot allocote a block of size 0,
        // when it gets freed, it would not have enough
        // space to put a free list node.
        let size = cmp::max(size, MIN_BLOCK_SIZE);

        // FIXME create a free list iterator and use a find for the iterator.
        let mut found_memory = todo!(); // self.find_memory(self.list_ix, size as usize);

        if found_memory.is_none() {
            log::info!("GC! couldn't find block size {}", size);
            self.gc(root); // FIXME a smarter way to call this

            // FIXME create a free list iterator and use a find for the iterator.
            found_memory = todo!(); // self.find_memory(self.list_ix, size as usize);
        }

        match found_memory {
            None => panic!("out of memory"),
            Some(block) => {
                self.mem_clear(block);
                self.mark_bitmap_at(block);
                self.set_block_header_tag(block, tag);

                log::info!("Allocating {} bytes at {}", size, block);
                debug_assert!(self.valid_index(block));
                debug_assert!(block + (size as usize) <= self.content.len());
                debug_assert!(self.validate_memory());

                block
            }
        }
    }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) {
            self[copy + i] = self[block + i]
        }
        copy
    }

    // `free` is called with a parent block frame.
    // Meaning you could call gc on it as the root XXX.
    pub fn free(&mut self, block: usize) {
        debug_assert!(self.validate_memory());

        // TODO FIXME
        // let was_marked = self.unmark_bitmap_at(block);
        // debug_assert!(was_marked);
        // self.set_block_header_tag(block, TAG_NONE);
        // self.add_to_free_list(self.list_ix, block);

        debug_assert!(self.validate_memory());
    }

    pub fn block_tag(&self, block: usize) -> L3Value {
        self[block - HEADER_SIZE] & 0xFF
    }

    pub fn block_size(&self, block: usize) -> L3Value {
        self[block - HEADER_SIZE] >> 8
    }

    pub fn set_block_header(&mut self, block: usize, tag: L3Value, size: usize) {
        self[block - HEADER_SIZE] = ((size as L3Value) << 8) | tag
    }

    // ---------------------------------------------------------------

    fn gc(&mut self, root: usize) {
        debug_assert!(self.validate_memory());

        // TODO mark all the objects that are reachable from `root`
        self.mark(root);
        // TODO sweep the heap and reclaim blocks
        self.sweep();

        debug_assert!(self.validate_memory());
    }

    fn mark(&mut self, root: usize) {
        let block_size = self.block_size(root) as usize;
        // Collect the indices that went from marked -> unmarked
        // NOTE there's no need to keep tracked of "who's been visited"
        // because when a block gets unmarked, it won't ever be added again.
        let marked_ixs: Vec<usize> = (root..(root + block_size))
            .filter(|&ix| {
                valid_address(self[ix]) && {
                    let ix = addr_to_ix(self[ix]);
                    self.valid_index(ix) && self.unmark_bitmap_at(ix)
                }
            })
            .collect();
        marked_ixs.iter().for_each(|&ix| self.mark(ix))
    }

    fn sweep(&mut self) {
        // debug_assert!(self.list_ix < self.free_ix);

        // The start of available memory to allocate.
        let mut block = self.free_ix;
        let end_ix = self.content.len();

        // Left(usize) : the free memory beforehand with potential space in-between.
        // Right(usize) : the free memory beforehand was in the previous block.
        let list_ix = self.list_ix;
        self[list_ix] = LIST_END; // Reset the free list first
        let mut previous_free: Either<usize, usize> = Left(self.list_ix);

        while block < end_ix {
            let block_tag = self.block_tag(block);
            let block_size = self.block_size(block) as usize;

            debug_assert!(0 < block_size);

            // FIXME some of the things in the inner matches are
            // redundent or unnecessary.
            match (block_tag, previous_free) {
                (TAG_NONE, Right(last_free_ix)) => {
                    // coalesce the blocks
                    self.mem_clear(block);
                    self.coalesce_blocks(last_free_ix, block);
                }

                // Add the block to the list
                (TAG_NONE, Left(last_free_ix)) => {
                    self.mem_clear(block);
                    self.add_to_free_list(last_free_ix, block);
                    previous_free = Right(block);
                }

                (tag, Left(last_free_ix)) if self.bitmap_at(block) => {
                    self.unmark_bitmap_at(block);
                    self.set_block_header_tag(block, TAG_NONE);
                    self.mem_clear(block);

                    self.add_to_free_list(last_free_ix, block);
                    previous_free = Right(block);
                }

                (tag, Right(last_free_ix)) if self.bitmap_at(block) => {
                    self.unmark_bitmap_at(block);
                    self.set_block_header_tag(block, TAG_NONE);
                    self.mem_clear(block);

                    // coalesce the blocks
                    self.coalesce_blocks(last_free_ix, block);
                }

                // Block is not getting freed, Mark the bitmap to set it as alive.
                (tag, Right(last_free_ix)) => {
                    self.mark_bitmap_at(block);
                    previous_free = Left(last_free_ix);
                }

                (_, _) => self.mark_bitmap_at(block),
            };

            // Move forward to the next block
            block += (block_size as usize) + HEADER_SIZE;
        }

        // TODO blocks not tagged TAG_NONE are "live" and should have the bit in the
        // bitmap set back to 1.
        // NOTE you can reconstruct the list from scratch which allows for
        // coallescing.
        //
        // steps
        // 1. start at the beginning of the heap
        // list_ix ->
        // IFF bitmap is high, free the block
        // IFF (this block is now free or was already free)
        //     && the previous block is free, coalesce.
        // OTH set bitmap idx and continue (this case disallows
        //     the next block from being coalesced with prev).
    }

    fn coalesce_blocks(&mut self, block: usize, next: usize) {
        debug_assert!(block < next);

        let block_size = self.block_size(block) as usize;
        let next_size = self.block_size(next) as usize;

        let block_tag = self.block_tag(block);
        let next_tag = self.block_tag(next);

        debug_assert_eq!(block_tag, TAG_NONE);
        debug_assert_eq!(next_tag, TAG_NONE);
        debug_assert_eq!(block + block_size + HEADER_SIZE, next);

        self.set_block_header_size(block, block_size + next_size + HEADER_SIZE);
    }

    /* Find Possible Memory
     *
     * Returns the block index to the allocated memory. NOTE this
     * memory is already removed from the free list and marked.
     * */
    fn find_memory(&mut self, curr_ix: usize, min_size: usize) -> Option<usize> {
        let next_ix = self.get_list_next(curr_ix)?;
        let next_size = self.block_size(next_ix) as usize;

        debug_assert_eq!(self.block_tag(curr_ix), TAG_NONE);
        debug_assert_eq!(self.block_tag(next_ix), TAG_NONE);

        // FIXME this is a HACK!
        if next_size == min_size || next_size > min_size + 2 * HEADER_SIZE {
            self.split_block(next_ix, min_size); // FIXME automatically could be bad.
            self.remove_from_free_list(curr_ix, next_ix);

            Some(next_ix)
        } else {
            self.find_memory(next_ix, min_size)
        }
    }

    fn get_list_next(&self, ix: usize) -> Option<usize> {
        if self[ix] == LIST_END {
            None
        } else {
            log::debug!("list next {} -> {}", ix, addr_to_ix(self[ix]));
            Some(dbg!(addr_to_ix(self[ix])))
        }
    }

    fn remove_from_free_list(&mut self, prev: usize, rem: usize) {
        let next = self.get_list_next(rem).map_or(LIST_END, ix_to_addr);
        self[prev] = next;
    }

    fn add_to_free_list(&mut self, prev: usize, next: usize) {
        debug_assert_eq!(self.block_tag(prev), TAG_NONE);
        debug_assert_eq!(self.block_tag(next), TAG_NONE);
        let prev_next = self[prev];
        self[next] = prev_next;
        self[prev] = ix_to_addr(next);
    }

    fn mem_clear(&mut self, block_start: usize) {
        debug_assert!(!self.bitmap_at(block_start));
        debug_assert_eq!(self.block_tag(block_start), TAG_NONE);

        let size = self.block_size(block_start) as usize;
        (0..size).for_each(|off| {
            self[block_start + off] = 0; // FIXME
        });
    }

    /** Split BLock
     *
     * Try to split a block into two smaller blocks, the first of which
     * cannot be any smaller than `min_size`.
     * The block pointer to by `block_ix` needs to be a free block.
     * */
    fn split_block(&mut self, block_ix: usize, min_size: usize) {
        let block_size = self.block_size(block_ix) as usize;

        debug_assert!(0 < min_size);
        debug_assert_eq!(self.block_tag(block_ix), TAG_NONE);

        debug_assert!(min_size <= block_size);

        if min_size == block_size {
            return;
        }

        let rem_size = block_size - min_size - HEADER_SIZE;

        // If the remaining memory is large enough to be useful
        // then we should split it and then set memory accordingly.
        //
        // FIXME pick a better heuristic for choosing to split or not.
        if rem_size >= 2 * HEADER_SIZE {
            let next_block_ix = block_ix + min_size + HEADER_SIZE;
            // setup the header for the next block
            self.set_block_header_size(block_ix, min_size);
            self.set_block_header(next_block_ix, TAG_NONE, rem_size);

            // FIXME REMOVE
            self.mem_clear(next_block_ix);

            self.add_to_free_list(block_ix, next_block_ix);
        }
    }

    fn ix_to_bitmap_addr(&self, block: usize) -> (usize, usize) {
        debug_assert!(self.heap_ix <= block);

        let addr = block - self.heap_ix;
        // compute offset into the bitmap
        let bitmap_off = addr >> LOG2_VALUE_BITS;
        // compute offset into the bitmap block
        let block_off = addr & 0x1F;

        debug_assert!(self.heap_ix <= block && block < self.content.len());
        debug_assert!(block_off < 32);
        debug_assert!(self.bitmap_ix + bitmap_off < self.heap_ix);

        let ix = self.bitmap_ix + bitmap_off;

        (ix, block_off)
    }

    fn set_block_header_tag(&mut self, block: usize, tag: L3Value) {
        let size = self.block_size(block) as usize;
        self.set_block_header(block, tag, size);
    }

    fn set_block_header_size(&mut self, block: usize, size: usize) {
        let tag = self.block_tag(block);
        self.set_block_header(block, tag, size);
    }

    fn bitmap_at(&self, block: usize) -> bool {
        let (ix, block_off) = self.ix_to_bitmap_addr(block);
        ((self[ix] >> block_off) & 0x1) == 0x1
    }

    fn mark_bitmap_at(&mut self, block: usize) {
        let (ix, block_off) = self.ix_to_bitmap_addr(block);
        // Set bit to be high
        let unmarked = self[ix];
        self[ix] = unmarked | (1 << block_off);
    }

    fn unmark_bitmap_at(&mut self, block: usize) -> bool {
        let (ix, block_off) = self.ix_to_bitmap_addr(block);
        let marked = self[ix];
        let mask = usize::MAX ^ (1 << block_off);
        // Set bit to be low
        self[ix] = ((marked as usize) & mask) as L3Value;
        marked != self[ix]
    }

    fn valid_index(&self, ix: usize) -> bool {
        self.heap_ix <= ix && ix <= self.content.len()
    }

    /* WARNING only call this function from within a debug_assert!
     *
     * Traverse the free list, and entirety of the heap, checking
     * invariants for both.
     *
     * - free list is non-recursive
     * - free list blocks are tagged TAG_NONE
     * - last free list node points to LIST_END
     * - allocated blocks are marked in bitmap
     * */
    fn validate_memory(&self) -> bool {
        // Validate that the free list is not recursive,
        // all blocks are marked with TAG_NONE,

        #[cfg(not(debug_assertions))]
        panic!("validate_memory invoked");

        debug_assert_eq!(self.block_size(self.list_ix), 1);

        // self.heap_ix points to the heap boundary,
        // going one header past should start a block.
        let mut ix = self.heap_ix + HEADER_SIZE;
        let mut free_blocks = 0;
        let mut block_num = 0;
        let content_len = self.content.len();

        while ix < content_len {
            block_num += 1;

            let block_tag = self.block_tag(ix);
            let block_size = self.block_size(ix) as usize;

            if block_tag == TAG_NONE {
                free_blocks += 1;
                debug_assert!(!self.bitmap_at(ix));
                debug_assert!(self[ix] == LIST_END || valid_address(self[ix]));
            } else {
                debug_assert!(self.bitmap_at(ix));
            }
            ix += block_size + HEADER_SIZE;
        }

        log::debug!("Block Count {} Free Count {}\n", block_num, free_blocks);

        debug_assert_eq!(ix - HEADER_SIZE, content_len);

        let mut free_list_ixs: Vec<usize> = Unfold::new(
            |ix| ix.and_then(|ixo| self.get_list_next(ixo)),
            Some(self.list_ix),
        )
        .take_while(Option::is_some)
        .take(free_blocks + 1) // Limit space to the entire memory if list is recurisve
        .map(Option::unwrap)
        .collect();

        debug_assert_eq!(free_list_ixs.len(), free_blocks);

        free_list_ixs.last().into_iter().for_each(|&last_ix| {
            debug_assert_eq!(self[last_ix], LIST_END);
        });

        free_list_ixs.pop(); // Remove last element

        free_list_ixs.iter().for_each(|&ix| {
            debug_assert_eq!(self.block_tag(ix), TAG_NONE);
            debug_assert!(valid_address(self[ix]));
        });

        true
    }

    /** GC Lists
     *
     * A GC List is represented by an L3Value that is either
     * LIST_END: (nil)
     * Or a non-nil value representing an address that points to
     * an index of a block.
     * */

    /** Cons
     *
     * Semantically similar to (cons! <elem> <list>) in Scheme
     * */
    fn consq(&mut self, elem_ix: usize) {
        let list_addr = self.list_addr;
        let new_list_addr = ix_to_addr(elem_ix);
        self[elem_ix] = list_addr;
        self.list_addr = new_list_addr;
    }

    fn car(list: L3Value) -> Option<usize> {
        todo!();
    }

    fn cdrq(list: &mut L3Value) {
        todo!();
    }

    fn havocq(&mut self) {
        self.list_addr = LIST_END;
    }
}

use std::ops::{Index, IndexMut};

impl Index<usize> for Memory {
    type Output = L3Value;
    fn index(&self, i: usize) -> &Self::Output {
        &self.content[i]
    }
}

impl IndexMut<usize> for Memory {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.content[i]
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn create_heap(size: usize) -> Memory {
        let mut mem = Memory {
            content: vec![0; size],
            list_ix: 0,
            bitmap_ix: 0,
            heap_ix: 0,
            free_ix: 0,
        };
        mem.set_heap_start(0);
        mem
    }

    #[test]
    fn partition_heap_00() {
        let mem = create_heap(100);
        assert_eq!(mem.bitmap_ix, 0);
        assert_eq!(mem.heap_ix, 4);
    }

    #[test]
    fn partition_heap_01() {
        let mem = create_heap(327);
        assert_eq!(mem.bitmap_ix, 0);
        assert_eq!(mem.heap_ix, 10);
    }

    #[test]
    fn partition_heap_02() {
        let mem = create_heap(100);
        assert_eq!(mem.bitmap_ix, 0);
        assert_eq!(mem.heap_ix, 4);

        let (ix, bitoff) = mem.ix_to_bitmap_addr(14);
        assert_eq!(ix, 0);
        assert_eq!(bitoff, 10);

        let (ix, bitoff) = mem.ix_to_bitmap_addr(36);
        assert_eq!(ix, 1);
        assert_eq!(bitoff, 0);

        let (ix, bitoff) = mem.ix_to_bitmap_addr(37);
        assert_eq!(ix, 1);
        assert_eq!(bitoff, 1);

        let (ix, bitoff) = mem.ix_to_bitmap_addr(99);
        assert_eq!(ix, 3);
        assert_eq!(bitoff, 0);
    }

    #[test]
    fn mark_addr() {
        let mut mem = create_heap(100);
        mem.mark_bitmap_at(5);
        assert_eq!(mem[0], 0x2);
        for &loc in mem.content[1..4].iter() {
            assert_eq!(dbg!(loc), 0);
        }
    }

    #[test]
    fn mark_unmark_addr() {
        let mut mem = create_heap(100);
        let ixs: Vec<usize> = vec![18, 31, 32, 33, 76, 99];

        for &ix in ixs.iter() {
            mem.mark_bitmap_at(ix);
        }

        for &ix in ixs.iter() {
            assert!(mem.unmark_bitmap_at(ix));
        }

        for &loc in mem.content[1..4].iter() {
            assert_eq!(dbg!(loc), 0);
        }
    }
}
