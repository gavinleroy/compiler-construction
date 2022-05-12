/**
 * Garbage Collector and Memory Manager for the L3 language.
 *
 * Gavin Gray, 05.2022
 * ETH Zuerich
 * */
use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};
use std::cmp;
use std::collections::HashSet;
use unfold::unfold;

const HEADER_SIZE: usize = 1;
const TAG_NONE: L3Value = 0xFF;
const LIST_END: L3Value = -1;
const MIN_BLOCK_SIZE: usize = 1;

/* NOTE by default std::dbg is not removed when
 * compiling in release mode. Annoying, but I get it.
 * This is a HACK which will turn dbg into the "identity macro"
 * in release mode but otherwise output to stderr.
 * */
#[cfg(not(debug_assertions))]
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

fn big_enough(size: usize, min_size: usize) -> bool {
    size == min_size || size > 2 * HEADER_SIZE + min_size
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
    free_list: L3Value,
    // The start of the bitmap region.
    bitmap_ix: usize,
    // The start of the heap, free memory.
    heap_ix: usize,
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
            free_list: LIST_END,
            bitmap_ix: 0,
            heap_ix: 0,
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

        #[cfg(debug_assertions)] // FIXME clear all the heap memory [unnecessary]
        self.zero_memory(heap_start_index, self.content.len());

        // Set up the first unallocated block of memory
        let unallocated_block_ix = self.heap_ix + HEADER_SIZE;
        let unallocated_block_size = (self.content.len() - self.heap_ix) - HEADER_SIZE;

        self.set_block_header(unallocated_block_ix, TAG_NONE, unallocated_block_size);

        // set the start of the list
        self.consq(unallocated_block_ix);

        log::info!("Bitmap memory IX {}", self.bitmap_ix);
        log::info!("Heap memory IX {}", self.heap_ix);
        log::info!("Free List IX {}", addr_to_ix(self.free_list));

        debug_assert!(self.validate_memory());
    }

    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize) -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);
        debug_assert!(size < 32); // XXX Should this be true?
        debug_assert!(self.validate_memory());

        // NOTE we cannot allocote a block of size 0,
        // when it gets freed, it would not have enough
        // space to put a free list node.
        let min_size = cmp::max(size as usize, MIN_BLOCK_SIZE);

        // FIXME create a free list iterator and use a find for the iterator.
        let mut found_memory = self.find_memory(min_size);

        if found_memory.is_none() {
            log::info!("GC with root {} min_size {}", root, min_size);

            self.gc(root); // FIXME a smarter way to call this

            // FIXME create a free list iterator and use a find for the iterator.
            found_memory = self.find_memory(min_size);
        }

        match found_memory {
            None => panic!("out of memory"),
            Some(block) => {
                let size = self.block_size(block) as usize;

                debug_assert!(min_size == size);

                self.block_clear(block);
                self.mark_bitmap_at(block);
                self.set_block_header_tag(block, tag);

                log::info!("Allocating {} bytes at {}", size, block);

                // Valid index is returned
                debug_assert!(self.valid_index(block));
                // Block returned was removed from free list
                debug_assert!(!(self.free_list_iter().iter().any(|&ix| ix == block)));
                // Entire block is in memory
                debug_assert!(block + (size as usize) <= self.content.len());
                // Memory state afterwards is valid [approximate]
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
        log::debug!("Copying {} to {}", block, copy);
        copy
    }

    // `free` is called with a parent block frame.
    // Meaning you could call gc on it as the root ??? XXX.
    pub fn free(&mut self, block: usize) {
        debug_assert!(self.validate_memory());
        debug_assert!(self.valid_index(block));

        log::debug!("FREE {}", block);

        // TODO FIXME when and why is free called ??? NOTE XXX
        let was_marked = self.unmark_bitmap_at(block);
        self.set_block_header_tag(block, TAG_NONE);

        debug_assert!(was_marked);

        self.consq(block);

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
        // let free_bytes_before = self.free_ix_count();

        // HACK simulate marking by zeroing the bitmap.
        // This means not objects will be reclaimed, but blocks
        // could be coalesced.
        // self.zero_memory(self.bitmap_ix, self.heap_ix);

        // TODO sweep the heap and reclaim blocks
        self.sweep();

        // let free_bytes_after = self.free_ix_count();
        // debug_assert_eq!(free_bytes_before, free_bytes_after);

        debug_assert!(self.validate_memory());
    }

    fn mark(&mut self, root: usize) {
        debug_assert_eq!(self.block_tag(root), TAG_REGISTER_FRAME);

        let mut seen: HashSet<usize> = HashSet::default();
        let mut work = vec![];

        seen.insert(root);
        work.push(root);

        while 0 < work.len() {
            let block = work.pop().unwrap();

            log::debug!("GC Mark at {}", block);

            let block_size = self.block_size(block) as usize;
            let marked_ixs: Vec<usize> = (block..(block + block_size))
                .filter_map(|ix| {
                    if valid_address(self[ix]) && {
                        let ix = addr_to_ix(self[ix]);
                        (0 < ix
                            && ix < self.content.len()
                            && (!self.valid_index(ix) && self.block_tag(ix) == TAG_REGISTER_FRAME))
                            || (self.valid_index(ix) && self.unmark_bitmap_at(ix))
                    } {
                        Some(addr_to_ix(self[ix]))
                    } else {
                        None
                    }
                })
                .collect();

            marked_ixs.iter().for_each(|&ix| {
                if !seen.contains(&ix) {
                    seen.insert(ix);
                    work.push(ix);
                }
            });
        }
    }

    fn sweep(&mut self) {
        // The start of available memory to allocate.
        let mut block = self.heap_ix + HEADER_SIZE;
        let end_ix = self.content.len();

        self.clearq(); // destroy the free list

        debug_assert_eq!(self.free_list, LIST_END);

        let mut previous_free: Option<usize> = None;

        let mut kept_count = 0;
        let mut free_count = 0;

        while block < end_ix {
            let block_tag = self.block_tag(block);
            let block_size = self.block_size(block) as usize;

            let marked_before = self.bitmap_at(block);

            debug_assert!(self.valid_index(block));

            match (block_tag, previous_free) {
                (tag, Some(last_free_ix)) if tag == TAG_NONE || self.bitmap_at(block) => {
                    free_count += 1; // FIXME

                    self.unmark_bitmap_at(block);
                    self.set_block_header_tag(block, TAG_NONE);
                    self.block_clear(block);

                    // coalesce the blocks
                    self.coalesce_blocks(last_free_ix, block);
                }

                // NOTE blocks still tagged in the bitmap are *unreachable*
                (tag, None) if tag == TAG_NONE || self.bitmap_at(block) => {
                    free_count += 1; // FIXME

                    self.unmark_bitmap_at(block);
                    self.set_block_header_tag(block, TAG_NONE);
                    self.block_clear(block);

                    self.consq(block);
                    previous_free = Some(block);
                }

                // -- remaining blocks are reachable.
                //
                // Block is not getting freed.
                // Mark the bitmap to set it as alive.
                (_, _) => {
                    kept_count += 1; // FIXME
                    self.mark_bitmap_at(block);
                    previous_free = None;
                }
            };

            if marked_before && !self.bitmap_at(block) {
                log::debug!("collected {}", block);
            }

            // Move forward to the next block
            block += (block_size as usize) + HEADER_SIZE;
        }

        log::info!(
            "[sweep] blocks: {} live {} free {}",
            kept_count + free_count,
            kept_count,
            free_count
        );
    }

    /** Find Possible Memory
     *
     * XXX FIXME TODO HACK
     *
     * Returns the block index to the allocated memory. NOTE this
     * memory is already removed from the free list and marked.
     * */
    fn find_memory(&mut self, min_size: usize) -> Option<usize> {
        if self.free_list == LIST_END {
            return None;
        }

        /* free list
         * o
         * |
         * |
         * |
         * v
         *
         * +---------+---------+---------+---------+
         * |         |         |         |         |
         * | o-------------------->  o----------------------------
         * |         |         |         |         |
         * +---------+---------+---------+---------+
         *
         * */

        unsafe {
            let mut prev: *mut L3Value = &mut self.free_list;
            let mut addr = self.free_list;

            while addr != LIST_END {
                let ix = addr_to_ix(addr);
                let ix_size = self.block_size(ix) as usize;

                // FIXME
                if big_enough(ix_size, min_size) {
                    self.split_block(ix, min_size);

                    *prev = self[ix];
                    return Some(ix);
                }

                prev = &mut self[ix];
                addr = self[ix];
            }
        }

        None
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

            log::debug!("split block {} {}", block_ix, next_block_ix);

            // FIXME REMOVE
            self.block_clear(next_block_ix);

            self.insert_after(block_ix, next_block_ix);
        }
    }

    /** Coalesce Blocks
     *
     * Given two consecutive blocks in memory
     * +------+------+------+------+
     * |prev  |free  |next  |rnd   |
     * |header|list  |header| mem  |
     * |<tag> |ptr   |<tag> | . .  |
     * |<size>|o     |<size>| ..  .|
     * +------+|-----+------+------+
     *         |->
     * Increase the size of the previous to gobble the
     * memory coming afterward.
     *
     * +------+------+------+------+
     * |prev  |free     rnd        |
     * |header|list      .  mem    |
     * |<tag> |ptr     .   . .     |
     * |<size>|o       .   ..  .   |
     * +------+|-----+------+------+
     *         |-->
     * */
    fn coalesce_blocks(&mut self, prev: usize, next: usize) {
        debug_assert!(prev < next);

        let prev_size = self.block_size(prev) as usize;
        let next_size = self.block_size(next) as usize;

        let prev_tag = self.block_tag(prev);
        let next_tag = self.block_tag(next);

        debug_assert_eq!(prev_tag, TAG_NONE);
        debug_assert_eq!(next_tag, TAG_NONE);
        debug_assert_eq!(prev + prev_size + HEADER_SIZE, next);

        let coalesced_size = prev_size + next_size + HEADER_SIZE;

        self.set_block_header_size(prev, coalesced_size);
    }

    fn block_clear(&mut self, block_start: usize) {
        debug_assert!(!self.bitmap_at(block_start));
        debug_assert_eq!(self.block_tag(block_start), TAG_NONE);

        let size = self.block_size(block_start) as usize;
        self.zero_memory(block_start, block_start + size);

        debug_assert_eq!(self.block_size(block_start) as usize, size);
        debug_assert_eq!(self.block_tag(block_start), TAG_NONE);
    }

    /** Memory Clear
     *
     * Zero memory in the range [start, end)
     * */
    fn zero_memory(&mut self, start: usize, end: usize) {
        log::debug!("Zero memory [{}, {})", start, end);
        for i in &mut self.content[start..end] {
            *i = 0;
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

    fn next_block_ix(&self, ix: usize) -> usize {
        let block_size = self.block_size(ix) as usize;
        ix + block_size + HEADER_SIZE
    }

    fn valid_index(&self, ix: usize) -> bool {
        self.heap_ix < ix && ix < self.content.len()
    }

    /** GC Lists
     *
     * A GC List is represented by an L3Value that is either
     * LIST_END: (nil)
     * Or a non-nil value representing an address that points to
     * an index of a block.
     *
     * TODO expand the functions to work on an arbitrary list
     * (this will help when there are 32 free lists).
     * */

    /** Cons
     *
     * Semantically similar to (cons! <elem> <list>) in Scheme
     * */
    fn consq(&mut self, elem_ix: usize) {
        let list_addr = self.free_list;
        let new_list_addr = ix_to_addr(elem_ix);
        self[elem_ix] = list_addr;
        self.free_list = new_list_addr;
    }

    /** Get the first element of the free list.
     * */
    fn car(&self) -> Option<usize> {
        if self.free_list == LIST_END {
            None
        } else {
            Some(addr_to_ix(self.free_list))
        }
    }

    /** Mutably remove the first element of the list.
     * */
    fn cdrq(&mut self) {
        debug_assert_ne!(self.free_list, LIST_END);
        let ix = addr_to_ix(self.free_list);
        self.free_list = self[ix];
    }

    /** Clear the Free List
     * */
    fn clearq(&mut self) {
        self.free_list = LIST_END;
    }

    fn insert_after(&mut self, prev: usize, next: usize) {
        debug_assert_eq!(self.block_tag(prev), TAG_NONE);
        debug_assert_eq!(self.block_tag(next), TAG_NONE);
        debug_assert!(!self.bitmap_at(prev));
        debug_assert!(!self.bitmap_at(next));

        let before = self.free_list_iter();

        self[next] = self[prev];
        self[prev] = ix_to_addr(next);

        let after = self.free_list_iter();

        debug_assert_eq!(before.len() + 1, after.len());
        debug_assert_eq!(self.block_tag(prev), TAG_NONE);
        debug_assert_eq!(self.block_tag(next), TAG_NONE);
        debug_assert!(!self.bitmap_at(prev));
        debug_assert!(!self.bitmap_at(next));
    }

    fn remove_from_free_list(&mut self, prev: usize, to_remove: usize) {
        debug_assert_eq!(self.block_tag(prev), TAG_NONE);
        debug_assert_eq!(self.block_tag(to_remove), TAG_NONE);
        debug_assert!(!self.bitmap_at(prev));
        debug_assert!(!self.bitmap_at(to_remove));
        debug_assert_eq!(addr_to_ix(self[prev]), to_remove);

        self[prev] = self[to_remove];

        debug_assert_ne!(addr_to_ix(self[prev]), to_remove);
        debug_assert_eq!(self.block_tag(prev), TAG_NONE);
        debug_assert_eq!(self.block_tag(to_remove), TAG_NONE);
        debug_assert!(!self.bitmap_at(prev));
        debug_assert!(!self.bitmap_at(to_remove));
    }

    fn free_list_iter(&self) -> Vec<usize> {
        unfold(
            |maddr| match maddr {
                None => None,
                Some(LIST_END) => None,
                Some(addr) => {
                    debug_assert_ne!(addr, LIST_END);
                    Some(self[addr_to_ix(addr)])
                }
            },
            Some(self.free_list),
        )
        .take_while(|o| o.map_or(false, |v| v != LIST_END))
        .map(Option::unwrap)
        .map(addr_to_ix)
        .collect()
    }

    fn free_ix_count(&self) -> usize {
        self.free_list_iter().iter().fold(0usize, |sum, &ix| {
            sum + (self.block_size(ix) as usize) + HEADER_SIZE
        })
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

        // self.heap_ix points to the heap boundary,
        // going one header past should start a block.
        let mut ix = self.heap_ix + HEADER_SIZE;
        let mut block_num = 0;
        let mut free_list_tmp = vec![];
        let mut free_total = 0;

        let content_len = self.content.len();

        while ix < content_len {
            block_num += 1;

            let block_tag = self.block_tag(ix);
            let block_size = self.block_size(ix) as usize;

            if block_tag == TAG_NONE {
                free_list_tmp.push(ix);
                free_total += block_size + HEADER_SIZE;

                debug_assert!(!self.bitmap_at(ix));
                debug_assert!(self[ix] == LIST_END || valid_address(self[ix]));
            } else {
                debug_assert!(self.bitmap_at(ix));
            }
            ix = self.next_block_ix(ix);
        }

        log::debug!(
            "[validate] blocks {} free {} with {} ixs\n",
            block_num,
            free_list_tmp.len(),
            free_total
        );

        debug_assert_eq!(ix - HEADER_SIZE, content_len);

        let mut free_list_ixs = self.free_list_iter();

        // log::debug!("free lists trav {:?}", free_list_tmp);
        // log::debug!("free lists iter {:?}", free_list_ixs);

        debug_assert_eq!(free_list_ixs.len(), free_list_tmp.len());
        debug_assert_eq!(self.free_ix_count(), free_total);

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
            free_list: LIST_END,
            bitmap_ix: 0,
            heap_ix: 0,
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
        assert_eq!(ix, 2);
        assert_eq!(bitoff, 31);
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

    #[test]
    fn consq_00() {
        // NOTE you can't use create_heap because it calls set_heap_addr
        // which will insert things into the free list.
        let mut mem = Memory {
            content: vec![0; 100],
            free_list: LIST_END,
            bitmap_ix: 0,
            heap_ix: 0,
        };
        let mut ixs: Vec<usize> = vec![18, 31, 32, 33, 76, 99];
        for &ix in ixs.iter() {
            mem.consq(ix);
            let hd = mem.car();
            assert_eq!(hd, Some(ix));
        }

        let free_list = mem.free_list_iter();

        assert_eq!(ixs.len(), free_list.len());

        ixs.reverse();

        for (&f, s) in ixs.iter().zip(free_list) {
            assert_eq!(f, s);
        }
    }
}
