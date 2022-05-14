/**
 * Garbage Collector and Memory Manager for the L3 language.
 *
 * Gavin Gray, 05.2022
 * ETH Zuerich
 * */
// TODO checklist
//
// The performance is *ok* but who wants to stop there.
// [ ] profile the runtime and find hot zones
//
// Additionally, the heuristic for being able to split a block is
// currently very weak.
// [ ] play around with additionaly heuristics
//
// [ ] implement a compaction algorithm for when
//      external fragmentation is so bad (due to bad heuristic).
use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};
use std::cmp;
use unfold::unfold;

const HEADER_SIZE: usize = 1;
const TAG_NONE: L3Value = 0xFF;
const LIST_END: L3Value = -1;
const MIN_BLOCK_SIZE: usize = 1;
const MIN_SPLIT_SIZE: usize = MIN_BLOCK_SIZE + HEADER_SIZE;
const NUM_FREE_LISTS: usize = 32;
const FL_OTH: usize = 0;

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

fn fl_ix(ix: usize) -> usize {
    if ix < NUM_FREE_LISTS {
        ix
    } else {
        FL_OTH
    }
}

fn should_split(total: usize, first: usize) -> bool {
    debug_assert!(total >= first);
    (total == first) || (total - first >= 5 * MIN_SPLIT_SIZE)
}

/// L3 VM Program Memory
pub struct Memory {
    /// Allocated memory for the entire program
    content: Vec<L3Value>,
    /// Start of each free list by size
    free_lists: [L3Value; NUM_FREE_LISTS],
    /// Index at which the bitmap starts
    bitmap_ix: usize,
    /// Index at which the available heap memory starts
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

/// Compute the ceiling of a / b
fn div_up(a: usize, b: usize) -> usize {
    // We *know* that the hint is exact,
    // this is thus precisely the amount of
    // chunks of length `b` each
    (0..a).step_by(b).size_hint().0
}

/// Given a size `total`, partiiton it into two slices such that
/// the first `smaller` segment is at least (1 / `ratio`) that of the right
/// `bigger` segment.
///
/// @param: `total`: the total size to split.
/// @param: `ratio`: fraction of size dedicated to `smaller`.
/// @returns: `(smaller, bigger)`
/// @ensures: `smaller + bigger = total`.
fn partition_by_ratio(total: usize, ratio: usize) -> (usize, usize) {
    let mut smaller = div_up(total, ratio);
    let mut bigger = total - smaller;
    let mut old_s;
    // FIXME this pseudo fixpoint method is a hack.
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
    // ---------------------------------------------------------------
    // External API *do not change*

    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            free_lists: [LIST_END; NUM_FREE_LISTS],
            bitmap_ix: 0,
            heap_ix: 0,
        }
    }

    /// Set the start of the available heap memory within the memory space content.
    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());

        let remaining_size = self.content.len() - heap_start_index;
        let (bitmap_size, heap_size) = partition_by_ratio(remaining_size, 32);

        debug_assert_eq!(bitmap_size + heap_size, remaining_size);
        debug_assert!(bitmap_size >= heap_size / 32);

        self.heap_ix = heap_start_index + bitmap_size;
        self.bitmap_ix = heap_start_index;
        self.zero_memory(heap_start_index, self.content.len());

        // Set up the first unallocated block of memory
        let unallocated_block_ix = self.heap_ix + HEADER_SIZE;
        let unallocated_block_size = (self.content.len() - self.heap_ix) - HEADER_SIZE;

        self.set_block_header(unallocated_block_ix, TAG_NONE, unallocated_block_size);

        // set the start of the list
        self.consq(unallocated_block_ix);

        log::info!("Bitmap memory IX {}", self.bitmap_ix);
        log::info!("Heap memory IX {}", self.heap_ix);
        log::info!("Free List IX {}", addr_to_ix(self.free_lists[FL_OTH]));

        debug_assert!(self.validate_memory());
    }

    /// Allocate a block with the given `tag` and `size`. If no available block is found,
    /// garbage collection should retain all blocks reachable from `root`.
    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize) -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);
        debug_assert!(self.validate_memory());

        // NOTE MIN_BLOCK_SIZE is chosen to  accomodate free list nodes
        let min_size = cmp::max(size as usize, MIN_BLOCK_SIZE);
        let mut found_memory = self.find_memory(min_size);

        if found_memory.is_none() {
            log::info!("GC with root {} min_size {}", root, min_size);
            self.gc(root, false); // FIXME is there a smarter way to call this?
                                  // TODO optimize. Potentially you could find a block of memory
                                  // while doing the garbage collection.
                                  // TODO use a compacting algorithm to reduce external fragmentation
                                  // if a block is still not found after GCing.
            found_memory = self.find_memory(min_size);
        }

        match found_memory {
            None => {
                log::debug!("Free Lists");
                for s in 0..NUM_FREE_LISTS {
                    log::debug!("{} -> {:?}", s, self.free_list_single(s));
                }
                log::debug!("Total {} available indices", self.free_ix_count());
                panic!("out of memory")
            }
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
                // Memory state afterwards is valid
                debug_assert!(self.validate_memory());

                block
            }
        }
    }

    #[allow(unused_variables)]
    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) {
            self[copy + i] = self[block + i]
        }
        log::debug!("Copying {} to {}", block, copy);
        copy
    }

    /// Free a block back to the allocator.
    pub fn free(&mut self, block: usize) {
        debug_assert!(self.valid_index(block));

        log::debug!("free frame {}", block);

        let was_marked = self.unmark_bitmap_at(block);
        self.set_block_header_tag(block, TAG_NONE);

        debug_assert!(was_marked);

        self.consq(block);
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
    // Internal utilities

    fn gc(&mut self, root: usize, _compact_heap: bool) {
        debug_assert!(self.validate_memory());

        // mark all the objects that are reachable from `root`
        self.mark(root);
        // sweep the heap and reclaim blocks
        self.sweep();

        debug_assert!(self.validate_memory());
    }

    /// Mark
    ///
    /// Starting from the frame `root`, identify all of the blocks
    /// that are still reachable. These blocks must be preserved during
    /// the collection's sweep phase.
    fn mark(&mut self, root: usize) {
        debug_assert_eq!(self.block_tag(root), TAG_REGISTER_FRAME);

        let mut work = vec![];

        work.push(root);

        while 0 < work.len() {
            let block = work.pop().unwrap();

            log::debug!("GC Mark at {}", block);

            let block_size = self.block_size(block) as usize;
            (block..(block + block_size)).for_each(|ix| {
                if valid_address(self[ix]) {
                    let ix = addr_to_ix(self[ix]);
                    if (0 < ix
                        && ix < self.content.len()
                        && (!self.valid_index(ix) && self.block_tag(ix) == TAG_REGISTER_FRAME))
                        || (self.valid_index(ix) && self.unmark_bitmap_at(ix))
                    {
                        work.push(ix);
                    }
                }
            });
        }
    }

    /// Sweep
    ///
    /// Free all of the block locations that were not identified during the
    /// marking phase.
    /// Sweeping coalesces blocks together that are adjacent in memory. The
    /// sweep phase will traverse the entirety of the memory, reconstructing
    /// the free list from scratch. Thus, the free list that existed beforehand
    /// is destroyed and rebuilt.
    ///
    /// NOTE `mark` must be called before sweep as the bitmap values are inversed.
    fn sweep(&mut self) {
        // The start of available memory to allocate.
        let mut block = self.heap_ix + HEADER_SIZE;
        let end_ix = self.content.len();

        self.clearq(); // XXX destroy the free list

        debug_assert!({ (0..NUM_FREE_LISTS).all(|s| self.free_lists[s] == LIST_END) });

        let mut previous_free: Option<usize> = None;

        // TODO these counters are only used in debugging, other than
        // macros is there a way I can compile away variables in Rust.
        let mut kept_count = 0;
        let mut free_count = 0;

        while block < end_ix {
            let block_tag = self.block_tag(block);
            let block_size = self.block_size(block) as usize;

            let _marked_before = self.bitmap_at(block);

            debug_assert!(self.valid_index(block));

            match (block_tag, previous_free) {
                (tag, Some(last_free_ix)) if tag == TAG_NONE || self.bitmap_at(block) => {
                    free_count += 1; // TODO

                    self.unmark_bitmap_at(block);
                    self.set_block_header_tag(block, TAG_NONE);
                    self.block_clear(block);

                    // coalesce the blocks
                    self.coalesce_blocks(last_free_ix, block);
                }

                // NOTE blocks still tagged in the bitmap are *unreachable*
                (tag, None) if tag == TAG_NONE || self.bitmap_at(block) => {
                    free_count += 1; // TODO

                    self.unmark_bitmap_at(block);
                    self.set_block_header_tag(block, TAG_NONE);
                    self.block_clear(block);

                    self.consq(block);
                    previous_free = Some(block);
                }

                // Block is not getting freed. Mark the bitmap to set it as alive.
                (_, _) => {
                    kept_count += 1; // TODO
                    self.mark_bitmap_at(block);
                    previous_free = None;
                }
            };

            #[cfg(debug_assertions)]
            if _marked_before && !self.bitmap_at(block) {
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

    /// Find Possible Memory
    ///
    /// Returns the block index to the allocated memory.
    /// NOTE this memory is already removed from the free list and marked.
    fn find_memory(&mut self, size: usize) -> Option<usize> {
        debug_assert!(0 < size);

        // // Only check in the appropriate size bucket
        // if size < NUM_FREE_LISTS && self.free_lists[size] != LIST_END {
        //     let ix = addr_to_ix(self.free_lists[size]);
        //     self.free_lists[size] = self[ix];
        //     return Some(ix);
        // }

        for i_size in 1..NUM_FREE_LISTS {
            if self.free_lists[i_size] == LIST_END // List empty
                || i_size < size // elements too small
                || !should_split(i_size, size)
            //elements too small to split
            {
                continue;
            }

            let ix = addr_to_ix(self.free_lists[i_size]);
            self.free_lists[i_size] = self[ix];
            self.split_block(ix, size);

            return Some(ix);
        }

        // look for a matching block in the case when size is too big
        // or a block is unavailable in smaller sizes.

        /* free list
         * o
         * |
         * |
         * v
         * +---------+---------+---------+---------+
         * |         |         |         |         |
         * | o-------------------->  o--------------------
         * |         |         |         |         |
         * +---------+---------+---------+---------+
         *
         * */

        unsafe {
            let mut prev: *mut L3Value = &mut self.free_lists[FL_OTH];
            let mut addr = self.free_lists[FL_OTH];

            while addr != LIST_END {
                let ix = addr_to_ix(addr);
                let ix_size = self.block_size(ix) as usize;

                if ix_size >= size && should_split(ix_size, size) {
                    *prev = self[ix];
                    self.split_block(ix, size);

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
     * The block pointer to by `block_ix` needs to be a free block
     * XXX but not currently in the free list.
     * */
    fn split_block(&mut self, block_ix: usize, min_size: usize) {
        debug_assert!(!self.free_list_iter().contains(&block_ix));

        let block_size = self.block_size(block_ix) as usize;

        debug_assert!(0 < min_size);
        debug_assert_eq!(self.block_tag(block_ix), TAG_NONE);

        debug_assert!(min_size <= block_size);

        if min_size == block_size {
            return;
        }

        // Assume that this method is only run when
        // - min_sizse == block_size
        // - the block should be split
        debug_assert!(should_split(block_size, min_size));

        let rem_size = block_size - min_size - HEADER_SIZE;
        let next_block_ix = block_ix + min_size + HEADER_SIZE;
        // setup the header for the next block
        self.set_block_header_size(block_ix, min_size);
        self.set_block_header(next_block_ix, TAG_NONE, rem_size);

        log::debug!("split block {} {}", block_ix, next_block_ix);

        self.block_clear(next_block_ix);
        self.consq(next_block_ix);
    }

    /// Coalesce Blocks
    ///
    /// Given two consecutive blocks in memory
    /// +------+------+------+------+
    /// |prev  |free  |next  |rnd   |
    /// |header|list  |header| mem  |
    /// |<tag> |ptr   |<tag> | . .  |
    /// |<size>|o     |<size>| ..  .|
    /// +------+|-----+------+------+
    ///         |->
    /// Increase the size of the previous to gobble the
    /// memory coming afterward.
    ///
    /// +------+------+------+------+
    /// |prev  |free     rnd        |
    /// |header|list      .  mem    |
    /// |<tag> |ptr     .   . .     |
    /// |<size>|o       .   ..  .   |
    /// +------+|-----+------+------+
    ///         |-->
    ///
    /// NOTE coalesce_blocks takes advantage of the fact that
    /// the 'prev' block is always at the beginning of a free
    /// list. This means that once it is updated it needs to be moved
    /// to the appropriate bucket.
    fn coalesce_blocks(&mut self, prev: usize, next: usize) {
        debug_assert!(prev < next);
        debug_assert!({
            (0..NUM_FREE_LISTS)
                .any(|s| self.free_lists[s] != LIST_END && addr_to_ix(self.free_lists[s]) == prev)
        });

        let prev_size = self.block_size(prev) as usize;
        let next_size = self.block_size(next) as usize;

        self.cdrq(prev_size); // Remove from current list

        let prev_tag = self.block_tag(prev);
        let next_tag = self.block_tag(next);

        debug_assert_eq!(prev_tag, TAG_NONE);
        debug_assert_eq!(next_tag, TAG_NONE);
        debug_assert_eq!(prev + prev_size + HEADER_SIZE, next);

        let coalesced_size = prev_size + next_size + HEADER_SIZE;

        self.set_block_header_size(prev, coalesced_size);

        self.consq(prev); // add back to the list
    }

    /// Clear the address `block_start`
    fn block_clear(&mut self, _block_start: usize) {
        #[cfg(debug_assertions)]
        {
            debug_assert!(!self.bitmap_at(_block_start));
            debug_assert_eq!(self.block_tag(_block_start), TAG_NONE);

            let size = self.block_size(_block_start) as usize;
            self.zero_memory(_block_start, _block_start + size);

            debug_assert_eq!(self.block_size(_block_start) as usize, size);
            debug_assert_eq!(self.block_tag(_block_start), TAG_NONE);
        }
    }

    /// Clear the memory in `contents` from start to end (inclusive, exclusive)
    ///
    /// NOTE in release mode this function is not run. If memory desperately needs
    /// to be zeroed then use a different method.
    fn zero_memory(&mut self, _start: usize, _end: usize) {
        #[cfg(debug_assertions)]
        {
            log::debug!("Zero memory [{}, {})", _start, _end);
            for i in &mut self.content[_start.._end] {
                *i = 0;
            }
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

    /// Modify the block tag without modifying the size.
    fn set_block_header_tag(&mut self, block: usize, tag: L3Value) {
        let size = self.block_size(block) as usize;
        self.set_block_header(block, tag, size);
    }

    /// Modify the block size without modifying the tag.
    fn set_block_header_size(&mut self, block: usize, size: usize) {
        let tag = self.block_tag(block);
        self.set_block_header(block, tag, size);
    }

    /// Poll the status of the bitmap at  `block` address.
    fn bitmap_at(&self, block: usize) -> bool {
        let (ix, block_off) = self.ix_to_bitmap_addr(block);
        ((self[ix] >> block_off) & 0x1) == 0x1
    }

    /// Set the value of the bitmap at address `block` to be high.
    fn mark_bitmap_at(&mut self, block: usize) {
        let (ix, block_off) = self.ix_to_bitmap_addr(block);
        // Set bit to be high
        let unmarked = self[ix];
        self[ix] = unmarked | (1 << block_off);
    }

    /// Set the value of the bitmap at address `block` to be low.
    ///
    /// @returns: the former value of the bitmap at address `block`.
    fn unmark_bitmap_at(&mut self, block: usize) -> bool {
        let (ix, block_off) = self.ix_to_bitmap_addr(block);
        let marked = self[ix];
        let mask = usize::MAX ^ (1 << block_off);
        // Set bit to be low
        self[ix] = ((marked as usize) & mask) as L3Value;
        marked != self[ix]
    }

    fn valid_index(&self, ix: usize) -> bool {
        self.heap_ix < ix && ix < self.content.len()
    }

    /// Add the block at `elem_ix` to a free list of appropriate size.
    fn consq(&mut self, elem_ix: usize) {
        let size = self.block_size(elem_ix) as usize;
        let ix = fl_ix(size);
        let list_addr = self.free_lists[ix];
        let new_list_addr = ix_to_addr(elem_ix);
        self[elem_ix] = list_addr;
        self.free_lists[ix] = new_list_addr;
    }

    /// Remove the first element from the free list with block `size`.
    fn cdrq(&mut self, size: usize) {
        debug_assert!(size < NUM_FREE_LISTS);
        debug_assert!(self.free_lists[size] != LIST_END);
        let ixs = fl_ix(size);
        let ix = addr_to_ix(self.free_lists[ixs]);
        self.free_lists[ixs] = self[ix];
    }

    /// Clear the Free List
    fn clearq(&mut self) {
        for i in 0..NUM_FREE_LISTS {
            self.free_lists[i] = LIST_END;
        }
    }

    // ---------------------------------------------------------------
    // Testing utilities
    //
    // NOTE all functions below should *not* be called in release mode.
    // The function bodies are removed when cfg(debug_assertions) are
    // off, allowing the compiler to remove the functions entirely.
    #[allow(unreachable_code)]
    #[allow(unused_variables)]
    fn free_list_single(&self, size: usize) -> Vec<usize> {
        #[cfg(not(debug_assertions))]
        panic!("free_list_single invoked");
        unfold(
            |maddr| match maddr {
                None => None,
                Some(LIST_END) => None,
                Some(addr) => {
                    // log::debug!("here {}", addr);
                    debug_assert_ne!(addr, LIST_END);
                    Some(self[addr_to_ix(addr)])
                }
            },
            Some(self.free_lists[size]),
        )
        .take_while(|o| o.map_or(false, |v| v != LIST_END))
        .map(Option::unwrap)
        .map(addr_to_ix)
        .collect()
    }

    #[allow(unreachable_code)]
    fn free_list_iter(&self) -> Vec<usize> {
        #[cfg(not(debug_assertions))]
        panic!("free_list_iter invoked");
        let mut ret: Vec<usize> = vec![];
        let vecs = (0..NUM_FREE_LISTS)
            .map(|s| self.free_list_single(s))
            .collect::<Vec<Vec<usize>>>();
        vecs.into_iter().for_each(|mut v| ret.append(&mut v));
        ret
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
     * - free list blocks are in the appropriate sized list
     * - allocated blocks are marked in bitmap
     * */
    fn validate_memory(&self) -> bool {
        #[cfg(debug_assertions)]
        {
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
                ix = block_size + HEADER_SIZE;
            }

            log::debug!(
                "[validate] blocks {} free {} with {} ixs\n",
                block_num,
                free_list_tmp.len(),
                free_total
            );

            (0..NUM_FREE_LISTS).for_each(|s| {
                let mut ls = self.free_list_single(s);

                // assert that sizes are in the right place
                ls.iter().for_each(|&b| {
                    assert!({
                        let sz = self.block_size(b) as usize;
                        (s == 0 && sz >= NUM_FREE_LISTS) || s == sz
                    })
                });

                // last positions point to LIST_END

                ls.last().into_iter().for_each(|&last_ix| {
                    debug_assert_eq!(self[last_ix], LIST_END);
                });

                ls.pop(); // Remove last element

                ls.iter().for_each(|&ix| {
                    debug_assert_eq!(self.block_tag(ix), TAG_NONE);
                    debug_assert!(valid_address(self[ix]));
                });
            });

            let free_list_ixs = self.free_list_iter();

            debug_assert_eq!(ix - HEADER_SIZE, content_len);
            debug_assert_eq!(free_list_ixs.len(), free_list_tmp.len());
            debug_assert_eq!(self.free_ix_count(), free_total);
        }
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
    // TODO the old tests are no longer usable now that they system is together.
}
