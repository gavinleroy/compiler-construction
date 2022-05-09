/**
 * Garbage Collector and Memory Manager for the L3 language.
 *
 * Gavin Gray, 05.2022
 * ETH Zuerich
 * */
use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES};
use std::collections::HashSet;
use unfold::Unfold;

const HEADER_SIZE: usize = 1;
const TAG_NONE: L3Value = 0xFF;
const LIST_END: L3Value = -1;

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
    list_ix: usize,
    bitmap_ix: usize,
    heap_ix: usize,
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

#[inline(always)]
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
            list_ix: 0,
            bitmap_ix: 0,
            heap_ix: 0,
            free_ix: 0,
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());

        let remaining_size = self.content.len() - heap_start_index;
        let (bitmap_size, heap_size) = partition_by_ratio(remaining_size, 32);

        dbg!(bitmap_size);
        dbg!(heap_size);

        debug_assert_eq!(bitmap_size + heap_size, remaining_size);
        debug_assert!(bitmap_size >= heap_size / 32);

        self.heap_ix = heap_start_index + bitmap_size;
        self.bitmap_ix = heap_start_index;
        self.mem_clear(heap_start_index, bitmap_size);

        // The free list will have a sentinal that starts at the beginning
        // of the heap. It will be unallocated memory, but not part of the
        // heap.

        let list_start_ix = self.heap_ix + HEADER_SIZE;
        // set the start of the list
        self.list_ix = dbg!(list_start_ix);
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

        self[list_start_ix] = dbg!(ix_to_addr(unallocated_block_ix));
        self.set_block_header(unallocated_block_ix, TAG_NONE, dbg!(unallocated_block_size));
        self[unallocated_block_ix] = LIST_END;

        debug_assert!(self.validate_memory());
    }

    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize) -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);
        debug_assert!(self.validate_memory());

        // FIXME don't call this all the time
        // self.gc(root);

        match self.find_memory(self.list_ix, size) {
            None => panic!("out of memory"),
            Some((prev, block)) => {
                let actual_size = self.split_block(block, size as usize);
                self.mark_bitmap_at(block);
                self.remove_from_free_list(prev, block);
                self.mem_clear(block, actual_size);
                self.set_block_header(block, tag, actual_size);

                debug_assert!(self.validate_memory());

                block
            }
        }
    }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        debug_assert!(self.validate_memory());
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) {
            self[copy + i] = self[block + i]
        }
        debug_assert!(self.validate_memory());
        copy
    }

    pub fn free(&mut self, block: usize) {
        debug_assert!(self.validate_memory());

        dbg!(block); // TODO
        let sz = self.block_size(block);
        self.set_block_header(block, TAG_NONE, sz as usize);
        self.add_to_free_list(self.list_ix, block);

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
        // TODO mark all the objects that are reachable from `root`
        self.mark(root);
        // TODO sweep the heap and reclaim blocks
        self.sweep();
    }

    fn mark(&mut self, root: usize) {
        let block_size = self.block_size(root) as usize;
        // Collect the indices that went from marked -> unmarked
        let marked_ixs: Vec<usize> = (root..(root + block_size))
            .filter(|&ix| {
                valid_address(self[ix]) && {
                    let ix = addr_to_ix(self[ix]);
                    self.unmark_bitmap_at(ix)
                }
            })
            .collect();
        marked_ixs.iter().for_each(|&ix| self.mark(ix))
    }

    fn sweep(&mut self) {
        // TODO forall heap blocks that are stil high construct the list with them
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
        ()
    }

    /* Find Possible Memory
     *
     * NOTE as the free list is singly linked, the direct address
     * to use cannot be returned. Take for example the following list:
     *
     * O -> O -> O -> O -> _
     *      ^    ^
     *      |    - memory to use
     *      - returned value
     *
     * The previous value is used, so that when the actual memory
     * is removed from the free list, the pointer can be moved forward.
     *
     * The returned memory might also be split, thus a pointer to that memory
     * is needed.
     * */
    fn find_memory(&self, curr_ix: usize, min_size: L3Value) -> Option<(usize, usize)> {
        dbg!(curr_ix);

        let next_ix = self.get_list_next(curr_ix)?;
        dbg!(next_ix);
        let next_size = self.block_size(next_ix);

        debug_assert_eq!(self.block_tag(curr_ix), TAG_NONE);
        debug_assert_eq!(self.block_tag(next_ix), TAG_NONE);

        if next_size >= min_size {
            Some((curr_ix, next_ix))
        } else {
            self.find_memory(next_ix, min_size)
        }
    }

    fn get_list_next(&self, ix: usize) -> Option<usize> {
        if self[ix] == LIST_END {
            None
        } else {
            dbg!(ix);
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

    fn mem_clear(&mut self, start: usize, size: usize) {
        (0..size).for_each(|off| {
            self[start + off] = 0; // FIXME
        });
    }

    /* Split BLock
     *
     * Try to split a block into two smaller blocks, the first of which
     * cannot be any smaller than `min_size`.
     * The block pointer to by `block_ix` needs to be a free block.
     * */
    fn split_block(&mut self, block_ix: usize, min_size: usize) -> usize {
        let block_size = self.block_size(block_ix) as usize;

        debug_assert_eq!(self.block_tag(block_ix), TAG_NONE);
        debug_assert!(min_size <= block_size);

        let rem_size = block_size - min_size;

        // If the remaining memory is large enough to be useful
        // then we should split it and then set memory accordingly.
        // FIXME pick a better heuristic for choosing to split or not.
        if rem_size >= 2 * HEADER_SIZE {
            let next_block_ix = block_ix + min_size + HEADER_SIZE;
            // setup the header for the next block
            self.set_block_header(next_block_ix, TAG_NONE, rem_size);
            self.set_block_header(block_ix, TAG_NONE, min_size);
            self[next_block_ix] = self[block_ix];
            self[block_ix] = ix_to_addr(next_block_ix);

            debug_assert!(self.validate_memory());

            min_size
        } else {
            block_size
        }
    }

    // FIXME the below functions could all be
    // collapsed into a simpler one, e.g. only the
    // thing at the end changes.

    fn bitmap_at(&self, block: usize) -> bool {
        let addr = block - self.heap_ix;
        // compute offset into the bitmap
        let bitmap_off = addr >> LOG2_VALUE_BITS;
        // compute offset into the bitmap block
        let block_off = addr & 0x1F;

        debug_assert!(self.heap_ix <= block && block < self.content.len());
        debug_assert!(block_off < 32);
        debug_assert!(self.bitmap_ix + bitmap_off < self.heap_ix);

        dbg!(addr);
        dbg!(bitmap_off);
        dbg!(block_off);

        // set bit to be high
        let ix = self.bitmap_ix + bitmap_off;
        ((self[ix] >> block_off) & 0x1) == 0x1
    }

    fn mark_bitmap_at(&mut self, block: usize) {
        let addr = block - self.heap_ix;
        // compute offset into the bitmap
        let bitmap_off = addr >> LOG2_VALUE_BITS;
        // compute offset into the bitmap block
        let block_off = addr & 0x1F;

        debug_assert!(self.heap_ix <= block && block < self.content.len());
        debug_assert!(block_off < 32);
        debug_assert!(self.bitmap_ix + bitmap_off < self.heap_ix);

        dbg!(addr);
        dbg!(bitmap_off);
        dbg!(block_off);

        // set bit to be high
        let ix = self.bitmap_ix + bitmap_off;
        let unmarked = self[ix];
        self[ix] = unmarked | (1 << block_off);
    }

    fn unmark_bitmap_at(&mut self, block: usize) -> bool {
        let addr = block - self.heap_ix;
        // compute offset into the bitmap
        let bitmap_off = addr >> 5;
        // compute offset into the bitmap block
        let block_off = addr & 0x1F;
        // set bit to be low

        debug_assert!(self.heap_ix <= block && block < self.content.len());
        debug_assert!(block_off < 32);
        debug_assert!(self.bitmap_ix + bitmap_off < self.heap_ix);

        dbg!(addr);
        dbg!(bitmap_off);
        dbg!(block_off);

        let ix = self.bitmap_ix + bitmap_off;
        let marked = self[ix];
        self[ix] = marked & (0xFFFF ^ (1 << block_off));

        dbg!(marked) != dbg!(self[ix])
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

        let free_list_ixs: Vec<usize> = Unfold::new(
            |ix| ix.and_then(|ixo| self.get_list_next(ixo)),
            Some(self.list_ix),
        )
        .take_while(Option::is_some)
        .take(self.content.len()) // Limit space to the entire memory if list is recurisve
        .map(Option::unwrap)
        .collect();

        free_list_ixs.iter().for_each(|&ix| {
            debug_assert_eq!(self.block_tag(ix), TAG_NONE);
        });

        free_list_ixs.last().into_iter().for_each(|&last_ix| {
            debug_assert_eq!(self[last_ix], LIST_END);
        });

        // self.heap_ix points to the heap boundary,
        // going one header past should start a block.
        let mut free_locs: HashSet<_> = HashSet::new();
        let mut ix = self.heap_ix + HEADER_SIZE;
        free_list_ixs.into_iter().for_each(|ix| {
            free_locs.insert(ix);
        });

        let content_len = self.content.len();
        while ix < content_len {
            dbg!(ix);
            let block_tag = self.block_tag(ix);
            let block_size = self.block_size(ix) as usize;

            if block_tag == TAG_NONE {
                debug_assert!(free_locs.contains(&ix));
                debug_assert!(!self.bitmap_at(ix));
            } else {
                debug_assert!(dbg!(self.bitmap_at(ix)));
            }
            ix += block_size + HEADER_SIZE;
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
            debug_assert!(mem.unmark_bitmap_at(ix));
        }

        for &loc in mem.content[1..4].iter() {
            assert_eq!(dbg!(loc), 0);
        }
    }
}
