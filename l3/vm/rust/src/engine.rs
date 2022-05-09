mod opcode;

use std::io;

use crate::memory::Memory;
use crate::{L3Value, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};

pub struct Engine {
    mem: Memory,
    free_boundary: usize,
    top_frames: [usize; 2],
    top_frame_index: usize,
    regs: usize,
}

fn extract_u(instr: L3Value, start: u32, len: u32) -> L3Value {
    (instr >> start) & ((1 << len) - 1)
}

fn extract_s(instr: L3Value, start: u32, len: u32) -> L3Value {
    let bits = extract_u(instr, start, len);
    let m = 1 << (len - 1);
    (bits ^ m) - m
}

fn opcode(instr: L3Value) -> L3Value {
    extract_u(instr, 27, 5)
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

fn offset_pc(pc: usize, offset: L3Value) -> usize {
    ((pc as L3Value) + offset) as usize
}

impl Engine {
    pub fn new(mem: Memory) -> Engine {
        Engine {
            mem: mem,
            free_boundary: 0,
            top_frames: [0, 0],
            top_frame_index: 0,
            regs: 0,
        }
    }

    pub fn emit_instruction(&mut self, instruction: L3Value) {
        self.mem[self.free_boundary] = instruction;
        self.free_boundary += 1;
    }

    fn emit_top_frames(&mut self) {
        for i in 0..=1 {
            self.free_boundary += 1;
            self.top_frames[i] = self.free_boundary;
            self.free_boundary += 2 + 256 - 32;
            for r in 0..32 {
                self.mem[self.free_boundary + r] = r as L3Value
            }
            self.free_boundary += 32;
        }

        self.set_frame_size(self.top_frames[0], 2);
        self.set_frame_size(self.top_frames[1], 0);

        self.top_frame_index = 0;
        self.regs = self.curr_frame() + 2;
    }

    fn curr_frame(&self) -> usize {
        self.top_frames[self.top_frame_index]
    }

    fn other_frame(&self) -> usize {
        self.top_frames[1 - self.top_frame_index]
    }

    fn set_ra(&mut self, instr: L3Value, new_value: L3Value) {
        self.mem[self.regs + extract_u(instr, 0, 8) as usize] = new_value
    }

    fn ra(&self, instr: L3Value) -> L3Value {
        self.mem[self.regs + extract_u(instr, 0, 8) as usize]
    }

    fn rb(&self, instr: L3Value) -> L3Value {
        self.mem[self.regs + extract_u(instr, 8, 8) as usize]
    }

    fn rc(&self, instr: L3Value) -> L3Value {
        self.mem[self.regs + extract_u(instr, 16, 8) as usize]
    }

    fn arith<F>(&mut self, instr: L3Value, op: F)
    where
        F: Fn(L3Value, L3Value) -> L3Value,
    {
        self.set_ra(instr, op(self.rb(instr), self.rc(instr)))
    }

    fn cond_pc<F>(&mut self, pc: usize, instr: L3Value, op: F) -> usize
    where
        F: Fn(L3Value, L3Value) -> bool,
    {
        let cond = op(self.ra(instr), self.rb(instr));
        offset_pc(pc, if cond { extract_s(instr, 16, 11) } else { 1 })
    }

    fn set_frame_size(&mut self, frame: usize, size: usize) {
        debug_assert!(self.top_frames.contains(&frame));
        self.mem.set_block_header(frame, TAG_REGISTER_FRAME, size);
    }

    fn call(&mut self, target_pc: usize, ret_pc: L3Value, parent_frame: L3Value) -> usize {
        let next = self.other_frame();
        self.mem[next + 0] = ret_pc;
        self.mem[next + 1] = parent_frame;
        self.top_frame_index = 1 - self.top_frame_index;
        self.regs = self.curr_frame() + 2;
        target_pc
    }

    fn ret(&mut self, ret_value: L3Value) -> usize {
        let curr_ix = self.curr_frame();
        let ret_pc = addr_to_ix(self.mem[curr_ix + 0]);
        let parent_frame = addr_to_ix(self.mem[curr_ix + 1]);
        if parent_frame == self.other_frame() {
            self.top_frame_index = 1 - self.top_frame_index;
            self.regs = self.curr_frame() + 2;
        } else {
            let parent_size = self.mem.block_size(parent_frame) as usize;
            for i in 0..=parent_size {
                // TODO optimize
                self.mem[curr_ix - 1 + i] = self.mem[parent_frame - 1 + i]
            }
            self.mem.free(parent_frame);
        }
        self.mem[self.regs + 223] = ret_value;
        ret_pc
    }

    pub fn run(&mut self) -> L3Value {
        self.emit_top_frames();
        self.mem.set_heap_start(self.free_boundary);

        let mut pc: usize = 0;

        loop {
            let inst = self.mem[pc];

            match opcode(inst) {
                opcode::ADD => {
                    self.arith(inst, |x, y| x.wrapping_add(y));
                    pc += 1;
                }
                opcode::SUB => {
                    self.arith(inst, |x, y| x.wrapping_sub(y));
                    pc += 1;
                }
                opcode::MUL => {
                    self.arith(inst, |x, y| x.wrapping_mul(y));
                    pc += 1;
                }
                opcode::DIV => {
                    self.arith(inst, |x, y| x.wrapping_div(y));
                    pc += 1;
                }
                opcode::MOD => {
                    self.arith(inst, |x, y| x.wrapping_rem(y));
                    pc += 1;
                }
                opcode::LSL => {
                    self.arith(inst, |x, y| x.wrapping_shl(y as u32));
                    pc += 1;
                }
                opcode::LSR => {
                    self.arith(inst, |x, y| x.wrapping_shr(y as u32));
                    pc += 1;
                }
                opcode::AND => {
                    self.arith(inst, |x, y| x & y);
                    pc += 1;
                }
                opcode::OR => {
                    self.arith(inst, |x, y| x | y);
                    pc += 1;
                }
                opcode::XOR => {
                    self.arith(inst, |x, y| x ^ y);
                    pc += 1;
                }
                opcode::JLT => pc = self.cond_pc(pc, inst, |x, y| x < y),
                opcode::JLE => pc = self.cond_pc(pc, inst, |x, y| x <= y),
                opcode::JEQ => pc = self.cond_pc(pc, inst, |x, y| x == y),
                opcode::JNE => pc = self.cond_pc(pc, inst, |x, y| x != y),
                opcode::JI => pc = offset_pc(pc, extract_s(inst, 0, 27)),
                opcode::CALL_NI => {
                    pc = self.call(
                        addr_to_ix(self.ra(inst)),
                        ix_to_addr(pc + 1),
                        ix_to_addr(self.curr_frame()),
                    )
                }
                opcode::CALL_ND => {
                    pc = self.call(
                        offset_pc(pc, extract_s(inst, 0, 27)),
                        ix_to_addr(pc + 1),
                        ix_to_addr(self.curr_frame()),
                    )
                }
                opcode::CALL_TI => {
                    let curr = self.curr_frame();
                    pc = self.call(
                        addr_to_ix(self.ra(inst)),
                        self.mem[curr + 0],
                        self.mem[curr + 1],
                    )
                }
                opcode::CALL_TD => {
                    let curr = self.curr_frame();
                    pc = self.call(
                        offset_pc(pc, extract_s(inst, 0, 27)),
                        self.mem[curr + 0],
                        self.mem[curr + 1],
                    )
                }
                opcode::RET => {
                    pc = self.ret(self.ra(inst));
                }
                opcode::HALT => {
                    return self.ra(inst);
                }
                opcode::LDLO => {
                    self.set_ra(inst, extract_s(inst, 8, 19));
                    pc += 1;
                }
                opcode::LDHI => {
                    let hi16 = extract_u(inst, 8, 16) << 16;
                    let lo16 = self.ra(inst) & 0xFFFF;
                    self.set_ra(inst, hi16 | lo16);
                    pc += 1;
                }
                opcode::MOVE => {
                    self.set_ra(inst, self.rb(inst));
                    pc += 1;
                }
                opcode::ARGS => {
                    let curr = self.curr_frame();
                    let next = self.other_frame();
                    if self.mem[curr + 1] == ix_to_addr(next) {
                        let next_c = self.mem.copy(next, curr);
                        self.mem[curr + 1] = ix_to_addr(next_c);
                    }

                    let mut i = 2;
                    let mut inst = inst;
                    while opcode(inst) == opcode::ARGS {
                        self.mem[next + i + 0] = self.ra(inst);
                        self.mem[next + i + 1] = self.rb(inst);
                        self.mem[next + i + 2] = self.rc(inst);
                        i += 3;
                        pc += 1;
                        inst = self.mem[pc];
                    }
                    self.set_frame_size(next, i);
                }
                opcode::FRAME => {
                    let size = extract_u(inst, 0, 8);
                    let curr = self.curr_frame();
                    let curr_size = self.mem.block_size(curr) - 2;
                    if curr_size < size {
                        for i in (curr_size as usize)..(size as usize) {
                            self.mem[self.regs + i] = 0 // TODO optimize
                        }
                    }
                    self.set_frame_size(curr, 2 + size as usize);
                    pc += 1;
                }
                opcode::BALO => {
                    let tag = extract_u(inst, 16, 8);
                    let size = self.rb(inst);
                    let block_ix = self.mem.allocate(tag, size, self.curr_frame());
                    self.set_ra(inst, ix_to_addr(block_ix));
                    pc += 1;
                }
                opcode::BSIZ => {
                    let block_ix = addr_to_ix(self.rb(inst));
                    self.set_ra(inst, self.mem.block_size(block_ix));
                    pc += 1;
                }
                opcode::BTAG => {
                    let block_ix = addr_to_ix(self.rb(inst));
                    self.set_ra(inst, self.mem.block_tag(block_ix));
                    pc += 1;
                }
                opcode::BGET => {
                    let block_ix = addr_to_ix(self.rb(inst));
                    let index = self.rc(inst) as usize;
                    self.set_ra(inst, self.mem[block_ix + index]);
                    pc += 1;
                }
                opcode::BSET => {
                    let block_ix = addr_to_ix(self.rb(inst));
                    let index = self.rc(inst) as usize;
                    self.mem[block_ix + index] = self.ra(inst);
                    pc += 1;
                }
                opcode::IO => {
                    use std::io::{Read, Write};

                    match extract_u(inst, 8, 8) {
                        0 => {
                            io::stdout().flush().expect("flush error");

                            let mut byte = [0u8; 1];
                            match io::stdin().read(&mut byte) {
                                Ok(1) => self.set_ra(inst, byte[0] as L3Value),
                                _ => self.set_ra(inst, -1),
                            }
                        }
                        1 => {
                            let byte = [self.ra(inst) as u8; 1];
                            io::stdout().write(&byte).expect("write error");
                        }
                        unknown_command => panic!("unknown IO command {}", unknown_command),
                    }
                    pc += 1;
                }
                unknown_opcode => panic!("unknown opcode {}", unknown_opcode),
            }
        }
    }
}
