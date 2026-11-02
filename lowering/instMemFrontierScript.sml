(*
 * Frontier checks per opcode
 *
 * inst_mem_below_frontier inst s says that every source memory range of
 * inst in s lies below the allocation frontier s.vs_alloca_next.  Here it
 * is unfolded per opcode into a condition on the operands' values, so a
 * leaf proof that knows where an instruction reads and writes discharges
 * it without the range tables.  DRET's ranges come from its parsed shape
 * (dret_memory_read_ranges), so it gets no per-opcode form.
 *
 * TOP-LEVEL:
 *   below_frontier_<opcode>   — the check for each opcode in the tables
 *   below_frontier_no_ranges  — an opcode outside the tables passes
 *   alloca_region_below_frontier
 *                             — an access inside an ALLOCA'd region
 *
 * Helpers:
 *   eval_operand_inst_idx, eval_operands_inst_idx,
 *   source_memory_read_ranges_inst_idx, source_memory_write_ranges_inst_idx,
 *   inst_mem_below_frontier_inst_idx [simp]
 *                             — the check ignores the instruction index
 *)

Theory instMemFrontier
Ancestors
  list rich_list venomState venomInst venomExecSemantics venomMemDefs
  codegenRel contextCodegenRel unitTransformDefs instIdxIndep

(* ===== Frontier checks per opcode ===== *)

(* The range tables only look at operands and the frame pointer, so the
   check ignores the instruction index. *)
Theorem eval_operand_inst_idx[simp] = instIdxIndepTheory.eval_op_inst_idx

Theorem eval_operands_inst_idx[simp] = instIdxIndepTheory.eval_ops_inst_idx

Theorem source_memory_read_ranges_inst_idx[simp]:
  !inst s n.
    source_memory_read_ranges inst (s with vs_inst_idx := n) =
    source_memory_read_ranges inst s
Proof
  rw[source_memory_read_ranges_def, memory_range_of_operands_def,
     dret_memory_read_ranges_def]
QED

Theorem source_memory_write_ranges_inst_idx[simp]:
  !inst s n.
    source_memory_write_ranges inst (s with vs_inst_idx := n) =
    source_memory_write_ranges inst s
Proof
  rw[source_memory_write_ranges_def, fixed_source_write_range_def,
     sized_source_write_range_def]
QED

Theorem inst_mem_below_frontier_inst_idx[simp]:
  !inst s n.
    inst_mem_below_frontier inst (s with vs_inst_idx := n) <=>
    inst_mem_below_frontier inst s
Proof
  rw[inst_mem_below_frontier_def]
QED

(* An opcode outside both range tables touches no source memory. *)
Theorem below_frontier_no_ranges:
  !inst s.
    ~MEM inst.inst_opcode
      [MLOAD; ILOAD; MCOPY; DRET; RETURN; REVERT; SHA3; LOG; CALL; STATICCALL;
       DELEGATECALL; CREATE; CREATE2; MSTORE; MSTORE8; ISTORE; CALLDATACOPY;
       RETURNDATACOPY; DLOADBYTES; CODECOPY; EXTCODECOPY] ==>
    inst_mem_below_frontier inst s
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

(* The checks for the opcodes the lowering emits, each as the condition on
   the operands' values; an operand that does not evaluate gives no
   range. *)
Theorem below_frontier_MLOAD:
  !id op outs s.
    inst_mem_below_frontier (mk_inst id MLOAD [op] outs) s <=>
    !off. eval_operand op s = SOME off ==> w2n off + 32 <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, mk_inst_def] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem below_frontier_ILOAD:
  !id op outs s.
    inst_mem_below_frontier (mk_inst id ILOAD [op] outs) s <=>
    !off. eval_operand op s = SOME off ==> w2n off + 32 <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, mk_inst_def] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem below_frontier_MSTORE:
  !id dst v outs s.
    inst_mem_below_frontier (mk_inst id MSTORE [dst; v] outs) s <=>
    !d w. eval_operand dst s = SOME d /\ eval_operand v s = SOME w ==>
          w2n d + 32 <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, fixed_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand v s` >> simp[]
QED

Theorem below_frontier_MSTORE8:
  !id dst v outs s.
    inst_mem_below_frontier (mk_inst id MSTORE8 [dst; v] outs) s <=>
    !d w. eval_operand dst s = SOME d /\ eval_operand v s = SOME w ==>
          w2n d + 1 <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, fixed_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand v s` >> simp[]
QED

Theorem below_frontier_ISTORE:
  !id dst v outs s.
    inst_mem_below_frontier (mk_inst id ISTORE [dst; v] outs) s <=>
    !d w. eval_operand dst s = SOME d /\ eval_operand v s = SOME w ==>
          w2n d + 32 <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, fixed_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand v s` >> simp[]
QED

Theorem below_frontier_MCOPY:
  !id dst src len outs s.
    inst_mem_below_frontier (mk_inst id MCOPY [dst; src; len] outs) s <=>
    !d a n. eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
            eval_operand len s = SOME n ==>
            (w2n n = 0 \/ w2n a + w2n n <= s.vs_alloca_next) /\
            (w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next)
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_CALLDATACOPY:
  !id dst src len outs s.
    inst_mem_below_frontier (mk_inst id CALLDATACOPY [dst; src; len] outs) s <=>
    !d a n. eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
            eval_operand len s = SOME n ==>
            w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_DLOADBYTES:
  !id dst src len outs s.
    inst_mem_below_frontier (mk_inst id DLOADBYTES [dst; src; len] outs) s <=>
    !d a n. eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
            eval_operand len s = SOME n ==>
            w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_RETURNDATACOPY:
  !id dst src len outs s.
    inst_mem_below_frontier (mk_inst id RETURNDATACOPY [dst; src; len] outs) s <=>
    !d a n. eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
            eval_operand len s = SOME n ==>
            w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_CODECOPY:
  !id dst src len outs s.
    inst_mem_below_frontier (mk_inst id CODECOPY [dst; src; len] outs) s <=>
    !d a n. eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
            eval_operand len s = SOME n ==>
            w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_EXTCODECOPY:
  !id addr dst src len outs s.
    inst_mem_below_frontier (mk_inst id EXTCODECOPY [addr; dst; src; len] outs) s <=>
    !x d a n. eval_operand addr s = SOME x /\ eval_operand dst s = SOME d /\
              eval_operand src s = SOME a /\ eval_operand len s = SOME n ==>
              w2n n = 0 \/ w2n d + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     mk_inst_def] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_SHA3:
  !id off len outs s.
    inst_mem_below_frontier (mk_inst id SHA3 [off; len] outs) s <=>
    !b n. eval_operand off s = SOME b /\ eval_operand len s = SOME n ==>
          w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand off s` >> Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_RETURN:
  !id off len outs s.
    inst_mem_below_frontier (mk_inst id RETURN [off; len] outs) s <=>
    !b n. eval_operand off s = SOME b /\ eval_operand len s = SOME n ==>
          w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand off s` >> Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_REVERT:
  !id off len outs s.
    inst_mem_below_frontier (mk_inst id REVERT [off; len] outs) s <=>
    !b n. eval_operand off s = SOME b /\ eval_operand len s = SOME n ==>
          w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand off s` >> Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_CREATE:
  !id vl off len outs s.
    inst_mem_below_frontier (mk_inst id CREATE [vl; off; len] outs) s <=>
    !v b n. eval_operand vl s = SOME v /\ eval_operand off s = SOME b /\
            eval_operand len s = SOME n ==>
            w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand vl s` >> simp[] >>
  Cases_on `eval_operand off s` >> Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_CREATE2:
  !id vl off len salt outs s.
    inst_mem_below_frontier (mk_inst id CREATE2 [vl; off; len; salt] outs) s <=>
    !v b n x. eval_operand vl s = SOME v /\ eval_operand off s = SOME b /\
              eval_operand len s = SOME n /\ eval_operand salt s = SOME x ==>
              w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand vl s` >> Cases_on `eval_operand salt s` >> simp[] >>
  Cases_on `eval_operand off s` >> Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_CALL:
  !id gas addr vl off len roff rlen outs s.
    inst_mem_below_frontier
      (mk_inst id CALL [gas; addr; vl; off; len; roff; rlen] outs) s <=>
    !g x v b n ro rn.
      eval_operand gas s = SOME g /\ eval_operand addr s = SOME x /\
      eval_operand vl s = SOME v /\ eval_operand off s = SOME b /\
      eval_operand len s = SOME n /\ eval_operand roff s = SOME ro /\
      eval_operand rlen s = SOME rn ==>
      (w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next) /\
      (w2n rn = 0 \/ w2n ro + w2n rn <= s.vs_alloca_next)
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand gas s` >> simp[] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  Cases_on `eval_operand vl s` >> simp[] >>
  Cases_on `eval_operand roff s` >> simp[] >>
  Cases_on `eval_operand rlen s` >> simp[] >>
  Cases_on `eval_operand off s` >> simp[] >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_STATICCALL:
  !id gas addr off len roff rlen outs s.
    inst_mem_below_frontier
      (mk_inst id STATICCALL [gas; addr; off; len; roff; rlen] outs) s <=>
    !g x b n ro rn.
      eval_operand gas s = SOME g /\ eval_operand addr s = SOME x /\
      eval_operand off s = SOME b /\ eval_operand len s = SOME n /\
      eval_operand roff s = SOME ro /\ eval_operand rlen s = SOME rn ==>
      (w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next) /\
      (w2n rn = 0 \/ w2n ro + w2n rn <= s.vs_alloca_next)
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand gas s` >> simp[] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  Cases_on `eval_operand roff s` >> simp[] >>
  Cases_on `eval_operand rlen s` >> simp[] >>
  Cases_on `eval_operand off s` >> simp[] >>
  Cases_on `eval_operand len s` >> simp[]
QED

Theorem below_frontier_DELEGATECALL:
  !id gas addr off len roff rlen outs s.
    inst_mem_below_frontier
      (mk_inst id DELEGATECALL [gas; addr; off; len; roff; rlen] outs) s <=>
    !g x b n ro rn.
      eval_operand gas s = SOME g /\ eval_operand addr s = SOME x /\
      eval_operand off s = SOME b /\ eval_operand len s = SOME n /\
      eval_operand roff s = SOME ro /\ eval_operand rlen s = SOME rn ==>
      (w2n n = 0 \/ w2n b + w2n n <= s.vs_alloca_next) /\
      (w2n rn = 0 \/ w2n ro + w2n rn <= s.vs_alloca_next)
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def] >>
  Cases_on `eval_operand gas s` >> simp[] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  Cases_on `eval_operand roff s` >> simp[] >>
  Cases_on `eval_operand rlen s` >> simp[] >>
  Cases_on `eval_operand off s` >> simp[] >>
  Cases_on `eval_operand len s` >> simp[]
QED

(* LOG as the lowering emits it: the topic count, the topics, then the
   data length and pointer; the table reads them from the end. *)
Theorem below_frontier_LOG:
  !id n topics len buf outs s.
    LENGTH topics = n /\ n < dimword (:256) ==>
    (inst_mem_below_frontier
       (mk_inst id LOG (Lit (n2w n) :: topics ++ [len; buf]) outs) s <=>
     !ts b l. eval_operands (REVERSE topics) s = SOME ts /\
              eval_operand buf s = SOME b /\ eval_operand len s = SOME l ==>
              w2n l = 0 \/ w2n b + w2n l <= s.vs_alloca_next)
Proof
  rw[inst_mem_below_frontier_def, source_memory_read_ranges_def,
     source_memory_write_ranges_def, memory_range_of_operands_def,
     mk_inst_def, REVERSE_APPEND] >>
  Cases_on `eval_operands (REVERSE topics) s` >> simp[] >>
  Cases_on `eval_operand buf s` >> Cases_on `eval_operand len s` >> simp[]
QED

(* An access inside an ALLOCA'd region is below the frontier. *)
Theorem alloca_region_below_frontier:
  !s aid b sz off len.
    alloca_next_valid s /\ FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
    off + len <= b + sz ==>
    off + len <= s.vs_alloca_next
Proof
  rw[alloca_next_valid_def] >> res_tac >> decide_tac
QED
