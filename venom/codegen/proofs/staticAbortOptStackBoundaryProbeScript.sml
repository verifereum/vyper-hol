(* Bounded concrete stack envelopes.  No symbolic, memory or spill relation
   is used.  The source cut after DUP1 is interior to the replaced envelope;
   synchronization below is only at the two exits. *)
Theory staticAbortOptStackBoundaryProbe
Ancestors
  asmOptimizer asmSem asmIR stackOpSim stackOpAsmSim planExec
  asmOptPeephole list arithmetic asmOptimizerChecks words

Theorem static_abort_stack_shuffle_concrete_cuts:
  asm_block_at p s.as_pc
    [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"] /\
  s.as_stack = x::y::xs /\
  asm_block_at q t.as_pc [AsmOp "SWAP1"; AsmOp "DUP2"] /\
  t.as_stack = u::v::ys ==>
  asm_steps lo op p 3 s =
    AsmOK (s with <|as_stack := x::y::x::xs; as_pc := s.as_pc + 3|>) /\
  asm_steps lo op p 1 s =
    AsmOK (s with <|as_stack := x::x::y::xs; as_pc := s.as_pc + 1|>) /\
  asm_steps lq oq q 2 t =
    AsmOK (t with <|as_stack := u::v::u::ys; as_pc := t.as_pc + 2|>)
Proof
  strip_tac >> fs[asm_block_at_cons] >>
  rewrite_tac[numLib.num_CONV ``3:num``, numLib.num_CONV ``2:num``,
              numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def,
       SRULE [dup_name_def] (Q.SPECL [`lo`, `op`, `0`] asm_step_dup_ok),
       SRULE [dup_name_def] (Q.SPECL [`lo`, `op`, `1`] asm_step_dup_ok),
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `1`] asm_step_swap_ok),
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `2`] asm_step_swap_ok),
       asm_next_def, LUPDATE_def, ADD_ASSOC]
  >> (simp[listTheory.LUPDATE_compute])
QED

(* A live tag may occupy either input slot.  All non-tag words, both
   memories, both code fields, and the two request histories are independent.
   The continuation is universal in the destination state, not merely in a
   symbolically related state.  No image of the erased source cut is used. *)
Theorem static_abort_stack_shuffle_tag_continuation:
  asm_block_at p s.as_pc
    [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"] /\
  s.as_stack = x::y::xs /\
  asm_block_at q t.as_pc [AsmOp "SWAP1"; AsmOp "DUP2"] /\
  t.as_stack = u::v::ys /\
  (j = 0 \/ j = 1) /\ EL j t.as_stack = n2w off /\
  (!out. out.as_pc = t.as_pc + 2 /\
    LENGTH out.as_stack = LENGTH t.as_stack + 1 /\
    out.as_call_ctx = t.as_call_ctx /\ out.as_requests = t.as_requests /\
    EL j out.as_stack = n2w off /\
    (j = 0 ==> EL 2 out.as_stack = n2w off) ==> D out) ==>
  ?out. asm_steps lq oq q 2 t = AsmOK out /\ D out /\
    LENGTH out.as_stack = LENGTH t.as_stack + 1 /\
    out.as_call_ctx = t.as_call_ctx /\ out.as_requests = t.as_requests /\
    EL j out.as_stack = n2w off /\
    (j = 0 ==> EL 2 out.as_stack = n2w off)
Proof
  strip_tac >>
  `asm_steps lq oq q 2 t =
    AsmOK (t with <|as_stack := u::v::u::ys; as_pc := t.as_pc + 2|>)`
    by metis_tac[static_abort_stack_shuffle_concrete_cuts] >>
  qexists `t with <|as_stack := u::v::u::ys; as_pc := t.as_pc + 2|>` >>
  gvs[] >> first_x_assum irule >> simp[]
QED

(* These are the actual intermediate lists at one index.  The first pair
   exposes SWAP1/ADD, so the second stage fires and the third sees ADD,
   not the original SWAP2.  The surviving tag z moves from slot 2 to 1. *)
Theorem static_abort_stack_same_index_add_lists:
  peep_swap_pair (AsmOp "SWAP2") (AsmOp "SWAP2") (AsmOp "SWAP1")
    (AsmOp "ADD" :: rest) = (AsmOp "SWAP1" :: AsmOp "ADD" :: rest, T) /\
  peep_swap_comm (AsmOp "SWAP1" :: AsmOp "ADD" :: rest) =
    SOME (AsmOp "ADD" :: rest, T) /\
  peep_dup_swap (AsmOp "ADD" :: rest) = SOME (AsmOp "ADD" :: rest, F)
Proof
  `asm_commutative_op (AsmOp "ADD")` by EVAL_TAC >>
  simp[peep_swap_pair_def, asm_swap_op_def, peep_swap_comm_def,
       peep_dup_swap_def]
QED

(* A different pair exposes DUP1/SWAP1: the middle stage does not fire,
   while the last stage does.  The tag at input slot 3 leaves at slot 4. *)
Theorem static_abort_stack_same_index_dup_lists:
  peep_swap_pair (AsmOp "SWAP3") (AsmOp "SWAP3") (AsmOp "DUP1")
    (AsmOp "SWAP1" :: rest) = (AsmOp "DUP1" :: AsmOp "SWAP1" :: rest, T) /\
  peep_swap_comm (AsmOp "DUP1" :: AsmOp "SWAP1" :: rest) =
    SOME (AsmOp "DUP1" :: AsmOp "SWAP1" :: rest, F) /\
  peep_dup_swap (AsmOp "DUP1" :: AsmOp "SWAP1" :: rest) =
    SOME (AsmOp "DUP1" :: rest, T)
Proof
  simp[peep_swap_pair_def, asm_swap_op_def, peep_swap_comm_def,
       peep_dup_swap_def]
QED

Theorem static_abort_stack_same_index_add_tags:
  asm_block_at p s.as_pc
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"; AsmOp "ADD"] /\
  s.as_stack = x::y::tag::xs /\
  asm_block_at q t.as_pc [AsmOp "ADD"] /\
  t.as_stack = u::v::tag::ys ==>
  ?a b. asm_steps lo op p 4 s = AsmOK a /\
    asm_steps lq oq q 1 t = AsmOK b /\
    a.as_pc = s.as_pc + 4 /\ b.as_pc = t.as_pc + 1 /\
    LENGTH a.as_stack + 1 = LENGTH s.as_stack /\
    LENGTH b.as_stack + 1 = LENGTH t.as_stack /\
    EL 1 a.as_stack = tag /\ EL 1 b.as_stack = tag /\
    a.as_call_ctx = s.as_call_ctx /\ b.as_call_ctx = t.as_call_ctx /\
    a.as_requests = s.as_requests /\ b.as_requests = t.as_requests
Proof
  strip_tac >> fs[asm_block_at_cons] >>
  `!ll oo c. asm_step ll oo (AsmOp "ADD") c = asm_binop word_add c` by
    simp[asm_step_def, asm_step_op_def, asm_step_arith_def] >>
  qexistsl [`s with <|as_stack := (x + y)::tag::xs; as_pc := s.as_pc + 4|>`,
    `t with <|as_stack := (u + v)::tag::ys; as_pc := t.as_pc + 1|>`] >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def,
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `1`] asm_step_swap_ok),
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `2`] asm_step_swap_ok),
       asm_binop_def, asm_next_def, LUPDATE_compute, ADD_ASSOC, WORD_ADD_COMM]
QED

Theorem static_abort_stack_same_index_dup_tags:
  asm_block_at p s.as_pc
    [AsmOp "SWAP3"; AsmOp "SWAP3"; AsmOp "DUP1"; AsmOp "SWAP1"] /\
  s.as_stack = x::y::z::tag::xs /\
  asm_block_at q t.as_pc [AsmOp "DUP1"] /\
  t.as_stack = u::v::w::tag::ys ==>
  ?a b. asm_steps lo op p 4 s = AsmOK a /\
    asm_steps lq oq q 1 t = AsmOK b /\
    a.as_pc = s.as_pc + 4 /\ b.as_pc = t.as_pc + 1 /\
    LENGTH a.as_stack = LENGTH s.as_stack + 1 /\
    LENGTH b.as_stack = LENGTH t.as_stack + 1 /\
    EL 4 a.as_stack = tag /\ EL 4 b.as_stack = tag /\
    a.as_call_ctx = s.as_call_ctx /\ b.as_call_ctx = t.as_call_ctx /\
    a.as_requests = s.as_requests /\ b.as_requests = t.as_requests
Proof
  strip_tac >> fs[asm_block_at_cons] >>
  qexistsl [`s with <|as_stack := x::x::y::z::tag::xs; as_pc := s.as_pc + 4|>`,
    `t with <|as_stack := u::u::v::w::tag::ys; as_pc := t.as_pc + 1|>`] >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def,
       SRULE [dup_name_def] (Q.SPECL [`lo`, `op`, `0`] asm_step_dup_ok),
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `1`] asm_step_swap_ok),
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `3`] asm_step_swap_ok),
       asm_next_def, LUPDATE_compute, ADD_ASSOC]
QED

(* The option NONE caused by the same-index bound check is not an assembly
   exception (nor an execution error).  Here the entire original window
   executes normally, with arbitrary memory and at least three stack words. *)

Theorem static_abort_stack_option_none_normal_execution:
  asm_block_at p s.as_pc
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"] /\
  s.as_stack = x::y::z::xs ==>
  stack_peephole_opts [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"] = NONE /\
  (?out. asm_steps lo op p 3 s = AsmOK out /\
    out.as_pc = s.as_pc + 3 /\ out.as_stack = y::x::z::xs /\
    out.as_requests = s.as_requests) /\
  ~(?out. asm_steps lo op p 3 s = AsmRevert out \/
           asm_steps lo op p 3 s = AsmFault out) /\
  ~(?msg. asm_steps lo op p 3 s = AsmError msg)
Proof
  strip_tac >> fs[asm_block_at_cons] >>
  `asm_steps lo op p 3 s =
    AsmOK (s with <|as_stack := y::x::z::xs; as_pc := s.as_pc + 3|>)` by
    (rewrite_tac[numLib.num_CONV ``3:num``, numLib.num_CONV ``2:num``,
                 numLib.num_CONV ``1:num``] >>
     simp[asm_steps_def,
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `1`] asm_step_swap_ok),
       SRULE [swap_name_def] (Q.SPECL [`lo`, `op`, `2`] asm_step_swap_ok),
       asm_next_def, LUPDATE_compute, ADD_ASSOC]) >>
  simp[asm_opt_peephole_swap_pair_then_swap1_at_end]
QED

(* Syntactic recognizers are not opcode validity certificates: the real
   table ranges are SWAP1..16, and only the uppercase concrete commutative
   names ADD/MUL/EQ/AND/OR/XOR have the required arithmetic behavior.
   In particular the optimizer's extra NE and lowercased names are not a
   license to transport pending concrete execution without a validity check. *)

Theorem static_abort_stack_recognizer_validity_boundary:
  asm_swap_op (AsmOp "SWAP17") /\
  ALOOKUP swap_table "SWAP17" = NONE /\
  asm_commutative_op (AsmOp "NE") /\ evm_opcode_byte "NE" = NONE /\
  asm_commutative_op (AsmOp "add") /\ evm_opcode_byte "add" = NONE
Proof
  EVAL_TAC
QED
