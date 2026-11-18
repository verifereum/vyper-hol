(* Revert-forward boundary diagnostic. No source/concrete memory agreement
   or static call-context premise is used in the pending execution below. *)
Theory staticAbortGeneratedRevertProbe
Ancestors
  fnFrameStepsRevertForwardDeep staticAbortTrace staticAbortStraight
  stackOpAsmSim asmSem stackOpSim words list arithmetic planExec asmIR

(* The E0013 exception predicate includes empty returndata. Unlike a static
   fault or the ASSERT postamble, a generated forwarded REVERT need not
   satisfy that observation. This is a diagnostic, not a counterexample
   to the frozen supplier, which observes only exception and requests. *)
Theorem generated_revert_pending_observation_probe:
  asm_block_at prog s.as_pc [AsmOp "REVERT"] /\
  2 <= LENGTH s.as_stack ==>
  ?t. asm_steps lo o2pc prog 1 s = AsmRevert t /\
      t.as_requests = s.as_requests
Proof
  strip_tac >>
  `s.as_pc < LENGTH prog /\ EL s.as_pc prog = AsmOp "REVERT"` by
    fs[asm_block_at_cons] >>
  Cases_on `s.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rewrite_tac[numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_revert, asm_revert_op_def]
QED

Theorem generated_revert_nonempty_payload_excludes_static_exception:
  asm_block_at prog s.as_pc [AsmOp "REVERT"] /\
  s.as_stack = [0w;1w] /\ s.as_memory = [7w] ==>
  ~(?n t. static_abort_exception lo o2pc prog n s t)
Proof
  strip_tac >>
  `s.as_pc < LENGTH prog /\ EL s.as_pc prog = AsmOp "REVERT"` by
    fs[asm_block_at_cons] >>
  simp[static_abort_exception_def] >>
  Cases_on `n` >>
  simp[asm_steps_def, asm_step_revert, asm_revert_op_def,
       asm_expand_memory_def]
QED

(* ABANDONED OPTIONAL SAMPLE (nonexecuting failed proof, retained under G0001).
   The sample below has not been proved and is not exported.

(* This is the no-spill template exposed by rf_probe_plan (and by
   rf_probe_assign_plan). It is not a general generated-certificate
   realization: in particular rf_probe_assign_fn is not codegen_ready_fn.
   All memory and operand words in this local placed window are arbitrary. *)
Theorem generated_revert_template_pending_progress:
  asm_block_at prog s.as_pc
    (execute_plan fmp [SOPush (Lit 1w); SOPush (Lit 0w);
      SOSwap 1; SOSwap 2; SOEmit "RETURNDATACOPY";
      SOPush (Lit 1w); SOSwap 1; SOEmit "REVERT"]) /\
  s.as_stack = a::b::rest ==>
  ?t. (asm_steps lo o2pc prog 8 s = AsmRevert t \/
       asm_steps lo o2pc prog 8 s = AsmFault t) /\
      t.as_requests = s.as_requests
Proof
  simp[execute_plan_def, exec_stack_op_def, encode_num_bytes_fuel_def,
       asm_block_at_cons] >> strip_tac >>
  `!u. asm_step lo o2pc (AsmOp "SWAP1") u = asm_swap 1 u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_swap``])) >> simp[]) >>
  `!u. asm_step lo o2pc (AsmOp "SWAP2") u = asm_swap 2 u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_swap``])) >> simp[]) >>
  `!u. asm_step lo o2pc (AsmOp "RETURNDATACOPY") u = asm_returndatacopy u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_returndatacopy``])) >> simp[]) >>
  `word_of_bytes F 0w (REVERSE (encode_num_bytes_fuel 32 0)) = (0w:bytes32) /\
   word_of_bytes F 0w (REVERSE (encode_num_bytes_fuel 32 1)) = (1w:bytes32)` by EVAL_TAC >>
  gvs[swap_name_def] >>
  rewrite_tac[numLib.num_CONV ``8:num``, numLib.num_CONV ``7:num``,
    numLib.num_CONV ``6:num``, numLib.num_CONV ``5:num``,
    numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
    numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_push_ok, asm_next_def,
       asm_swap_def, asm_returndatacopy_def,
       asm_step_revert, asm_revert_op_def] >>
  FAIL_TAC "universal pending template probe"
QED
*)
