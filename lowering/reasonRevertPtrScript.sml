(* Shared checked terminal edge for reason encoders. *)
Theory reasonRevertPtr
Ancestors
  reasonEncoderTailPtr reasonTupleCopyPtr stmtAbortPtr ptrSafeRun ptrDiscipline bodyPtrDefs
  venomExecSemantics venomInst venomState emitHelperProps
  fragGasPathPtr contextCodegenRel codegenRel finite_map memLocDefs

Theorem ptr_inst_ok_reason_revert:
  ptr_covers G tn src s (w2n szw) /\
  eval_operand szw_op s = SOME szw /\ op_taint tn szw_op = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn
    (mk_inst id REVERT [Var src;szw_op] []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, memory_range_of_operands_def,
       eval_operand_def, about_to_revert_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[eval_operand_def] >> metis_tac[]
QED

Theorem reason_emit_revert_path_ptr:
  emit_inst REVERT [Var src;szw_op] [] sa = ((),sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ptr_covers G tn src s (w2n szw) /\
  eval_operand szw_op s = SOME szw /\ op_taint tn szw_op = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id REVERT [Var src;szw_op] []) s =
    Abort a t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >> irule emit_abort_zero_path_ptr >> simp[] >>
  qexistsl_tac [`REVERT`, `[Var src;szw_op]`, `sa`, `sb`] >> simp[] >>
  irule ptr_inst_ok_reason_revert >> metis_tac[]
QED

(* Final three instructions, independent of the original reason location. *)
Theorem reason_encoder_revert_path_ptr:
  emit_inst ADD [Var outer;Lit 28w] [start] sa = ((),c1) /\
  emit_inst ADD [Lit 4w;Var encoded] [len] c1 = ((),c2) /\
  emit_inst REVERT [Var start;Var len] [] c2 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var outer s = SOME a /\ ptr_covers G tn outer s capacity /\
  lookup_var encoded s = SOME n /\ op_taint tn (Var encoded) = {} /\
  28 + w2n (4w + n) <= capacity /\
  w2n a + 28 < dimword (:256) /\ encoded <> start /\ start <> len ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  strip_tac >>
  `w2n (28w : bytes32) = 28` by
    simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  qpat_assum `w2n (28w : bytes32) = 28` (fn th =>
    drule_all (SRULE [eval_operand_def, op_taint_def, th]
      (Q.INST [`offset` |-> `Lit 28w`, `d` |-> `28w`,
               `k` |-> `w2n (4w + n : bytes32)`] reason_encoder_offset_path_ptr))) >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand (Lit 4w) s1 = SOME 4w /\
   eval_operand (Var encoded) s1 = SOME n /\
   op_taint tn1 (Lit 4w) = {} /\ op_taint tn1 (Var encoded) = {}` by
    (fs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `ptr_covers G2 tn2 start s2 (w2n (4w + n))` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `?sf. step_inst_base (mk_inst c2.cs_next_id REVERT [Var start;Var len] []) s2 =
          Abort Revert_abort sf` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Var len) s2 = SOME (4w + n)` by simp[eval_operand_def] >>
  drule_all reason_emit_revert_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `sf`] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED
