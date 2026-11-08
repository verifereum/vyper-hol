Theory bodyPtrBytestringBuiltinsAllocationEntry
Ancestors
  bodyPtrBytestringBuiltinsBuffer fragExec ptrDiscipline venomExecSemantics
  venomInst venomState compileEnv words

(* Project the allocation implementation's witnesses to the continuation entry.
   The ambient embedding is split, never replaced by an erased execution. *)
Theorem slice_allocation_continuation_entry:
  compile_slice_out_buf n sa = ((root,data),sb) /\
  cs_extends sb sx /\ fn_has_code sa sx fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ 32 <= n /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  fn_has_code sb sx fn /\
  ?G2 tn2 t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t) /\
    stmt_state_rel ctx fn cenv cx es t /\
    (!w. eval_operand (Lit w) t = SOME w /\
         op_prov G2 (Lit w) = NONE /\ op_taint tn2 (Lit w) = {})
Proof
  strip_tac >>
  `cs_extends sa sb` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  drule_all fn_has_code_split >> strip_tac >> simp[] >>
  drule_all compile_slice_out_buf_counted >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[eval_operand_def, op_prov_def, op_taint_def]
QED
