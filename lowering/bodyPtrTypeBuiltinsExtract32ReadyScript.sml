Theory bodyPtrTypeBuiltinsExtract32Ready
Ancestors
  bodyPtrTypeBuiltinsExtract32Assembly bodyPtrTypeBuiltinsExtract32Suffix
  exprSimExtract32Run exprSimExtract32Post exprSimExtract32Read
  bodyPtrDefs loweringPosts compileEnv exprLoweringProps exprLowering
  exprSimDefs vyperState vyperContext vyperAST vyperTypeSystem
  valueEncoding words list finite_map fragExec gasSummaryComposePtr venomState

Theorem extract32_tail_ptr_ready:
  expr_post ctx func cenv cx src es sa sm s0 es1 (BytesV bs) srcop s1 /\
  expr_post ctx func cenv cx off es1 sm sc s1 ee (IntV i) offop s /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME (BaseTV bt) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) srcop G tn s /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand srcop s = SOME (n2w p) /\
  LENGTH bs < dimword(:256) /\ Num i < dimword(:256) /\
  p+32+LENGTH bs < dimword(:256) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  eval_operand offop s = SOME (n2w (Num i)) /\
  not_fresh_at sc len /\ not_fresh_at sc data /\
  (!z. offop = Var z ==> not_fresh_at sc z) /\ (!l. offop <> Label l) /\
  op_prov G offop = NONE /\ op_taint tn offop = {} /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G tn data s span) /\
  compile_extract32_load (Var len) (Var data) offop sc = (raw,sd) /\
  compile_clamp_basetype raw (BaseT bt) sd = (op,se) /\
  fn_has_code sc se func /\ ee.gas_obs = [] /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (vyperState$bind (lift_sum (evaluate_extract32 bs (Num i) bt)) (\v. return (Value v)))
    (ee,s,G,tn)
    (\res ef H th t. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx (TypeBuiltin ann Extract32 (BaseT bt) [src;off])
        es sa se s0 ef (Value v) (StackValue ty op) t /\
      t.vs_current_bb = se.cs_current_bb /\ t.vs_inst_idx = LENGTH se.cs_current_insts /\
      ghost_inv d cenv cx ef H th t /\
      ptr_vv_ok cx (post_value_type cenv (TypeBuiltin ann Extract32 (BaseT bt) [src;off]))
        (Value v) (StackValue ty op) ef H th t /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res ef gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all extract32_tail_ready_certificate >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  `!z. Var len = Var z \/ Var data = Var z \/ offop = Var z ==>
       not_fresh_at sc z` by (simp[] >> metis_tac[]) >>
  drule_all extract32_tail_run_any >> strip_tac >>
  irule extract32_tail_outcome_of_runs_ptr >>
  qpat_assum `compile_extract32_load _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_clamp_basetype _ _ _ = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`th`,`H`] >> reverse conj_tac
  >- (`s with vs_inst_idx := s.vs_inst_idx = s` by simp[venom_state_component_equality] >>
      qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >> metis_tac[]) >>
  Cases_on `evaluate_extract32 bs (Num i) bt`
  >- suspend "success" >> gvs[] >> metis_tac[]
QED

Resume extract32_tail_ptr_ready[success]:
  gvs[] >> suspend "endpoint"
QED

Resume extract32_tail_ptr_ready[endpoint]:
  conj_tac
  >- (irule extract32_tail_post_of_run >>
      qpat_assum `expr_post _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all extract32_tail_run_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  simp[] >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `ghost_inv d cenv cx ee H th (t with vs_inst_idx := LENGTH se.cs_current_insts) /\
   ghost_kept cenv es sa G0 tn0 s0 H th` by
    (irule extract32_tail_ghost_frame >>
     qpat_assum `compile_extract32_load _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_clamp_basetype _ _ _ = _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, expr_type_def, read_result_def, return_def]
QED

Finalise extract32_tail_ptr_ready
