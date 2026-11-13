(* Final counted continuation, after both operand posts are established. *)
Theory exprSimExtract32Tail
Ancestors
  exprSimHashBoundary
  exprSimExtract32Assembly exprSimExtract32Post exprSimExtract32Value
  exprSimHash exprSimVVFrame exprSimDefs loweringPosts gasOutcome gasSummary
  vyperState vyperContext vyperAST vyperTypeSystem valueEncoding
  exprLoweringProps compileEnv builtinBytes words list finite_map venomState fragExec

Theorem extract32_tail_ready:
  expr_post ctx func cenv cx src es sa sm s0 es1 (BytesV bs) src_op s1 /\
  expr_post ctx func cenv cx off es1 sm st3 s1 es2 (IntV i) off_op s2 /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv st3 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= st3.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
              BytesT (Fixed k) => k <= 32 | _ => T) /\
  is_word_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s2.vs_memory /\
  LENGTH bs < dimword (:256) /\ Num i < dimword (:256) /\
  p + 32 + LENGTH bs < dimword (:256) /\
  eval_operand len s2 = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s2 = SOME (n2w (p + 32)) /\
  eval_operand off_op s2 = SOME (n2w (Num i)) /\ fresh_vars_wrt st3 s2 /\
  compile_extract32_load len dp off_op st3 = (raw,st4) /\
  compile_clamp_basetype raw (BaseT bt) st4 = (op,sb) /\
  fn_has_code st3 sb func /\ es2.gas_obs = [] /\
  ~s2.vs_halted /\ s2.vs_current_bb = st3.cs_current_bb /\
  s2.vs_inst_idx = LENGTH st3.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
       [expr_type src;expr_type off] [BytesV bs;IntV i])) (\v. return (Value v)))
    (es2,s2)
    (\res ee t. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])
        es sa sb s0 ee (Value v) (StackValue ty op) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> simp[evaluate_type_builtin_def] >>
  Cases_on `evaluate_extract32 bs (Num i) bt`
  >- suspend "success" >>
  suspend "error"
QED

Resume extract32_tail_ready[success]:
  drule_all extract32_tail_success_marked >>
  disch_then (qspec_then `es2` (qspec_then `ctx` strip_assume_tac)) >>
  `stmt_state_rel ctx func cenv cx es2 u` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`s2`,`st3`] >>
     gvs[expr_post_def]) >>
  `u.vs_memory = s2.vs_memory /\ u.vs_allocas = s2.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!z w. not_fresh_at st3 z /\ lookup_var z s2 = SOME w ==>
     lookup_var z u = SOME w` by metis_tac[] >>
  `vv_post ctx func cenv cx (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])
     es sa sb s0 es2 (Value x) (StackValue ty op) u` by
    (drule_all extract32_posts_to_vv_post_frame >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value x)`, `es2`,
    `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[gas_marked_exec_def, lift_sum_def, bind_def, return_def] >>
  fs[gas_marked_exec_def] >>
  `es2 with gas_obs := [] = es2` by simp[evaluation_state_component_equality] >>
  simp[]
QED

Resume extract32_tail_ready[error]:
  `?msg. y = RuntimeError msg` by
    (irule extract32_error_runtime >> goal_assum (drule_at Any) >>
     Cases_on `bt` >> gvs[]) >> gvs[] >>
  `LENGTH bs < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256)` by
    decide_tac >>
  drule_all extract32_tail_error_marked >>
  disch_then (qspec_then `es2` (qspec_then `ctx` strip_assume_tac)) >>
  rename1 `gas_marked_exec _ _ _ _ (REPLICATE ticks F) _ _ _` >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `REPLICATE ticks F` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `es2`,
    `Abort Revert_abort (u with vs_inst_idx := j)`] >>
  gvs[gas_marked_exec_def, lift_sum_def, bind_def, raise_def,
      expr_exit_def, exit_result_def]
QED

Finalise extract32_tail_ready
