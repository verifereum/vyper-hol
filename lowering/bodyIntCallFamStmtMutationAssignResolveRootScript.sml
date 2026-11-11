(* No-code roots of the resource-carrying assignment-place resolver. *)
Theory bodyIntCallFamStmtMutationAssignResolveRoot
Ancestors
  bodyIntCallJointContract targetPlaceSimCases bodyIntCallJointCallCore
  bodyIntCallFamAggStructFields exprSimHypsDefs exprLowering compileEnv
  vyperTypeEnv vyperState gasOutcome gasSummary fragGasMode fragGasPathMem
  loweringPosts targetPlaceSimDefs

Theorem intcall_target_name_resolve:
  type_place_target env (NameTarget id) = SOME vt /\
  compile_get_target_ptr compile_expr ce (NameTarget id) sa = (r,sb) /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_base_place fp.jc_cx (NameTarget id)) (es,s)
    (\res ee u. ?pv. res = INL pv /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee pv vt r u /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee result. expr_exit res result)
Proof
  strip_tac >>
  gvs[vyperTypeEnvTheory.type_place_target_NameTarget] >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_expr_res_def] >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  gvs[compile_get_target_ptr_def, comp_return_def] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, Once vyperInterpreterTheory.evaluate_def,
       get_scopes_def, type_check_def, assert_def, bind_def, return_def] >>
  simp[ignore_bind_def, assert_def, bind_def, return_def] >>
  conj_tac
  >- (irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  simp[intcall_expr_cont_def] >>
  fs[target_post_def, intcall_expr_res_def, place_ptr_rel_def,
     place_readable_def] >>
  `ce.ce_var_type id = SOME ty /\
   evaluate_type (get_tenv fp.jc_cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
              vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
  `?w. lookup_var p s = SOME w` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
              local_ptrs_rel_def] >>
  simp[value_type_place_def, venomStateTheory.eval_operand_def,
       mem_path_offset_def, wordsTheory.WORD_ADD_0] >>
  conj_tac >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[read_place_def, get_scopes_def, lift_option_type_def, bind_def,
       return_def, read_memory_path_def, lift_sum_def, evaluate_subscripts_def]
QED
