Theory assignEffectfulIndexEmpty
Ancestors
  assignPlaceEmptyStore stmtSimAugAssignPlaceMemory stmtSimDeclMem
  loweringPosts exprLoweringProps stmtLowering compileEnv exprOperandVar
  vyperState vyperPlaceFrames stmtSimAssignStorage
  gasOutcome gasSummary fragGasMode loweringStateRelDefs stmtSimDeclCompose

Theorem assign_effectful_empty_target_store:
  target_post ctx func cenv cx es sa st s0 mid (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ has_length_word dty /\
  compile_store_at_loc cenv.ce_imm_alloca dst (Lit 0w) (SOME loc) st = ((),sb) /\
  write_place cx p (default_value dtv) mid = (INL (),ff) /\
  expr_sim_inv cenv cx env mid /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv st /\ storage_place_region cx p /\
  (!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id mid.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  loc <> LocCode /\ loc <> LocCalldata /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_frame cenv es sa s0 cenv mid s /\ ci_mono sa st /\
  ~block_is_terminated st ==>
  gas_outcome F (cx_tops cx) (ctx,func) (write_place cx p (default_value dtv))
    (mid,s)
    (\res ee u. !tail. stmt_post ctx func cx lctx cenv cenv sa sb es s0
       res (ee with gas_obs := tail) u)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `?w. eval_operand dst s = SOME w /\
       place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty)` by
    gvs[target_post_def] >>
  `!x. dst = Var x ==> not_fresh_at st x` by gvs[target_post_def] >>
  `stmt_state_rel ctx func cenv cx mid s` by gvs[target_post_def] >>
  drule_all assign_place_empty_store_framed >> strip_tac >>
  `!tail. write_place cx p (default_value dtv) (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)` by
    (Cases_on `p`
     >- (qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
         simp[write_place_def, write_storage_slot_gas_obs, AllCaseEqs()] >>
         rpt strip_tac >> gvs[])
     >- (drule aug_place_memory_write_gas_obs >> simp[]) >>
     fs[place_ptr_rel_def]) >>
  `stmt_post ctx func cx lctx cenv cenv sa sb es s0 (INL ()) ff t` by
    (irule aug_place_normal_post >> simp[] >>
     conj_tac
     >- (fs[target_post_def] >> metis_tac[compiler_ci_mono_not_fresh]) >>
     conj_tac >- (fs[target_post_def] >> metis_tac[]) >>
     Cases_on `loc` >> gvs[compile_store_at_loc_def] >>
     irule emit_void_nonterminator_open >> goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`, `ff`, `OK t`] >> simp[stmt_post_end_gas_obs]
QED
