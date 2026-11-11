(* Enriched local-name production on the actual empty marked execution. *)
Theory bodyIntCallProducerRoots
Ancestors
  bodyIntCallProducerInterface exprSimNameValue exprSimHypsDefs
  exprSimProps exprSimDefs loweringPosts localPtrsProps
  compileEnv exprLowering exprLoweringProps vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperInterpreter vyperState venomState context
  valueEncoding valueEncodingProofs finite_map gasOutcome gasSummary

Theorem name_value_provenance:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  value_has_type entry.type entry.value /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME ann /\
  stmt_state_rel ctx func cenv cx es s0 ==>
  intcall_vv_provenance cenv cx ann sa sa es
    (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory)) s0
Proof
  strip_tac >> simp[intcall_vv_provenance_def, mk_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  `v = entry.value` by
    (gvs[read_result_def, read_place_def, read_memory_path_def,
         get_scopes_def, bind_def, lift_option_type_def, lift_sum_def,
         return_def, raise_def, evaluate_subscripts_def]) >>
  gvs[] >>
  `?base. lookup_var p s0 = SOME base /\ type_memory_size entry.type <= sz /\
          val_wf entry.type entry.value` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  rename1 `lookup_var p s0 = SOME root_word` >>
  qexists_tac `root_word` >> simp[eval_operand_def] >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`id`,`sz`,`entry`,`p`,`root_word`,`0`] >>
  simp[local_region_def, sub_layout_def] >>
  drule val_footprint_le >> simp[]
QED

Theorem compile_name_value_provenance:
  expr_sim_pre cenv cx env (Name ann id) es /\
  compile_expr cenv ty (Name ann id) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (Name ann id)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Name ann id)) (es,s0)
    (\res ee s. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (Name ann id) es sa sb s0 ee tv vv s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx ann sa sb ee tv vv s)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`,`sa`,`ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`,`es`,`OK s0`] >>
  conj_tac >- (irule name_value_marked_exec >> simp[]) >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule name_value_post >> simp[]) >>
  irule name_value_provenance >> simp[] >>
  goal_assum (drule_at Any)
QED
