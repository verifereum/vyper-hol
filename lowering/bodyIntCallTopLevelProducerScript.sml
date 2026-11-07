(* Top-level immutable roots retain their identity on the selected run. *)
Theory bodyIntCallTopLevelProducer
Ancestors
  bodyIntCallProvenanceIntro exprSimTopLevelImmutable exprSimTopLevel
  bodyIntCallProducerInterface bodyIntCallPathLayout exprSimHypsDefs
  exprSimDefs loweringPosts gasOutcome gasSummary vyperInterpreter vyperState
  venomState context

Theorem toplevel_immutable_provenance:
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  off + type_memory_size tv < dimword (:256) ==>
  intcall_vv_provenance cenv cx ann sa sb es
    (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s
Proof
  strip_tac >> gvs[] >>
  simp[intcall_vv_provenance_def, mk_ptr_def, eval_operand_def] >>
  qexistsl_tac [`id`,`off`,`tv`,`v`,`0`,`v`] >>
  simp[sub_layout_def, read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, bind_def,
       return_def, evaluate_subscripts_def, lift_sum_def]
QED

Theorem compile_toplevel_immutable_provenance:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  compile_expr cenv ty (TopLevelName ann (src,id)) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (TopLevelName ann (src,id))) (es,s0)
    (\res ee s. ?raw. res = INL raw /\
      vv_post ctx func cenv cx (TopLevelName ann (src,id)) es sa sb s0 ee raw vv s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx ann sa sb ee raw vv s)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all toplevel_immutable_lookup >> strip_tac >>
  drule compile_toplevel_immutable_ptr >>
  disch_then (qspecl_then [`ty`,`sa`,`ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`,`es`,`OK s0`] >>
  conj_tac >- (irule toplevel_immutable_marked_exec >> simp[] >> metis_tac[]) >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule toplevel_immutable_post >> simp[] >> metis_tac[]) >>
  irule toplevel_immutable_provenance >> simp[] >> metis_tac[]
QED

Theorem compile_toplevel_storage_provenance:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  compile_expr cenv ty (TopLevelName ann (src,id)) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (TopLevelName ann (src,id))) (es,s0)
    (\res ee s. ?raw. res = INL raw /\
      vv_post ctx func cenv cx (TopLevelName ann (src,id)) es sa sb s0 ee raw vv s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx ann sa sb ee raw vv s)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src,id)) es` by
    metis_tac[compile_toplevel_name_sim, expr_vv_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >> disch_then drule_all >>
  Cases_on `tr` >>
  gvs[exprLoweringTheory.compile_expr_def, vyperASTTheory.expr_type_def,
      intcall_vv_provenance_def, mk_ptr_def]
QED

Theorem compile_toplevel_name_provenance:
  expr_sim_pre cenv cx env (TopLevelName ann nsid) es /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (TopLevelName ann nsid)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (TopLevelName ann nsid)) (es,s0)
    (\res ee s. ?raw. res = INL raw /\
      vv_post ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee raw vv s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx ann sa sb ee raw vv s)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> PairCases_on `nsid` >> rename1 `TopLevelName ann (src,id)` >>
  Cases_on `get_module_code cx src`
  >- metis_tac[exprSimTopLevelPropsTheory.missing_module_not_gas_admissible] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule compile_toplevel_immutable_provenance >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  drule_all exprSimTopLevelPropsTheory.admissible_toplevel_storage_lookup >> strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  irule compile_toplevel_storage_provenance >> simp[] >> metis_tac[]
QED
