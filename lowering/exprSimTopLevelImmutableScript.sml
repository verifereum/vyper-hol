(* Counted top-level name simulation: immutable. *)
Theory exprSimTopLevelImmutable
Ancestors
  exprSimTopLevelProps exprSimMemorySource
  exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv
  vyperTypeInvariants vyperTypeGlobalLookupSoundness vyperTyping
  vyperValueOperation valueEncoding fragExec venomState
  vyperStorageLayoutSafety vyperLookupStorage

val lookup_global_tac =
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM];

Theorem toplevel_immutable_lookup:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es ==>
  src = cenv.ce_module /\
  ?off imms tv v.
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
    evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
    off + type_memory_size tv < dimword (:256)
Proof
  strip_tac >>
  `env_consistent env cx es /\ state_well_typed es /\
   well_typed_expr env (TopLevelName ann (src,id))` by
    fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_find_NONE_bare_global >> strip_tac >>
  `src = cenv.ce_module /\
   ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
         !tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
              off + type_memory_size tv < dimword (:256)` by
    (fs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >>
  simp[] >> lookup_global_tac >>
  fs[get_immutables_def, get_address_immutables_def, lift_option_type_def,
       bind_def, return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def, expr_vv_res_ok_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables cenv.ce_module imms) id` >>
  simp[return_def, raise_def, expr_vv_res_ok_def] >>
  rename1 `FLOOKUP _ id = SOME tvv` >> PairCases_on `tvv` >>
  `evaluate_type (get_tenv cx) ann = SOME tvv0` by
    (fs[env_consistent_def, env_immutables_consistent_def] >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  `value_has_type tvv0 tvv1` by
    (fs[state_well_typed_def, EVERY_MEM] >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >> first_x_assum drule >>
     simp[imms_well_typed_def] >>
     qpat_x_assum `FLOOKUP _ _ = SOME _` mp_tac >>
     simp[get_source_immutables_def] >> CASE_TAC >> simp[] >>
     metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem compile_toplevel_immutable_ptr:
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==>
  compile_expr cenv ty (TopLevelName ann (src,id)) sa =
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),sa)
Proof
  simp[compile_expr_def, comp_return_def, vyperASTTheory.expr_type_def]
QED

Theorem toplevel_immutable_marked_exec:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\ ~s0.vs_halted ==>
  gas_marked_exec F (ctx,func) (eval_expr cx (TopLevelName ann (src,id)))
    (es,s0) [] (INL (PlaceR (ImmutablePlace src id []))) es (OK s0)
Proof
  strip_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules] >>
  lookup_global_tac >>
  fs[get_immutables_def, get_address_immutables_def, lift_option_type_def,
     bind_def, return_def, raise_def]
QED

Theorem toplevel_immutable_post:
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  off + type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s0 ==>
  vv_post ctx func cenv cx (TopLevelName ann (src,id)) es sa sa s0
    (es with gas_obs := []) (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s0
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, immutable_holds_def,
       contextTheory.mk_ptr_def, eval_operand_def, locals_kept_mem,
       vyperASTTheory.expr_type_def] >>
  qexistsl_tac [`id`, `off`, `tv`, `v`, `0`] >>
  fs[sub_layout_def, read_result_def, read_place_def, get_immutables_def,
     get_address_immutables_def, lift_option_type_def, bind_def,
     return_def, evaluate_subscripts_def, lift_sum_def] >>
  qexists_tac `v` >> gvs[return_def]
QED

Theorem compile_toplevel_immutable_sim:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  drule_all toplevel_immutable_lookup >> strip_tac >>
  drule compile_toplevel_immutable_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`, `es`, `OK s0`] >>
  conj_tac >- (irule toplevel_immutable_marked_exec >> simp[] >> metis_tac[]) >>
  disj1_tac >> simp[] >> irule toplevel_immutable_post >> simp[] >> metis_tac[]
QED

