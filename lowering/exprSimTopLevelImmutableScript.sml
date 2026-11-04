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

Theorem compile_toplevel_immutable_sim:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  `env_consistent env cx es /\ state_well_typed es /\
   well_typed_expr env (TopLevelName ann (src,id))` by
    fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_find_NONE_bare_global >> strip_tac >>
  `src = cenv.ce_module /\
   ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
         !tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
              off + type_memory_size tv < dimword (:256)` by
    (fs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >> lookup_global_tac >>
  simp[get_immutables_def, get_address_immutables_def, lift_option_type_def,
       bind_def, return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables cenv.ce_module imms) id` >>
  simp[return_def, raise_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  rename1 `FLOOKUP _ id = SOME tvv` >> PairCases_on `tvv` >>
  strip_tac >> gvs[] >>
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
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_def, vyperASTTheory.expr_type_def] >>
  strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, immutable_holds_def,
       contextTheory.mk_ptr_def, eval_operand_def,
       vyperASTTheory.expr_type_def] >>
  qexistsl [`id`, `off`, `tvv0`, `tvv1`, `0`] >>
  simp[sub_layout_def, read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, bind_def,
       return_def, evaluate_subscripts_def, lift_sum_def]
QED
