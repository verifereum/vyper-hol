(* Memory case of the body induction (bodyMemory's body_mem_mutual): pop on a
   nested target. *)
Theory bodyMemPopNested
Ancestors
  bodyMemoryPreds popNestedTargetMemory popNestedLocalMemory popNestedStorageMemory
  vyperImmutableAccessFrame
  bodyExprForceMemory exprSimPopNested popTargetPre gasContext
  bodySim exprSimHypsDefs targetPlaceSim exprSimPopNestedBase
  vyperTypeAssignContext vyperTypeCallGraph exprLowering

Theorem body_pop_nested_mem_case:
  !cx v10 bt.
    (!id. bt <> NameTarget id) /\ (!nid. bt <> TopLevelNameTarget nid) /\
    body_base_target_mem_ok cx bt ==>
    body_expr_mem_ok cx (Pop v10 bt)
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac body_expr_mem_ok_intro >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
  gvs[] >>
  `expr_vv_sim_mem ctx func cenv cx ty (Pop v10 bt) es` by
    suspend "value" >>
  simp[] >> irule body_expr_sim_mem_of_vv_sim_mem >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> simp[nested_pop_compile_eq, LET_THM] >>
      rpt (pairarg_tac >> gvs[])) >>
  qexists_tac `env` >> simp[]
QED

Resume body_pop_nested_mem_case[value]:
  qspec_then `bt` strip_assume_tac target_root_cases
  >- suspend "local" >>
  Cases_on `?ts d. get_module_code cx src = SOME ts /\
                   find_var_decl_by_name id ts = SOME d`
  >- (gvs[] >> suspend "storage") >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  metis_tac[pop_immutable_root_rejected]
QED

Resume body_pop_nested_mem_case[local]:
  `~immutable_root cx bt` by fs[immutable_root_def] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_of_pop] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT v10 (Dynamic n)))` by
    metis_tac[expr_body_pre_def, well_typed_expr_Pop_dynamic_target] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    fs[expr_body_pre_def, int_calls_expr_def] >>
  `target_sim_mem ctx func cenv cx env bt es` by
    (irule pop_nested_local_target_mem >> metis_tac[]) >>
  irule pop_nested_local_sim_mem >> metis_tac[]
QED

Resume body_pop_nested_mem_case[storage]:
  `~immutable_root cx bt` by fs[immutable_root_def] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_of_pop] >>
  `target_sim_mem ctx func cenv cx env bt es` by
    (irule pop_nested_storage_target_mem >> metis_tac[]) >>
  irule pop_nested_storage_sim_mem >> metis_tac[]
QED

Finalise body_pop_nested_mem_case
