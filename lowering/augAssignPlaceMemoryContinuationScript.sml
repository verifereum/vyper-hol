(* Counted target traversal with a caller-supplied continuation. *)
Theory augAssignPlaceMemoryContinuation
Ancestors
  augAssignPlaceMemoryTarget augAssignPlaceRhsMemory
  augAssignPlaceWordStoreMemory bodyAugAssignOther gasSummary
  targetPlaceSimMem stmtSimAugAssignPlaceMemory stmtSimAugAssignPlaceStorage
  vyperInterpreter gasOutcome targetPlaceSimDefs
  gasContext targetPlaceSimCases vyperState
Libs
  pairLib

Theorem aug_place_target_mem_continuation:
  target_sim_mem ctx func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p mid t marks.
    target_post ctx func cenv cx es sa sp s0 mid (PlaceR p) (Type ty) r t /\
    t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL p, mid with gas_obs := tail)) /\
    gas_marked_path T ctx func s0 (LENGTH marks) (OK t) ==>
    gas_outcome T (cx_tops cx) (ctx,func) ((k p) : evaluation_state -> 'a evaluation_result) (mid,t) Q R) /\
  (!res ee rr. expr_exit (res : eval_result + exception) rr ==> ?ex. res = INR ex /\ R (INR ex) ee rr) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx bt) k) (es,s0) Q R
Proof
  strip_tac >>
  `eval_target_place cx bt = bind (eval_base_place cx bt) get_place` by
    (simp[Once evaluate_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ target_place_res_ok _` mp_tac >>
     asm_rewrite_tac[] >>
     rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `gs` mp_tac) >>
     Cases_on `res` >> simp[bind_def, target_res_ok_def] >>
     simp[target_place_res_ok_def]) >>
  qpat_x_assum `target_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_mem_def]) >>
  disch_then (qspecl_then [`Type ty`, `sa`, `sp`, `r`, `s0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rewrite_tac[aug_place_target_bind_base] >>
  drule aug_place_result_bind_outcome_path >>
  disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `?p. v = PlaceR p` by
    (qpat_x_assum `gas_admissible _ target_place_res_ok _` mp_tac >>
     rewrite_tac[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     asm_rewrite_tac[] >> simp[bind_def] >> strip_tac >>
     Cases_on `v` >>
     gvs[get_place_def, raise_def, target_place_res_ok_def]) >>
  gvs[] >> simp[get_place_def, bind_return] >>
  first_x_assum irule >> simp[] >> qexists_tac `marks` >>
  simp[bind_def, get_place_def, return_def]
QED
