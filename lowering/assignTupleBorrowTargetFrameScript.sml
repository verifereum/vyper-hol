Theory assignTupleBorrowTargetFrame
Ancestors
  assignTupleResidualSnapshot bodyPtrPopTargetSimCurrentLocal
  bodySimAugPlaceScopes supportedStmts supportedExprs
  vyperInterpreter vyperState vyperPlaceStatePreservation
  vyperScopePreservation vyperPlaceFrames

Theorem supported_target_scopes_frame:
  !bt tops bindings cx es res ee.
    supported_target tops bindings bt /\
    eval_base_place cx bt es = (res,ee) ==> ee.scopes = es.scopes
Proof
  Cases_on `bt` >> simp[supported_target_def] >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >>~- ([`eval_base_place _ (TopLevelNameTarget _) _ = _`],
      rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >~ [`eval_base_place _ (SubscriptTarget _ _) _ = _`]
  >- (rename1 `eval_base_place cx (SubscriptTarget inner key) es = _` >>
      Cases_on `inner` >> gvs[] >>
      rename1 `eval_base_place cx (SubscriptTarget (TopLevelNameTarget nsid) key) es = _` >>
      PairCases_on `nsid` >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      imp_res_tac lookup_global_scopes >> imp_res_tac read_result_state >>
      imp_res_tac extend_place_state >> gvs[] >>
      metis_tac[aug_place_supported_expr_scopes]) >>
  rename1 `eval_base_place cx (AttributeTarget inner fname) es = _` >>
  Cases_on `inner` >> gvs[] >>
  rename1 `eval_base_place cx (AttributeTarget (TopLevelNameTarget nsid) fname) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_scopes >> imp_res_tac extend_place_state >> gvs[]
QED

(* The path identifies the saved value, including any dynamic-array length words. *)
Theorem tuple_borrowed_value_target_frame_ptr:
  target_post ctx func cenv cx es sa sb s ee pv vt r t /\
  ghost_kept cenv es sa G tn s G' tn' /\
  supported_target tops bindings bt /\
  eval_base_place cx bt es = (res,ee) /\
  expr_sim_inv cenv cx env ee /\ ghost_inv d cenv cx ee G' tn' t /\
  FLOOKUP env.var_types id = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME root_tv /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME bw /\ not_fresh_at sa p /\
  mem_path_offset root_tv path = SOME (off,tv) /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ptr_val_ok cx ty v op G tn s /\
  eval_operand op s = SOME w /\ w2n w = w2n bw + off /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) ==>
  ptr_val_ok cx ty v op G' tn' t
Proof
  strip_tac >>
  `ee.scopes = es.scopes` by metis_tac[supported_target_scopes_frame] >>
  `eval_operand op t = SOME w` by
    metis_tac[tuplePlaceSnapshotTheory.tuple_place_target_operand] >>
  `lookup_var p t = SOME bw` by
    (`eval_operand (Var p) t = SOME bw` suffices_by
       simp[venomStateTheory.eval_operand_def] >>
     irule tuplePlaceSnapshotTheory.tuple_place_target_operand >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `lookup_scopes id ee.scopes = SOME entry` by simp[] >>
  `ISL (evaluate_subscripts entry.type entry.value path)` by simp[] >>
  drule_all target_current_local_path_ptr >> strip_tac >>
  gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
  conj_tac
  >- (Cases_on `op` >> gvs[bodyPtrDefsTheory.ghost_kept_def,
                         ptrDisciplineTheory.op_taint_def]) >>
  conj_tac
  >- (Cases_on `op` >> gvs[bodyPtrDefsTheory.ghost_kept_def,
                         ptrDisciplineTheory.op_prov_def]) >>
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  gvs[bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]
QED
