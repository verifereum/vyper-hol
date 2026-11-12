Theory bodyPtrPopTargetSimIndexFrame
Ancestors
  bodyPtrPopTargetDefs bodyPtrDefs targetPlaceSimCasesBase
  loweringPosts exprSimProps compileEnv venomState ptrDiscipline
  augAssignPtrRhsFrame finite_map exprLowering compileEnv
  stmtSimAugAssignPlace targetPlaceSim

(* Slot-place classification is independent of runtime registers.  Only the
   saved operand's value and ghost classification need an index frame. *)
Theorem target_storage_index_frame_ptr:
  target_post ctx func cenv cx es sa sm s0 ee
    (PlaceR (StoragePlace tr slot tv)) vt rb s /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr slot tv)) rb G tn s /\
  expr_post ctx func cenv cx e ee sm sb s ef v x u /\
  ghost_kept cenv ee sm G tn s H un /\
  (!lbl. FST rb <> Label lbl) ==>
  eval_operand (FST rb) u = SOME slot /\
  place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
    (FST (SND rb)) vt /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr slot tv)) rb H un u
Proof
  strip_tac >>
  `eval_operand (FST rb) s = SOME slot /\
   place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
     (FST (SND rb)) vt /\
   (!z. FST rb = Var z ==> not_fresh_at sm z)` by
    (fs[target_post_def, place_ptr_rel_def] >> metis_tac[]) >>
  `!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==>
    lookup_var z u = SOME w` by (fs[expr_post_def] >> metis_tac[]) >>
  Cases_on `FST rb` >>
  fs[eval_operand_def, target_ptr_ok_def, op_prov_def, op_taint_def] >>
  rename1 `FST rb = Var p` >>
  drule ghost_kept_old_operand >>
  disch_then (qspec_then `p` mp_tac) >> simp[op_taint_def]
QED

Theorem target_toplevel_compiled_not_label_ptr:
  compile_get_target_ptr cfn cenv bt sa = (rb,sb) /\
  target_root bt = TopLevelNameTarget nsid ==>
  !lbl. FST rb <> Label lbl
Proof
  Cases_on `bt` >> simp[target_root_def] >> rpt strip_tac
  >- (gvs[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars nsid` >>
      gvs[comp_return_def] >> Cases_on `x` >> gvs[comp_return_def])
  >- metis_tac[aug_place_target_ptr_not_label] >>
  metis_tac[aug_place_target_ptr_not_label]
QED
