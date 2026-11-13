(* Nonword snapshots retain the original producer provenance. *)
Theory exprExtRequestSnapshotNonword
Ancestors
  exprExtRequestSnapshotProbe exprExtRequestTyping exprExtRequestStrongCapture
  exprExtRequestJointUnwrap exprPtrUnwrapStorageShape
  exprLowering loweringPosts compileEnv context valueCopyBytes vyperAST
  eventTopicValueProps exprExtRequestCapture

Theorem extrequest_snapshot_nonword_unwrap:
  well_typed_expr env e /\ ~expr_has_effect e /\
  compile_expr ce ty e sa = (vv,sc) /\
  vv_holds ce cx (expr_type e) r vv ee t /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) ==>
  unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) =
  unwrap_value ce vv
Proof
  strip_tac >> Cases_on `vv`
  >- simp[ext_call_arg_value_def] >>
  rename1 `vv_holds ce cx (expr_type e) r (LocatedValue vt p) ee t` >>
  fs[ext_call_arg_value_def, vv_type_def] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule_all extrequest_lowered_type_compatible >>
      disch_then (qspec_then `ce` strip_assume_tac) >>
      gvs[vv_holds_def] >>
      imp_res_tac bytestring_type_not_word >>
      gvs[unwrap_value_def]) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[compile_nonmemory_lowered_value_type] >>
  gvs[vv_holds_def]
QED

(* The original capture may already include an arbitrary later history frame.
   Retagging affects neither staging nor the eventual unwrap program. *)
Theorem extrequest_snapshot_nonword_endpoint:
  well_typed_expr env e /\ ~expr_has_effect e /\
  compile_expr ce ty e sa = (vv,sc) /\
  extrequest_strong_capture ctx func ce cx e r vv ee sn t /\
  stmt_state_rel ctx func ce cx ee t /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) ==>
  compile_snapshot_vv ce F
    (ext_call_arg_value (lowered_value_type ce e) vv) sn =
    (ext_call_arg_value (lowered_value_type ce e) vv,sn) /\
  unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) =
    unwrap_value ce vv
Proof
  strip_tac >> conj_tac
  >- (irule extrequest_snapshot_nonword_no_copy >> simp[]) >>
  drule_all extrequest_strong_capture_projection >>
  strip_tac >>
  `vv_holds ce cx (expr_type e) r vv ee t` by
    metis_tac[extrequest_capture_holds] >>
  irule extrequest_snapshot_nonword_unwrap >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
