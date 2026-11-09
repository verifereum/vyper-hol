(* Historical expression posts retained until positional reads occur. *)
Theory exprExtRequestCapture
Ancestors
  exprExtRequestSuffix exprExtRequestReadProbe loweringPosts
  exprLowering vyperState list

Definition extrequest_capture_def:
  extrequest_capture ctx func cenv cx e r vv ee t <=>
    ?es0 sa sb s0 ec tc.
      post_value_type cenv e = expr_type e /\
      vv_post ctx func cenv cx e es0 sa sb s0 ec r vv tc /\
      extrequest_read_frame cx ec ee /\
      vv_holds cenv cx (expr_type e) r vv ee t /\
      (!op w. (case vv of StackValue ty x => op = x
                       | LocatedValue ty p => op = p.ptr_operand) /\
              eval_operand op tc = SOME w ==> eval_operand op t = SOME w)
End

Definition extrequest_captures_def:
  extrequest_captures ctx func cenv cx es rs vvs ee t <=>
    LENGTH rs = LENGTH vvs /\
    LIST_REL (\e rv. extrequest_capture ctx func cenv cx e
                         (FST rv) (SND rv) ee t) es (ZIP (rs,vvs))
End

Theorem extrequest_capture_intro:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sb s0 ee r vv t ==>
  extrequest_capture ctx func cenv cx e r vv ee t
Proof
  strip_tac >> simp[extrequest_capture_def] >>
  qexistsl_tac [`es`, `sa`, `sb`, `s0`, `ee`, `t`] >>
  gvs[vv_post_def, extrequest_read_frame_def] >> metis_tac[]
QED

Theorem extrequest_captures_nil[simp]:
  extrequest_captures ctx func cenv cx [] [] [] ee t
Proof
  simp[extrequest_captures_def]
QED

Theorem extrequest_captures_cons[simp]:
  extrequest_captures ctx func cenv cx (e::es) (r::rs) (vv::vvs) ee t <=>
  extrequest_capture ctx func cenv cx e r vv ee t /\
  extrequest_captures ctx func cenv cx es rs vvs ee t
Proof
  simp[extrequest_captures_def] >> metis_tac[]
QED

Theorem extrequest_capture_holds:
  extrequest_capture ctx func cenv cx e r vv ee t ==>
  vv_holds cenv cx (expr_type e) r vv ee t
Proof
  simp[extrequest_capture_def] >> metis_tac[]
QED

Theorem extrequest_capture_read:
  extrequest_capture ctx func cenv cx e r vv ee t ==>
  ?v. read_result cx r ee = (INL v,ee)
Proof
  strip_tac >> drule extrequest_capture_holds >>
  Cases_on `vv` >> simp[vv_holds_def] >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

Theorem extrequest_captures_read:
  !es rs vvs. extrequest_captures ctx func cenv cx es rs vvs ee t ==>
  ?vs. read_results cx rs ee = (INL vs,ee) /\ LENGTH vs = LENGTH rs
Proof
  Induct >> Cases_on `rs` >> Cases_on `vvs` >>
  simp[extrequest_captures_def, Once read_results_def, return_def] >> rpt strip_tac >>
  drule extrequest_capture_read >> strip_tac >>
  qpat_x_assum `!rs vvs. _` mp_tac >>
  simp[extrequest_captures_def] >>
  disch_then (drule_all_then strip_assume_tac) >>
  simp[read_results_def, bind_def, return_def]
QED
