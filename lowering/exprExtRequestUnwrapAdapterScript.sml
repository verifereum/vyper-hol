(* Endpoint post adapters retain the historical producer's allocation cutoff. *)
Theory exprExtRequestUnwrapAdapter
Ancestors
  exprExtRequestStrongCapture exprExtRequestReconstruct
  exprExtRequestHistoryCompose exprExtRequestReadProbe loweringPosts
  exprSimUnwrap exprSafeOperand compileEnv exprExtRequestHistory vyperState

Theorem extrequest_history_placement:
  vv_at cenv cx ty sa sc ec r vv tc /\
  stmt_state_rel ctx func cenv cx ec tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  (case vv of StackValue aty op => safe_operand sc op
   | LocatedValue aty p => safe_operand sc p.ptr_operand) ==>
  vv_at cenv cx ty sa sn ee r vv t
Proof
  strip_tac >>
  `!n b sz. local_region cenv ec.scopes tc n b sz <=>
            local_region cenv ee.scopes t n b sz` by
    (rpt gen_tac >> irule extrequest_history_local_regions >> metis_tac[]) >>
  `extrequest_read_frame cx ec ee` by gvs[extrequest_history_frame_def] >>
  `!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r ec = (INL v,ec)` by
    (drule extrequest_read_result_frame >>
     disch_then (qspec_then `r` mp_tac) >>
     Cases_on `read_result cx r ec` >>
     drule read_result_state >> simp[]) >>
  Cases_on `vv`
  >- (gvs[vv_at_def, expr_val_at_def] >>
      rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v. read_result _ _ _ = _ ==> _`
        (drule_all_then strip_assume_tac) >>
      `eval_operand o' t = SOME w` by
        (drule_all extrequest_history_operand >> simp[]) >>
      qexists_tac `w` >> simp[]
      >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
          gvs[extrequest_history_frame_def] >>
          metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  gvs[vv_at_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ ==> !v tvt. _` mp_tac >> simp[] >>
  strip_tac >>
  `eval_operand p.ptr_operand t = SOME w` by
    (drule_all extrequest_history_operand >> simp[]) >>
  qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
      gvs[extrequest_history_frame_def] >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem extrequest_endpoint_post:
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty op => safe_operand sc op
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) ==>
  vv_post ctx func cenv cx e ee sa sn t ee r vv t
Proof
  strip_tac >>
  `vv_holds cenv cx (expr_type e) r vv ee t` by
    (drule_all extrequest_history_holds >> simp[]) >>
  `vv_at cenv cx (expr_type e) sa sn ee r vv t` by
    (irule extrequest_history_placement >>
     qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
     gvs[vv_post_def] >> metis_tac[]) >>
  simp[vv_post_def, locals_kept_def]
QED

(* Producer-start facts remain explicit; this theorem does not move the producer. *)
Theorem extrequest_history_unwrap_read:
  unwrap_value cenv vv sn = (op, sb) /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e ee sa sn t ee r vv t` by
    (drule_all extrequest_endpoint_post >> simp[]) >>
  irule unwrap_value_marked_read >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`sn`, `vv`] >> simp[] >>
  `sc.cs_next_var <= sn.cs_next_var /\ sc.cs_next_id <= sn.cs_next_id` by
    gvs[extrequest_history_frame_def] >>
  reverse (rpt conj_tac) >- decide_tac >- decide_tac >>
  Cases_on `vv` >> gvs[contextTheory.vv_operand_def, safe_operand_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
