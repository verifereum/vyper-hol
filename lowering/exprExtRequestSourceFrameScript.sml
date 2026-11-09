(* Effect-free source operands preserve captured read projections. *)
Theory exprExtRequestSourceFrame
Ancestors
  exprExtRequestSourceProbe exprExtRequestReadProbe vyperCallOutcomeFrame
  sum supportedExprTraverse vyperInterpreter
  vyperStatePreservation vyperPlaceFrames vyperState vyperAST

(* State-observing primitives used by the pure evaluator branches. *)
Theorem extrequest_read_primitive_frames:
  state_rel_frame (extrequest_read_frame cx) (read_result cx res) /\
  state_rel_frame (extrequest_read_frame cx) (lookup_global cx src id) /\
  state_rel_frame (extrequest_read_frame cx) (lookup_flag_mem cx nsid mid)
Proof
  rpt conj_tac >> irule extrequest_read_observation_frame >>
  rpt strip_tac
  >- metis_tac[read_result_state]
  >- metis_tac[lookup_global_state]
  >> metis_tac[lookup_flag_mem_state]
QED

Theorem extrequest_read_leaf_frames:
  state_rel_frame (extrequest_read_frame cx) (eval_expr cx (Name ann id)) /\
  state_rel_frame (extrequest_read_frame cx) (eval_expr cx (Literal ann lit)) /\
  state_rel_frame (extrequest_read_frame cx)
    (eval_expr cx (TopLevelName ann (src,id))) /\
  state_rel_frame (extrequest_read_frame cx)
    (eval_expr cx (FlagMember ann nsid mid))
Proof
  rpt conj_tac
  >- (rewrite_tac[Once evaluate_def] >>
      simp[state_rel_frame_def, bind_def, get_scopes_def,
           type_check_def, assert_def, return_def, raise_def,
           ignore_bind_def, extrequest_read_frame_def] >>
      gen_tac >> Cases_on `IS_SOME (lookup_scopes id st.scopes)` >> simp[])
  >- simp[Once evaluate_def, state_rel_frame_def, return_def]
  >- simp[Once evaluate_def, extrequest_read_primitive_frames]
  >> simp[Once evaluate_def, extrequest_read_primitive_frames]
QED

Theorem extrequest_read_pure_frames:
  state_rel_frame (extrequest_read_frame cx) (return v) /\
  state_rel_frame (extrequest_read_frame cx) (raise ex) /\
  state_rel_frame (extrequest_read_frame cx) (type_check b msg) /\
  state_rel_frame (extrequest_read_frame cx) (lift_sum rs) /\
  state_rel_frame (extrequest_read_frame cx) get_accounts /\
  state_rel_frame (extrequest_read_frame cx) (conditional_result cx res) /\
  state_rel_frame (extrequest_read_frame cx) (select_result cx ty res sub) /\
  state_rel_frame (extrequest_read_frame cx) (result_array_length cx res) /\
  state_rel_frame (extrequest_read_frame cx) (extend_place cx p sub) /\
  state_rel_frame (extrequest_read_frame cx) (get_place res)
Proof
  rpt conj_tac >> irule extrequest_read_observation_frame
  >- simp[return_def]
  >- simp[raise_def]
  >- (Cases_on `b` >> simp[type_check_def, assert_def, return_def, raise_def])
  >- (Cases_on `rs` >> simp[lift_sum_def, return_def, raise_def])
  >- simp[get_accounts_def, return_def]
  >- metis_tac[conditional_result_state]
  >- metis_tac[select_result_state]
  >- metis_tac[result_array_length_state]
  >- metis_tac[extend_place_state]
  >> metis_tac[get_place_state]
QED

Theorem extrequest_evaluate_read_frame:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx ty id body vs. eval_for cx ty id body vs = eval_for cx ty id body vs) /\
  (!cx e. ~supported_expr_exists expr_effect_root e ==>
    state_rel_frame (extrequest_read_frame cx) (eval_expr cx e)) /\
  (!cx es. ~supported_exprs_exists expr_effect_root es ==>
    state_rel_frame (extrequest_read_frame cx) (eval_exprs cx es)) /\
  (!cx bt. ~supported_target_exists expr_effect_root bt ==>
    state_rel_frame (extrequest_read_frame cx) (eval_base_place cx bt)) /\
  (!cx tgt. ~supported_target_exists expr_effect_root tgt ==>
    state_rel_frame (extrequest_read_frame cx) (eval_target_place cx tgt)) /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. ~supported_exprs_exists expr_effect_root es ==>
    state_rel_frame (extrequest_read_frame cx) (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def, expr_effect_root_def] >> rpt gen_tac
  >- simp[extrequest_read_leaf_frames]
  >- simp[extrequest_read_leaf_frames]
  >- simp[extrequest_read_leaf_frames]
  >- suspend "if_exp"
  >- simp[extrequest_read_leaf_frames]
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "type_builtin"
  >- simp[Once evaluate_def, state_rel_frame_def, return_def]
  >- suspend "exprs_cons"
  >- suspend "base_name"
  >- simp[Once evaluate_def, extrequest_read_primitive_frames]
  >- suspend "base_attribute"
  >- suspend "base_subscript"
  >- suspend "target"
  >- simp[Once evaluate_def, state_rel_frame_def, return_def]
  >> suspend "results_cons"
QED

Resume extrequest_evaluate_read_frame[attribute]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[struct]:
  rpt strip_tac >>
  fs[supported_fields_exists_every, supported_exprs_exists_every,
     listTheory.EVERY_MAP, combinTheory.o_DEF] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[if_exp]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >>
  irule extrequest_read_frame_switch >> metis_tac[]
QED

Resume extrequest_evaluate_read_frame[subscript]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def] >> reverse conj_tac
  >- metis_tac[] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_primitive_frames,
       extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[base_name]:
  rewrite_tac[Once evaluate_def] >>
  simp[state_rel_frame_def, bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def,
       ignore_bind_def, extrequest_read_frame_def] >>
  gen_tac >> Cases_on `IS_SOME (lookup_scopes id st.scopes)` >> simp[]
QED

Resume extrequest_evaluate_read_frame[base_attribute]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[target]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[results_cons]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[extrequest_read_frame_def] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >> metis_tac[]
QED

Resume extrequest_evaluate_read_frame[exprs_cons]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[extrequest_read_frame_def] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_primitive_frames] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >> metis_tac[]
QED

Resume extrequest_evaluate_read_frame[base_subscript]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[extrequest_read_frame_def] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def] >> reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_primitive_frames,
       extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[type_builtin]:
  rpt strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def] >> reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames]
QED

Resume extrequest_evaluate_read_frame[builtin]:
  rpt strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >>
  Cases_on `bt = Len`
  >- (simp[] >> irule state_rel_frame_bind_guarded >>
      simp[extrequest_read_frame_def] >> reverse conj_tac
      >- (first_x_assum irule >> goal_assum (drule_at Any) >>
          fs[supported_exprs_exists_every, listTheory.EVERY_MEM] >>
          conj_tac >- (Cases_on `es` >>
            gvs[type_check_def, assert_def, return_def, raise_def,
                vyperContextTheory.builtin_args_length_ok_def] >> metis_tac[listTheory.MEM]) >>
          goal_assum (drule_at Any)) >>
      rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[extrequest_read_frame_def, extrequest_read_pure_frames]) >>
  Cases_on `bt = Env MsgGas` >> simp[extrequest_read_bookkeeping_frame] >>
  irule state_rel_frame_bind_guarded >> simp[extrequest_read_frame_def] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_pure_frames] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[extrequest_read_frame_def, extrequest_read_bookkeeping_frame,
       extrequest_read_pure_frames]
QED

Finalise extrequest_evaluate_read_frame

Theorem extrequest_pure_expr_read_frame:
  ~expr_has_effect e ==>
  state_rel_frame (extrequest_read_frame cx) (eval_expr cx e)
Proof
  simp[expr_has_effect_def, extrequest_evaluate_read_frame]
QED

Theorem extrequest_pure_exprs_read_frame:
  EVERY (\e. ~expr_has_effect e) es ==>
  state_rel_frame (extrequest_read_frame cx) (eval_exprs cx es)
Proof
  simp[expr_has_effect_def, supported_exprs_exists_every,
       combinTheory.o_DEF, extrequest_evaluate_read_frame]
QED

Theorem extrequest_pure_results_read_frame:
  EVERY (\e. ~expr_has_effect e) es ==>
  state_rel_frame (extrequest_read_frame cx) (eval_expr_results cx es)
Proof
  simp[expr_has_effect_def, supported_exprs_exists_every,
       combinTheory.o_DEF, extrequest_evaluate_read_frame]
QED
