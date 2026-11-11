(* Source-frame composition and induction-interface probes. *)
Theory exprExtRequestSourceProbe
Ancestors
  exprExtRequestReadProbe supportedExprTraverse vyperInterpreter
  vyperStatePreservation vyperCallOutcomeFrame vyperMisc vyperState

Theorem extrequest_read_frame_refl[simp]:
  extrequest_read_frame cx s s
Proof
  simp[extrequest_read_frame_def]
QED

Theorem extrequest_read_frame_trans:
  extrequest_read_frame cx s t /\ extrequest_read_frame cx t u ==>
  extrequest_read_frame cx s u
Proof
  simp[extrequest_read_frame_def]
QED

Theorem extrequest_read_observation_frame:
  (!s res t. f s = (res,t) ==> t = s) ==>
  state_rel_frame (extrequest_read_frame cx) f
Proof
  simp[state_rel_frame_result] >> metis_tac[extrequest_read_frame_refl]
QED

Theorem extrequest_read_bookkeeping_frame:
  state_rel_frame (extrequest_read_frame cx) next_gas_reading /\
  state_rel_frame (extrequest_read_frame cx) (precompile_call_success bt)
Proof
  simp[state_rel_frame_result] >> conj_tac >> rpt strip_tac
  >- (drule next_gas_reading_state >> strip_tac >>
      simp[extrequest_read_frame_def]) >>
  drule precompile_call_success_state >> strip_tac >>
  simp[extrequest_read_frame_def]
QED

Theorem extrequest_read_frame_exprs:
  !es. EVERY (\e. state_rel_frame (extrequest_read_frame cx) (eval_expr cx e)) es ==>
    state_rel_frame (extrequest_read_frame cx) (eval_exprs cx es)
Proof
  Induct >> simp[Once evaluate_def]
  >- simp[state_rel_frame_def, return_def] >>
  rpt strip_tac >> ho_match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[extrequest_read_frame_trans] >>
  conj_tac >- simp[] >>
  rpt strip_tac >> ho_match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[extrequest_read_frame_trans] >> conj_tac
  >- (irule extrequest_read_observation_frame >> metis_tac[read_result_state]) >>
  rpt strip_tac >> ho_match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[extrequest_read_frame_trans] >>
  simp[state_rel_frame_def, return_def]
QED

Theorem extrequest_read_frame_expr_results:
  !es. EVERY (\e. state_rel_frame (extrequest_read_frame cx) (eval_expr cx e)) es ==>
    state_rel_frame (extrequest_read_frame cx) (eval_expr_results cx es)
Proof
  Induct >> simp[Once evaluate_def]
  >- simp[state_rel_frame_def, return_def] >>
  rpt strip_tac >> ho_match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[extrequest_read_frame_trans] >>
  conj_tac >- simp[] >>
  rpt strip_tac >> ho_match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[extrequest_read_frame_trans] >>
  simp[state_rel_frame_def, return_def]
QED

Theorem extrequest_read_frame_switch:
  state_rel_frame (extrequest_read_frame cx) f /\
  state_rel_frame (extrequest_read_frame cx) g ==>
  state_rel_frame (extrequest_read_frame cx) (switch_BoolV cx res f g)
Proof
  strip_tac >> rewrite_tac[switch_BoolV_def] >>
  ho_match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[extrequest_read_frame_trans] >> conj_tac
  >- (irule extrequest_read_observation_frame >> metis_tac[read_result_state]) >>
  rpt strip_tac >> IF_CASES_TAC >- simp[] >> IF_CASES_TAC >- simp[] >>
  simp[state_rel_frame_def, raise_def]
QED
