Theory concretizePtrDallocaObservationTransport
Ancestors
  ptrDiscipline pred_set finite_map

(* These consumers take source event bounds explicitly.  Producing the
   matching request or final_taint witness is a separate semantic obligation. *)
Theorem ptr_dalloca_storage_agreement_mono:
  storage_agree_except X st su /\ X SUBSET Y ==>
  storage_agree_except Y st su
Proof
  rw[storage_agree_except_def, word_agree_except_def,
     key_taint_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_request_taint_transport:
  dead_wf D /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  t.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  storage_agree_except tn.t_stor
    (s.vs_accounts s.vs_call_ctx.cc_address).storage
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  storage_agree_except tn.t_trans
    (s.vs_transient s.vs_call_ctx.cc_address)
    (t.vs_transient t.vs_call_ctx.cc_address) /\
  tt.t_stor SUBSET tn.t_stor /\ tt.t_trans SUBSET tn.t_trans ==>
  tt.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  tt.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
    (t.vs_transient t.vs_call_ctx.cc_address)
Proof
  strip_tac >>
  `storage_agree_except
     (D.d_stor s.vs_call_ctx.cc_address
       (s.vs_accounts s.vs_call_ctx.cc_address).storage)
     (s.vs_accounts s.vs_call_ctx.cc_address).storage
     (t.vs_accounts t.vs_call_ctx.cc_address).storage` by
    (irule ptr_dalloca_storage_agreement_mono >> goal_assum drule >> simp[]) >>
  `storage_agree_except
     (D.d_trans s.vs_call_ctx.cc_address
       (s.vs_transient s.vs_call_ctx.cc_address))
     (s.vs_transient s.vs_call_ctx.cc_address)
     (t.vs_transient t.vs_call_ctx.cc_address)` by
    (irule ptr_dalloca_storage_agreement_mono >> goal_assum drule >> simp[]) >>
  fs[dead_wf_def] >> metis_tac[SUBSET_TRANS]
QED

Theorem ptr_dalloca_final_taint_transport:
  dead_wf D /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  tn.t_imm SUBSET D.d_imm s.vs_immutables /\
  R SUBSET D.d_ret s.vs_returndata /\
  t.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  storage_agree_except tn.t_stor
    (s.vs_accounts s.vs_call_ctx.cc_address).storage
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  storage_agree_except tn.t_trans
    (s.vs_transient s.vs_call_ctx.cc_address)
    (t.vs_transient t.vs_call_ctx.cc_address) /\
  FDOM s.vs_immutables = FDOM t.vs_immutables /\
  (!k. k IN FDOM s.vs_immutables ==>
    word_agree_except {b | (k,b) IN tn.t_imm}
      (s.vs_immutables ' k) (t.vs_immutables ' k)) /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata /\
  (!i. i < LENGTH s.vs_returndata /\ i NOTIN R ==>
    EL i s.vs_returndata = EL i t.vs_returndata) /\
  tt.t_stor SUBSET tn.t_stor /\ tt.t_trans SUBSET tn.t_trans /\
  tt.t_imm SUBSET tn.t_imm /\ Rt SUBSET R ==>
  tt.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  tt.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
    (t.vs_transient t.vs_call_ctx.cc_address) /\
  tt.t_imm SUBSET D.d_imm t.vs_immutables /\
  Rt SUBSET D.d_ret t.vs_returndata
Proof
  strip_tac >>
  `tt.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
     (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
   tt.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
     (t.vs_transient t.vs_call_ctx.cc_address)` by
    (irule ptr_dalloca_request_taint_transport >>
     goal_assum drule >> simp[] >> metis_tac[]) >>
  `imms_agree_except D s.vs_immutables t.vs_immutables` by
    (fs[imms_agree_except_def, word_agree_except_def, SUBSET_DEF] >>
     metis_tac[]) >>
  `!i. i < LENGTH s.vs_returndata /\
       i NOTIN D.d_ret s.vs_returndata ==>
       EL i s.vs_returndata = EL i t.vs_returndata` by
    (fs[SUBSET_DEF] >> metis_tac[]) >>
  fs[dead_wf_def] >> metis_tac[SUBSET_TRANS]
QED
