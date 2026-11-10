Theory loadElimPhiTransport
Ancestors
  loadElimTargetWrites loadElimOperationalHistory loadElimHistoryHelpers
  venomExecSemantics venomState list abiEncoderObserver

Theorem le_snapshot_batch_transport:
  !xs s t s'.
    R s t /\
    (!x y v w. R x y ==> R (update_var v w x) (update_var v w y)) /\
    (!j. MEM j xs ==> read s j = read t j) /\
    le_snapshot_batch read s xs = SOME s' ==>
    ?t'. le_snapshot_batch read t xs = SOME t' /\ R s' t'
Proof
  Induct >- simp[le_snapshot_batch_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[le_snapshot_batch_def, AllCaseEqs()] >>
  qpat_x_assum `!s t s'. _ /\ _ /\ le_snapshot_batch read s xs = SOME s' ==> _`
    (qspecl_then [`s`, `t`, `t'`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem le_eval_phis_transport:
  R s t /\
  (!x y v w. R x y ==> R (update_var v w x) (update_var v w y)) /\
  (!j. MEM j (le_phi_prefix js) ==> eval_one_phi s j = eval_one_phi t j) /\
  eval_phis s js = OK s' ==>
  ?t'. eval_phis t js = OK t' /\ R s' t'
Proof
  simp[le_eval_phis_snapshot] >>
  metis_tac[le_snapshot_batch_transport]
QED

Theorem le_eval_phis_prefix_eq:
  le_phi_prefix xs = le_phi_prefix ys ==>
  eval_phis s xs = eval_phis s ys
Proof
  metis_tac[loadElimOccurrenceCoverageTheory.le_phi_prefix_take, eval_phis_prefix]
QED

Triviality resolve_phi_MEM:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  ho_match_mp_tac venomExecSemanticsTheory.resolve_phi_ind >>
  rw[resolve_phi_def] >> gvs[] >> res_tac >> simp[]
QED

Theorem le_eval_one_phi_agreement:
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) inst.inst_operands ==> lookup_var v s = lookup_var v t) ==>
  eval_one_phi s inst = eval_one_phi t inst
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (Cases >> simp[eval_operand_def] >> metis_tac[]) >>
  simp[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >- simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t.vs_prev_bb` >> simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  drule resolve_phi_MEM >>
  strip_tac >> metis_tac[]
QED

Theorem le_configured_rest_phis_transport:
  le_configured_context ctx /\ R s t /\
  (!x y v w. R x y ==> R (update_var v w x) (update_var v w y)) /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!j v. MEM j (le_phi_prefix js) /\ MEM (Var v) j.inst_operands ==>
         lookup_var v s = lookup_var v t) /\
  eval_phis s js = OK s' ==>
  ?t'. eval_phis t (MAPi (\n i. load_elim_inst ctx actions (lats n) i) js) = OK t' /\
       R s' t'
Proof
  strip_tac >>
  `eval_phis t (MAPi (\n i. load_elim_inst ctx actions (lats n) i) js) =
   eval_phis t js` by
    (irule le_eval_phis_prefix_eq >> simp[le_configured_transformed_phi_prefix]) >>
  simp[] >> irule le_eval_phis_transport >>
  conj_tac >- simp[] >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> irule le_eval_one_phi_agreement >> simp[] >> metis_tac[]
QED
