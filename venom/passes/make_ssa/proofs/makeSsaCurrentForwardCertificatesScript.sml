Theory makeSsaCurrentForwardCertificates
Ancestors
  makeSsaCurrentCutInv makeSsaCurrentWfSsa makeSsaCurrentDemand
  venomExecSemantics venomState

(* Output liveness is deliberately absent: every selected original PHI
   operand is a predecessor demand, including operands of dead PHIs. *)
Theorem current_forward_original_phi_selected_defined:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME old /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  MEM (p,v) (phi_pairs (EL k old.bb_instructions).inst_operands) /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME pred /\
  current_cut_inv fn A renamed H events p (LENGTH pred.bb_instructions) st st' ==>
  IS_SOME (lookup_var v st)
Proof
  strip_tac >> drule_all current_wf_original_phi_demand >>
  fs[current_cut_inv_def]
QED

(* Pruned insertion supplies this demand without output-liveness at the
   successor, provided the original PHI batch does not redefine v. *)
Theorem current_forward_inserted_phi_selected_defined:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  lookup_block h fn.fn_blocks = SOME old /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==> ~MEM v di.inst_outputs) /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME pred /\
  current_cut_inv fn A renamed H events p (LENGTH pred.bb_instructions) st st' ==>
  IS_SOME (lookup_var v st)
Proof
  strip_tac >> drule_all current_wf_inserted_pred_demand >>
  fs[current_cut_inv_def]
QED

(* The only remaining static producer case for inserted PHI reads is a
   loop-header insertion for a variable already defined by an original PHI. *)
Theorem current_forward_inserted_phi_defined_or_local_phi:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  lookup_block h fn.fn_blocks = SOME old /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME pred /\
  current_cut_inv fn A renamed H events p (LENGTH pred.bb_instructions) st st' ==>
  IS_SOME (lookup_var v st) \/
  (?di back. MEM di old.bb_instructions /\ di.inst_opcode = PHI /\
    MEM v di.inst_outputs /\ fn_cfg_edge fn back h /\
    dominates (dom_analyze (cfg_analyze fn) fn) h back)
Proof
  strip_tac >>
  Cases_on `!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
    ~MEM v di.inst_outputs`
  >- (disj1_tac >> drule_all current_forward_inserted_phi_selected_defined >> simp[]) >>
  gvs[] >> disj2_tac >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecProofsTheory.lookup_block_label] >>
  qpat_x_assum `old.bb_label = h` (SUBST_ALL_TAC o SYM) >>
  drule_all current_wf_original_phi_inserted_return >> metis_tac[]
QED
