(* Constructor-level stopping observations for indexed DFT swaps. *)
Theory dftStoppingSwap
Ancestors
  dftSuccessSwap dftCommutation analysisSimProofsBase venomExecSemantics
  venomState venomInst instIdxIndep list

Theorem dft_abort_update_iff[local]:
  ~MEM (Var v) i.inst_operands /\ ~MEM v i.inst_outputs ==>
  ((?t. step_inst fuel C i (update_var v w s) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  strip_tac >>
  `!z. MEM (Var z) i.inst_operands ==> v <> z` by metis_tac[] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_frame >>
      disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
      Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]) >>
  drule_all step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[map_result_state_def] >> metis_tac[]
QED

Theorem dft_abort_fold_iff:
  !us s.
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
              ~MEM (FST p) i.inst_outputs) us ==>
  ((?t. step_inst fuel C i
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_abort_update_iff]
QED

Theorem dft_invoke_halt_fold_iff:
  !us s.
  i.inst_opcode = INVOKE /\
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
              ~MEM (FST p) i.inst_outputs) us ==>
  (step_inst fuel C i
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = Halt t <=>
   step_inst fuel C i s = Halt t)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  `!z. MEM (Var z) i.inst_operands ==> FST h <> z` by metis_tac[] >>
  drule_all step_inst_invoke_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `SND h`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]
QED

Theorem dft_error_idx_iff:
  ~is_terminator i.inst_opcode ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = Error e <=>
   step_inst fuel C i s = Error e)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >>
  simp[invoke_step_inst_idx_OK_only, step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def]
QED

Theorem dft_abort_idx_iff:
  ~is_terminator i.inst_opcode ==>
  ((?t. step_inst fuel C i (s with vs_inst_idx := n) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >>
  simp[invoke_step_inst_idx_OK_only, step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def] >> metis_tac[]
QED

Theorem dft_invoke_halt_idx_iff:
  i.inst_opcode = INVOKE ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = Halt t <=>
   step_inst fuel C i s = Halt t)
Proof
  strip_tac >> simp[invoke_step_inst_idx_OK_only] >>
  Cases_on `step_inst fuel C i s` >> simp[]
QED
