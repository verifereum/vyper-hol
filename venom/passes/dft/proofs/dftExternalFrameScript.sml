(* Bidirectional successful framing of external calls by disjoint updates. *)
Theory dftExternalFrame
Ancestors
  dftCommutation venomExecSemantics venomState venomInst list

Theorem dft_external_ok_update_iff[local]:
  is_ext_call_op y.inst_opcode /\
  ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs ==>
  (step_inst fuel C y (update_var v w s) = OK r <=>
   ?t. step_inst fuel C y s = OK t /\ r = update_var v w t)
Proof
  strip_tac >>
  `y.inst_opcode <> INVOKE` by
    (Cases_on `y.inst_opcode` >> gvs[is_ext_call_op_def]) >>
  `!z. MEM (Var z) y.inst_operands ==> v <> z` by metis_tac[] >>
  drule_all step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
  Cases_on `step_inst fuel C y s` >> simp[map_result_state_def] >>
  metis_tac[]
QED

Theorem dft_external_ok_fold_iff:
  !us s r.
  is_ext_call_op y.inst_opcode /\
  EVERY (\p. ~MEM (Var (FST p)) y.inst_operands /\
              ~MEM (FST p) y.inst_outputs) us ==>
  (step_inst fuel C y
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = OK r <=>
   ?t. step_inst fuel C y s = OK t /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_external_ok_update_iff] >> metis_tac[]
QED
