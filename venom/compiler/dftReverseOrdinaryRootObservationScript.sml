Theory dftReverseOrdinaryRootObservation
Ancestors
  dftOrdinaryRootObservation dftEdgeReadiness dftGasProvenance
  dftScheduleOrder venomEffects venomInst list

Theorem dft_reverse_ordinary_edit:
  D = dft_pos_edit_ctx fi bi pre call x post C /\
  dft_pos_runtime_ready C fi bi pre call x post ==>
  C = dft_pos_edit_ctx fi bi pre x call post D
Proof
  metis_tac[dft_pos_runtime_ready_inverse]
QED

Theorem dft_reverse_ordinary_ready:
  D = dft_pos_edit_ctx fi bi pre call x post C /\
  dft_pos_runtime_ready C fi bi pre call x post ==>
  dft_pos_runtime_ready D fi bi pre x call post
Proof
  metis_tac[dft_pos_runtime_ready_reverse]
QED

(* The root clause, unlike effect conflicts, is directional. *)
Theorem dft_reverse_ordinary_nop_guard_probe:
  let call = <|inst_id := 0; inst_opcode := INVOKE;
               inst_operands := [Label "callee"]; inst_outputs := []|> in
  let x = <|inst_id := 1; inst_opcode := NOP;
            inst_operands := []; inst_outputs := []|> in
  ~dft_must_order call x /\ dft_must_order x call
Proof
  EVAL_TAC >> simp[]
QED
