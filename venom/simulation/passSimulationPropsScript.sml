(*
 * Pass Simulation Framework — Correctness (Statements Only)
 *
 * Re-exports from proofs/passSimulationProofsScript.sml via ACCEPT_TAC.
 *)

Theory passSimulationProps
Ancestors
  passSimulationProofs

Theorem lookup_block_map:
  !lbl bbs bt.
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    lookup_block lbl (MAP bt bbs) =
      OPTION_MAP bt (lookup_block lbl bbs)
Proof
  ACCEPT_TAC lookup_block_map_proof
QED

Theorem lift_result_refl:
  !(R : venom_state -> venom_state -> bool).
    (!s. R s s) ==>
    !r. lift_result R r r
Proof
  ACCEPT_TAC lift_result_refl_proof
QED

Theorem lift_result_trans:
  !(R : venom_state -> venom_state -> bool).
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) ==>
    !r1 r2 r3. lift_result R r1 r2 /\ lift_result R r2 r3 ==>
               lift_result R r1 r3
Proof
  ACCEPT_TAC lift_result_trans_proof
QED

Theorem inst_sim_block_sim:
  !(R : venom_state -> venom_state -> bool) f.
    inst_simulates R f ==>
    block_simulates R (block_map_transform f)
Proof
  ACCEPT_TAC inst_sim_block_sim_proof
QED

Theorem block_sim_function:
  !(R : venom_state -> venom_state -> bool) bt.
    block_simulates R bt /\
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    !fuel fn s.
      lift_result R (run_function fuel fn s)
                 (run_function fuel (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_proof
QED

Theorem conditional_inst_sim:
  !(R : venom_state -> venom_state -> bool) f P.
    (!s. R s s) /\
    (!inst s. P inst ==>
       lift_result R (step_inst inst s) (step_inst (f inst) s)) /\
    (!inst. P inst ==>
       is_terminator inst.inst_opcode =
       is_terminator (f inst).inst_opcode) /\
    (!inst. ~P inst ==> f inst = inst) ==>
    inst_simulates R f
Proof
  ACCEPT_TAC conditional_inst_sim_proof
QED

Theorem block_sim_compose:
  !(R : venom_state -> venom_state -> bool) bt1 bt2.
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) /\
    block_simulates R bt1 /\ block_simulates R bt2 ==>
    block_simulates R (bt2 o bt1)
Proof
  ACCEPT_TAC block_sim_compose_proof
QED
