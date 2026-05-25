(* Phase 4: Comparator flip correctness.
 *
 * The cmp_flip transform reorders comparison operands and inserts
 * ISZERO instructions, preserving execution up to dead variables.
 *
 * TOP-LEVEL: ao_phase4_correct
 *)

Theory aoPhase4Proof
Ancestors
  algebraicOptDefs algebraicOptCmpFlipSim
  aoCmpFlipObligation
  venomExecSemantics venomWf venomState venomInst
  stateEquiv stateEquivProps execEquivProps
  passSimulationProps passSimulationDefs
Libs
  pairLib BasicProvers

Theorem ao_phase4_correct:
  !fuel ctx fn1 s.
    let dfg1 = dfg_build_function fn1 in
    let dead = ao_cmp_flip_dead_vars dfg1 fn1 in
    wf_function fn1 /\ ssa_form fn1 /\
    EVERY inst_wf (fn_insts fn1) ==>
    (?e. run_blocks fuel ctx fn1 s = Error e) \/
    lift_result (state_equiv dead) (execution_equiv dead) (execution_equiv dead)
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx (ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1) s)
Proof
  cheat
QED

val _ = export_theory();
