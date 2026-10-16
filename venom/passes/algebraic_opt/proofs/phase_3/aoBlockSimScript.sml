(*
 * Algebraic Optimization — Phase 3 Block Simulation
 *
 * Lifts per-instruction simulation (ao_transform_inst) to block-level
 * simulation using analysis_block_sim_univ.
 *
 * Key insight: ao_transform_block = analysis_block_transform with
 * appropriate lattice instantiation (lattice = num, value = index).
 *
 * TOP-LEVEL:
 *   ao_phase3_block_sim — Phase 3 per-block lift_result simulation
 *)

Theory aoBlockSim
Ancestors
  algebraicOptDefs aoPeepholeSim aoResolveSim
  analysisSimDefs analysisSimProofsBase
  stateEquiv stateEquivProps
  execEquivParamProps
  venomExecSemantics venomState venomInst venomWf
  dfAnalyzeDefs indexedLists
  finite_map

(* ===== Lattice construction =====
 *
 * We need df_at bottom result bb.bb_label i = i for all valid i.
 * Construct result with ds_inst mapping (lbl, i) |-> i for all i.
 *)

(* Build a df_state where ds_inst(lbl, i) = i for i < n *)
Definition idx_df_state_def:
  idx_df_state lbl n : num df_state =
    <| ds_inst := FUN_FMAP (\p. SND p)
         (IMAGE (\i. (lbl, i)) (count n));
       ds_boundary := FEMPTY |>
End

(* ===== Per-instruction simulation =====
 *
 * This is the key assumption. It says: for well-formed instructions,
 * executing the original instruction relates to executing the transformed
 * instruction list via lift_result.
 *
 * Proved as ao_transform_inst_sim_inst in aoTransformInstSimScript.sml.
 * We re-state it here as the main hypothesis of our block sim theorem.
 *)

(* ===== Operand agreement under state_equiv =====
 *
 * If x NOTIN fv, then state_equiv fv s1 s2 ==> lookup_var x s1 = lookup_var x s2
 *)
Triviality operand_agreement[local]:
  !fv inst x s1 s2.
    MEM (Var x) inst.inst_operands /\
    x NOTIN fv /\
    state_equiv fv s1 s2 ==>
    lookup_var x s1 = lookup_var x s2
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* ===== Main theorem: Phase 3 block simulation ===== *)

(* ===== Invariant-carrying block simulation ===== *)

(* Like ao_phase3_block_sim but with state_inv.
   Per-instruction sim requires BOTH sound AND state_inv.
   state_inv is preserved through step_inst and state_equiv. *)

