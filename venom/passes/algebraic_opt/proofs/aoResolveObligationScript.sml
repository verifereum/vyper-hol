(* Obligation: iszero resolution preserves step_inst semantics.
 *
 * Reformulated with chain invariant preconditions.
 *
 * Integration with algebraicOptProofsScript.sml:
 *   1. Extend sinv to: ao_dfg_inv /\ ao_iszero_chain_inv /\ ao_chains_defined
 *   2. ao_transform_inst_sim_inst (line ~1909): replace H_resolve precondition
 *      with ao_iszero_chain_inv + ao_chains_defined from the extended sinv
 *   3. ao_per_inst_sim_fn0 (line ~1981): propagate extended sinv
 *   4. ao_phases123_run_blocks_sim (line ~2028): remove H_resolve from
 *      preconditions, use ao_resolve_iszero_inst_sim with chain invariant
 *      from extended sinv
 *   5. Prove sinv preservation: ao_iszero_chain_inv and ao_chains_defined
 *      are maintained by step_inst (SSA ensures no overwriting)
 *   6. Prove sinv initial: ao_iszero_chain_inv_initial for block entry
 *   7. Prove sinv compat: chain invariant compatible with state_equiv fv
 *)
Theory aoResolveObligation
Ancestors
  algebraicOptDefs venomExecSemantics venomWf
  stateEquiv
Libs
  pairLib BasicProvers

(* ===== Definitions ===== *)

(* Adjacent chain elements satisfy the iszero relationship *)
Definition ao_iszero_chain_inv_def:
  ao_iszero_chain_inv targets st <=>
    !v chain. ALOOKUP targets v = SOME chain ==>
      !k. k + 1 < LENGTH chain ==>
        !val_k val_k1.
          eval_operand (EL k chain) st = SOME val_k /\
          eval_operand (EL (k + 1) chain) st = SOME val_k1 ==>
          val_k1 = bool_to_word (val_k = 0w)
End

(* All chain elements are defined *)
Definition ao_chains_defined_def:
  ao_chains_defined targets st <=>
    !v chain k. ALOOKUP targets v = SOME chain /\
                k < LENGTH chain ==>
                ?w. eval_operand (EL k chain) st = SOME w
End

(* Well-formed targets: chain has >= 2 elements, variable is last *)
Definition ao_targets_wf_def:
  ao_targets_wf targets <=>
    !v chain. ALOOKUP targets v = SOME chain ==>
      1 < LENGTH chain /\ LAST chain = Var v
End

(* ===== Structural: ao_compute_fn_iszero_targets produces wf targets ===== *)

Theorem ao_compute_fn_iszero_targets_wf:
  !fn. ao_targets_wf (ao_compute_fn_iszero_targets fn)
Proof
  cheat
QED

(* ===== Chain invariant preservation ===== *)

(* Chain invariant holds for empty targets *)
Theorem ao_iszero_chain_inv_empty:
  !st. ao_iszero_chain_inv [] st
Proof
  simp[ao_iszero_chain_inv_def]
QED

(* Chain definedness holds for empty targets *)
Theorem ao_chains_defined_empty:
  !st. ao_chains_defined [] st
Proof
  simp[ao_chains_defined_def]
QED

(* Chain invariant preserved by step_inst that doesn't modify chain vars.
   In SSA form, a variable is written at most once, so once the chain
   invariant is established, it is maintained by all subsequent instructions
   (which write different variables). *)
Theorem ao_iszero_chain_inv_step_preserved:
  !targets inst fuel ctx st st'.
    ao_iszero_chain_inv targets st /\
    step_inst fuel ctx inst st = OK st' /\
    (* SSA: inst doesn't overwrite any chain variable *)
    (!v chain k. ALOOKUP targets v = SOME chain /\
                 k < LENGTH chain ==>
                 eval_operand (EL k chain) st' =
                 eval_operand (EL k chain) st) ==>
    ao_iszero_chain_inv targets st'
Proof
  cheat
QED

(* Chain definedness preserved similarly *)
Theorem ao_chains_defined_step_preserved:
  !targets inst fuel ctx st st'.
    ao_chains_defined targets st /\
    step_inst fuel ctx inst st = OK st' /\
    (!v chain k. ALOOKUP targets v = SOME chain /\
                 k < LENGTH chain ==>
                 eval_operand (EL k chain) st' =
                 eval_operand (EL k chain) st) ==>
    ao_chains_defined targets st'
Proof
  cheat
QED

(* Chain invariant compatible with state_equiv on fresh vars:
   if two states agree on all non-fresh vars, and the chain uses
   only non-fresh vars, then the chain invariant transfers. *)
Theorem ao_iszero_chain_inv_state_equiv_compat:
  !targets fv st1 st2.
    ao_iszero_chain_inv targets st1 /\
    state_equiv fv st1 st2 /\
    (* Chain variables are not in fv (fresh vars) *)
    (!v chain k x. ALOOKUP targets v = SOME chain /\
                   k < LENGTH chain /\ EL k chain = Var x ==> x NOTIN fv) ==>
    ao_iszero_chain_inv targets st2
Proof
  cheat
QED

(* Similarly for chains_defined *)
Theorem ao_chains_defined_state_equiv_compat:
  !targets fv st1 st2.
    ao_chains_defined targets st1 /\
    state_equiv fv st1 st2 /\
    (!v chain k x. ALOOKUP targets v = SOME chain /\
                   k < LENGTH chain /\ EL k chain = Var x ==> x NOTIN fv) ==>
    ao_chains_defined targets st2
Proof
  cheat
QED

(* ===== Main theorem ===== *)

Theorem ao_resolve_iszero_inst_sim:
  !targets inst fuel ctx st.
    inst_wf inst /\
    ao_iszero_chain_inv targets st /\
    ao_chains_defined targets st /\
    ao_targets_wf targets ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) st =
    step_inst fuel ctx inst st
Proof
  cheat
QED
