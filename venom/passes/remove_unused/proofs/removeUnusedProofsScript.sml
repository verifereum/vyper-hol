(*
 * Remove Unused Variables — Proofs
 *
 * Proof strategy:
 *   1. Per-instruction: NOP'ing a removable instruction with dead outputs
 *      is identity on all state except those outputs.
 *      Key lemma: step_effect_free_state_equiv (from venomInstProps)
 *      says step_inst on effect-free inst gives state_equiv (set outputs).
 *      NOP gives OK s (step_nop_identity). So original and NOP'd differ
 *      only on the outputs → state_equiv (set outputs).
 *
 *   2. Block-level: accumulate per-instruction NOP'd outputs. Each
 *      non-NOP'd instruction reads only live vars (liveness soundness),
 *      so it doesn't observe the missing dead outputs.
 *
 *   3. Function-level: block_sim_function with FLIPPED triangle.
 *      Standard block_sim_function has operand condition on the ORIGINAL
 *      function. With state_equiv elim, eliminated vars don't agree,
 *      but NOP'd instructions in the original still reference them.
 *      Fix: flip the triangle composition:
 *        run_block orig s1 ~ run_block trans s1  (same-state, diff-code)
 *        run_block trans s1 ~ run_block trans s2  (same-code, R_ok states)
 *      Now the operand condition is on the TRANSFORMED block. NOP'd
 *      instructions have empty operand lists. Surviving instructions
 *      only read live vars (not in elim), so they agree under
 *      state_equiv elim. Proof is identical to block_sim_function_proof
 *      with the two triangle legs swapped.
 *
 *   4. OWHILE iteration preserves the relation (monotone elim set).
 *
 * Preconditions:
 * - liveness_analyze is sound (dead vars are truly unused)
 * - msize_fence correctly identifies reachable live MSIZEs
 *)

Theory removeUnusedProofs
Ancestors
  removeUnusedDefs passSimulationProps venomInstProps venomWf

(* ===== Liveness soundness predicate ===== *)

(* If a variable is not live-after at index idx, then no later
   instruction in the block reads it without an intervening write. *)
Definition liveness_sound_for_block_def:
  liveness_sound_for_block (lr : liveness_result) bb <=>
    !idx v.
      idx < LENGTH bb.bb_instructions ==>
      let live = live_after_at lr bb.bb_label idx
                   (LENGTH bb.bb_instructions) in
      ~MEM v live ==>
      !j. idx < j /\ j < LENGTH bb.bb_instructions ==>
          let inst_j = EL j bb.bb_instructions in
          MEM (Var v) inst_j.inst_operands ==>
          ?k. idx < k /\ k < j /\
              MEM v (EL k bb.bb_instructions).inst_outputs
End

(* ===== Per-instruction NOP correctness ===== *)

(* Core lemma: NOP'ing a removable instruction preserves
   state_equiv (set inst.inst_outputs).
   Original: step_inst gives OK s', differs from s only on outputs.
   NOP: step_inst gives OK s (identity).
   So s and s' are state_equiv (set outputs).

   is_removable = non-volatile, non-terminator, has outputs.
   All removable opcodes (pure, reads like MLOAD/SLOAD/TLOAD,
   MSIZE, PHI, ASSIGN) only modify vs_vars at the output positions.
   Volatile ops (CALL, LOG, etc.) are excluded by is_removable.
   Ops without outputs (MSTORE, SSTORE, etc.) are excluded too. *)
(* venom_wf eliminates Error branches from step_inst,
   inst_wf ensures well-formed operand counts. *)
Theorem nop_removable_state_equiv:
  !fuel ctx inst s s'.
    venom_wf ctx /\ inst_wf inst /\
    is_removable inst /\
    step_inst fuel ctx inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

(* ===== Block-level ===== *)

(* Outputs NOP'd by remove_unused_block *)
Definition block_nop_outputs_def:
  block_nop_outputs lr fence bb =
    set (FLAT (MAPi (\idx inst.
      let live = live_after_at lr bb.bb_label idx
                   (LENGTH bb.bb_instructions) in
      let fenced = fence idx in
      if is_removable inst /\
         (~fenced \/ Eff_MSIZE NOTIN write_effects inst.inst_opcode) /\
         EVERY (\v. ~MEM v live) inst.inst_outputs
      then inst.inst_outputs
      else [])
      bb.bb_instructions))
End

Theorem remove_unused_block_correct_proof:
  !fuel ctx lr fence bb s.
    liveness_sound_for_block lr bb ==>
    let nop_outs = block_nop_outputs lr fence bb in
    lift_result (state_equiv nop_outs) (execution_equiv nop_outs)
      (run_block fuel ctx bb s)
      (run_block fuel ctx (remove_unused_block lr fence bb) s)
Proof
  cheat
QED

(* ===== Function-level ===== *)

(* Outputs eliminated by a single pass *)
Definition single_pass_eliminated_vars_def:
  single_pass_eliminated_vars fn =
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
      fn.fn_blocks)) DIFF
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
      (remove_unused_single_pass fn).fn_blocks))
End

(* Single-pass correctness: excludes only the single-pass elim set *)
Theorem remove_unused_single_pass_correct_proof:
  !fuel ctx fn s.
    let elim = single_pass_eliminated_vars fn in
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (remove_unused_single_pass fn) s)
Proof
  cheat
QED

(* Iteration monotonicity: each pass only removes more outputs,
   so the full elim set is a superset of each single-pass elim set.
   state_equiv is monotone (larger excl set → weaker relation). *)
Theorem remove_unused_iterate_monotone:
  !fn. single_pass_eliminated_vars fn SUBSET
       remove_unused_eliminated_vars fn
Proof
  cheat
QED

(* Full iteration correctness *)
Theorem remove_unused_function_correct_proof:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn ==>
    let elim = remove_unused_eliminated_vars fn in
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (remove_unused_function fn) s)
Proof
  cheat
QED
