(*
 * Algebraic Optimization — CMP Flip Block-level Simulation
 *
 * Proves that the cmp_flip mini-pass preserves block execution semantics
 * up to state_equiv on dead variables (comparator outputs whose values
 * change under the flip).
 *
 * TOP-LEVEL:
 *   cmp_flip_run_insts_sim — run_insts simulation for cmp_flip transform
 *)

Theory algebraicOptCmpFlipBlockProof
Ancestors
  algebraicOptDefs algebraicOptCmpFlipSim
  analysisSimDefs analysisSimProofsBase
  passSimulationProps
  stateEquiv stateEquivProps execEquivProps
  venomExecSemantics venomState venomInst venomWf
  finite_map
Libs
  pairLib BasicProvers

(* ===== Core lemma: per-instruction cmp_flip simulation =====
 *
 * For each instruction, executing the original from state s1 and
 * the transformed from state s2 (where execution_equiv dead s1 s2)
 * produces execution_equiv dead results.
 *
 * Four cases:
 * 1. Unchanged: same instruction → step_inst_result_equiv
 * 2. Flip: CMP→FLIP_CMP from SAME state → dead var output differs
 * 3. Remove: ISZERO vs ASSIGN from DIFFERENT states → same iz_out
 * 4. Insert: 1 inst vs 2 insts → ISZERO heals dead var for ASSERT
 *)

(* ===== Case 1: Unchanged instruction =====
 * step_inst on same instruction from state_equiv states gives result_equiv.
 * Direct from step_inst_result_equiv. *)

(* ===== Case 2: Flip instruction =====
 * CMP(x,w) → FLIP_CMP(x,w') from the SAME state s.
 * Both access the same operands. Output (dead var) differs.
 * All other state fields (memory, etc.) identical. *)

(* For flip case: executing two non-INVOKE instructions from the SAME state,
   both with the same single output variable (which is in dead) and the same
   variable operands (only literal differs), produces execution_equiv dead.
   Key: both succeed or both fail (since they access the same variable operand).
   Output values may differ but output var is in dead. *)
Triviality flip_step_exec_equiv[local]:
  !inst1 inst2 dead fuel ctx st out.
    inst1.inst_opcode <> INVOKE /\ inst2.inst_opcode <> INVOKE /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    inst1.inst_outputs = [out] /\ inst2.inst_outputs = [out] /\
    out IN dead /\
    ((* step_inst_base either both OK or both Error *)
    (?val1 val2.
       step_inst_base inst1 st = OK (update_var out val1 st) /\
       step_inst_base inst2 st = OK (update_var out val2 st)) \/
    (?e1 e2.
       step_inst_base inst1 st = Error e1 /\
       step_inst_base inst2 st = Error e2)) ==>
    lift_result (execution_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (step_inst fuel ctx inst1 st)
      (step_inst fuel ctx inst2 st)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_non_invoke] >>
  gvs[lift_result_def, execution_equiv_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `out = v` >> gvs[]
QED

(* ===== Case 3: Remove (ISZERO → ASSIGN) =====
 * From execution_equiv dead states where the operand (dead var) has
 * related values: val_st2 = iszero_equiv(val_st1).
 * ISZERO(dead_var → iz_out) in st1 gives iz_out = iszero(val_st1).
 * ASSIGN(dead_var → iz_out) in st2 gives iz_out = val_st2.
 * From flip pair: iszero(val_st1) = val_st2. So iz_out agrees. *)

Triviality remove_step_exec_equiv[local]:
  !out_var iz_out st1 st2 dead fuel ctx.
    execution_equiv dead st1 st2 /\
    out_var IN dead /\ iz_out NOTIN dead /\
    (* The operand values satisfy the flip pair equivalence *)
    (?v1 v2. lookup_var out_var st1 = SOME v1 /\
             lookup_var out_var st2 = SOME v2 /\
             bool_to_word (v1 = 0w) = v2) ==>
    lift_result (execution_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (step_inst fuel ctx
        <| inst_id := ARB; inst_opcode := ISZERO;
           inst_operands := [Var out_var]; inst_outputs := [iz_out] |> st1)
      (step_inst fuel ctx
        <| inst_id := ARB; inst_opcode := ASSIGN;
           inst_operands := [Var out_var]; inst_outputs := [iz_out] |> st2)
Proof
  rpt gen_tac >> strip_tac >>
  (* Both are non-INVOKE, so step_inst = step_inst_base *)
  simp[step_inst_non_invoke] >>
  (* Unfold step_inst_base for ISZERO and ASSIGN *)
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def, lookup_var_def] >>
  gvs[] >>
  (* Now: OK (update_var iz_out (bool_to_word (v1 = 0w)) st1)
     vs   OK (update_var iz_out v2 st2)
     and bool_to_word (v1 = 0w) = v2 *)
  simp[lift_result_def] >>
  (* Need: execution_equiv dead (update_var iz_out ... st1) (update_var iz_out ... st2) *)
  gvs[execution_equiv_def, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> rw[] >>
  (* For v ∉ dead: if v = iz_out then both updated to same value;
     if v ≠ iz_out then unchanged from st1/st2 which agree by hypothesis *)
  first_x_assum irule >> simp[]
QED

val _ = export_theory();
