(*
 * Cross-Block Simulation — Lifting Theorem
 *
 * Per-block resolving_block_sim lifts to function-level pass_correct.
 *
 * TOP-LEVEL:
 *   resolving_block_sim_function — the main lifting theorem
 *   resolves_to_mono             — monotonicity: n ≤ m ⟹ resolves_to n ⟹ resolves_to m
 *   resolves_to_lift_result      — lift_result implies resolves_to 0
 *)

Theory crossBlockSimProps
Ancestors
  crossBlockSimDefs crossBlockSimProofs passSimulationDefs execEquivParamDefs
  stateEquiv stateEquivProps execEquivProps venomExecProps

(* ===== Basic properties ===== *)

(* lift_result is resolves_to at n=0 *)
Theorem resolves_to_lift_result:
  !R_ok R_term bbs1 bbs2 r1 r2.
    lift_result R_ok R_term r1 r2 ==>
    resolves_to R_ok R_term bbs1 bbs2 0 r1 r2
Proof
  simp[resolves_to_def]
QED

(* Monotonicity: increasing the budget preserves the relation *)
Theorem resolves_to_mono:
  !R_ok R_term bbs1 bbs2 n m r1 r2.
    n <= m /\
    resolves_to R_ok R_term bbs1 bbs2 n r1 r2 ==>
    resolves_to R_ok R_term bbs1 bbs2 m r1 r2
Proof
  metis_tac[resolves_to_mono_proof]
QED

(* ===== Main lifting theorem ===== *)

(*
 * Per-block resolving_block_sim lifts to function-level pass_correct.
 *
 * Preconditions:
 *   1. valid_state_rel: R_ok/R_term satisfy closure conditions
 *   2. Transitivity of R_ok, R_term
 *   3. Label preservation by bt
 *   4. Per-block resolving_block_sim (core simulation assumption)
 *   5. Operand agreement under R_ok (for state equiv propagation)
 *   6. Fuel monotonicity for both functions
 *
 * Conclusion: pass_correct (termination equiv + result equiv)
 *
 * Proof strategy:
 *   Forward termination: induction on fuel. At each block step,
 *     resolving_block_sim gives either OK/OK (IH applies) or
 *     cross-result (resolving side terminates within n extra steps;
 *     other side already terminal).
 *   Backward termination: symmetric.
 *   Result equiv: align fuels via fuel_mono, prove lift_result by
 *     induction. OK/OK case: triangle via run_block_preserves_R +
 *     block sim. Cross-result case: resolution produces matching
 *     terminal result.
 *)
Theorem resolving_block_sim_function:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bt.
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (* Per-block simulation with resolution *)
    (!bb fuel ctx s.
       MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 ==>
       resolving_block_sim R_ok R_term fn.fn_blocks fn'.fn_blocks
         (run_block fuel ctx bb s)
         (run_block fuel ctx (bt bb) s)) /\
    (* Operand agreement for state equiv propagation through original fn *)
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (* Fuel monotonicity *)
    (!fuel k ctx s.
       terminates (run_function fuel ctx fn s) ==>
       run_function (fuel + k) ctx fn s = run_function fuel ctx fn s) /\
    (!fuel k ctx s.
       terminates (run_function fuel ctx fn' s) ==>
       run_function (fuel + k) ctx fn' s = run_function fuel ctx fn' s)
  ==>
    !ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    (* Termination equivalence *)
    ((?fuel. terminates (run_function fuel ctx fn s)) <=>
     (?fuel'. terminates (run_function fuel' ctx fn' s))) /\
    (* Result equivalence when both terminate *)
    (!fuel fuel'.
       terminates (run_function fuel ctx fn s) /\
       terminates (run_function fuel' ctx fn' s) ==>
       lift_result R_ok R_term
         (run_function fuel ctx fn s)
         (run_function fuel' ctx fn' s))
Proof
  ACCEPT_TAC resolving_block_sim_function_proof
QED

(* Fuel monotonicity: terminated results are stable under added fuel *)
Theorem run_function_fuel_mono:
  !fuel ctx fn s.
    terminates (run_function fuel ctx fn s) ==>
    !k. run_function (fuel + k) ctx fn s = run_function fuel ctx fn s
Proof
  ACCEPT_TAC crossBlockSimProofsTheory.run_function_fuel_mono
QED
