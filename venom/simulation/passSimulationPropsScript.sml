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
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
    (!s. R_ok s s) /\ (!s. R_term s s) ==>
    !r. lift_result R_ok R_term r r
Proof
  ACCEPT_TAC lift_result_refl_proof
QED

Theorem lift_result_trans:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) ==>
    !r1 r2 r3. lift_result R_ok R_term r1 r2 /\
               lift_result R_ok R_term r2 r3 ==>
               lift_result R_ok R_term r1 r3
Proof
  ACCEPT_TAC lift_result_trans_proof
QED

(* inst_sim_block_sim removed — likely false without valid_state_rel (L177).
   inst_sim_block_sim_proof was removed from passSimulationProofsScript.sml.
   block_sim_function below is the correct replacement. *)

(* Per-fn-block sim + valid_state_rel + operand cond ⟹ function sim.
   Block sim only required at vs_inst_idx = 0 (entry invariant). *)
Theorem block_sim_function:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_proof
QED

(* Reachability-guarded version: entry block unconditional, non-entry needs prev_bb *)
Theorem block_sim_function_reachable:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        (bb = HD fn.fn_blocks \/ s.vs_prev_bb <> NONE) ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      (fn.fn_blocks <> [] /\
       s.vs_current_bb = (HD fn.fn_blocks).bb_label \/
       s.vs_prev_bb <> NONE) ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_reachable_proof
QED

(* conditional_inst_sim removed — proof was removed from passSimulationProofs *)
(* block_sim_compose removed — proof was removed from passSimulationProofs *)

Theorem lift_result_implies_pass_correct:
  !fresh exec1 exec2.
    (!fuel. result_equiv fresh (exec1 fuel) (exec2 fuel)) /\
    (!fuel fuel'. terminates (exec1 fuel) /\ terminates (exec1 fuel') ==>
                  exec1 fuel = exec1 fuel') /\
    (!fuel fuel'. terminates (exec2 fuel) /\ terminates (exec2 fuel') ==>
                  exec2 fuel = exec2 fuel')
  ==>
    pass_correct fresh exec1 exec2
Proof
  ACCEPT_TAC lift_result_implies_pass_correct_proof
QED
