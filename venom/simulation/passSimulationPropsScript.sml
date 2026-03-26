(*
 * Pass Simulation Framework — Correctness (Statements Only)
 *
 * Re-exports from proofs/passSimulationProofsScript.sml via ACCEPT_TAC.
 *)

Theory passSimulationProps
Ancestors
  passSimulationProofs

(* ===== Utilities ===== *)

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

(* lift_result covariant in both R_ok and R_term *)
Theorem lift_result_weaken:
  !(R1 : venom_state -> venom_state -> bool)
   (R2 : venom_state -> venom_state -> bool)
   (R1' : venom_state -> venom_state -> bool)
   (R2' : venom_state -> venom_state -> bool).
    (!s1 s2. R1 s1 s2 ==> R1' s1 s2) /\
    (!s1 s2. R2 s1 s2 ==> R2' s1 s2) ==>
    !r1 r2. lift_result R1 R2 r1 r2 ==>
            lift_result R1' R2' r1 r2
Proof
  ACCEPT_TAC lift_result_weaken_proof
QED

(* ===== General (relational) block sim ⟹ function sim ===== *)

(* Most general: per-block sim takes R-related states directly.
   No triangle, no valid_state_rel, no operand condition. *)
Theorem block_sim_function:
  !R_ok R_term bt fn.
    (!s. R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term
          (run_block fuel ctx bb s1)
          (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx fn s)
        (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_proof
QED

(* Like block_sim_function but R_ok reflexivity is conditional on
   a state predicate P preserved across blocks.
   Useful when per-block sim requires a condition (e.g. calldata length bound)
   that is maintained across blocks. *)
Theorem block_sim_function_with_pred:
  !P R_ok R_term bt fn.
    (!s. P s ==> R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s1 s2 s1' s2'.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 /\ P s1 /\
       run_block fuel ctx bb s1 = OK s1' /\
       run_block fuel ctx (bt bb) s2 = OK s2' /\
       R_ok s1' s2' ==>
       P s1') /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ P s1 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term
          (run_block fuel ctx bb s1)
          (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      P s /\ s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx fn s)
        (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_with_pred_proof
QED

(* ===== Pointwise block sim ⟹ function sim ===== *)

(* Triangle combiner: same-state per-block sim + valid_state_rel ⟹
   R-related per-block sim. Per-block adapter for pointwise theorems below. *)
Theorem same_state_to_rel_block_sim:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bb bt_bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x. MEM bb fn.fn_blocks /\
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\
    (!fuel ctx s. s.vs_inst_idx = 0 ==>
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term (run_block fuel ctx bb s)
                               (run_block fuel ctx bt_bb s))
  ==>
    !fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
      (?e. run_block fuel ctx bb s1 = Error e) \/
      lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx bt_bb s2)
Proof
  ACCEPT_TAC same_state_to_rel_block_sim_proof
QED

(* Pointwise: per-block sim proved on a single state (not R-related pair).
   Requires valid_state_rel, R_ok/R_term transitivity, and operand condition.
   Corollary of block_sim_function + same_state_to_rel_block_sim. *)
Theorem block_sim_function_pointwise:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_pointwise_proof
QED

(* Pointwise + reachability guard: per-block sim only required for entry block
   or when vs_prev_bb <> NONE (reachable non-entry). *)
Theorem block_sim_function_pointwise_reachable:
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
  ACCEPT_TAC block_sim_function_pointwise_reachable_proof
QED

(* ===== Bridge ===== *)

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

Theorem state_equiv_execution_equiv_valid_state_rel:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv vars)
Proof
  ACCEPT_TAC execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel
QED
