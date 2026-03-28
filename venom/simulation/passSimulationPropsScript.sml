(*
 * Pass Simulation Framework — Correctness (Statements Only)
 *
 * Re-exports from proofs/passSimulationProofsScript.sml via ACCEPT_TAC.
 *)

Theory passSimulationProps
Ancestors
  passSimulationProofs analysisSimDefs venomWf venomInst passSimulationDefs
Libs
  indexedListsTheory listTheory

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

(* Two-state variant: per-block sim takes related states, no operand condition *)
Theorem two_state_block_sim_function:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s1)
                                 (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC two_state_block_sim_function_proof
QED

(* Unconditional version: when per-block sim gives lift_result (no error
   disjunct), function-level sim also gives unconditional lift_result. *)
Theorem block_sim_function_unconditional:
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
  ACCEPT_TAC block_sim_function_unconditional_proof
QED

(* Monotonicity for lift_result *)
Theorem lift_result_mono:
  !R1 R2 T1 T2 r1 r2.
    (!s1 s2. R1 s1 s2 ==> R2 s1 s2) /\
    (!s1 s2. T1 s1 s2 ==> T2 s1 s2) /\
    lift_result R1 T1 r1 r2 ==>
    lift_result R2 T2 r1 r2
Proof
  ACCEPT_TAC lift_result_mono_proof
QED

(* Invariant-carrying version: per-block sim only required when Inv holds.
   The invariant must be preserved by original block execution. *)
Theorem block_sim_function_inv:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        Inv s /\ s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!bb inst x.
       MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx fn' s)
Proof
  ACCEPT_TAC block_sim_function_inv_proof
QED

(* Invariant-carrying version with direct run_block_preserves_R obligation.
   Strictly more general than block_sim_function_inv. *)
Theorem block_sim_function_inv_rbpr:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        Inv s /\ s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb fuel ctx s s'.
       MEM bb fn'.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!fuel ctx bb s1 s2.
       MEM bb fn'.fn_blocks /\ R_ok s1 s2 /\
       Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2))
  ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx fn' s)
Proof
  ACCEPT_TAC block_sim_function_inv_rbpr_proof
QED

(* Cross-state variant: single cross-state per-block sim obligation.
   Strictly more general than rbpr. *)
Theorem block_sim_function_inv_cross:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!bb fuel ctx s s'.
       MEM bb fn'.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!bb fuel ctx s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 /\
       Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx fn' s)
Proof
  ACCEPT_TAC block_sim_function_inv_cross_proof
QED

(* Error-disjunct invariant block sim: block_inv stable under R_ok *)
Theorem block_sim_function_error:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (block_inv : venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ block_inv s ==>
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb fuel ctx s v.
       MEM bb fn.fn_blocks /\ block_inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK v ==> block_inv v) /\
    (!s1 s2. R_ok s1 s2 /\ block_inv s1 ==> block_inv s2) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ block_inv s ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_error_proof
QED

(* Strengthened: per-block sim and preserved handlers get vs_current_bb = bb_label *)
Theorem block_sim_function_error_bb:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (block_inv : venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ block_inv s /\
        s.vs_current_bb = bb.bb_label ==>
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb fuel ctx s v.
       MEM bb fn.fn_blocks /\ block_inv s /\ s.vs_inst_idx = 0 /\
       s.vs_current_bb = bb.bb_label /\
       run_block fuel ctx bb s = OK v ==> block_inv v) /\
    (!s1 s2. R_ok s1 s2 /\ block_inv s1 ==> block_inv s2) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ block_inv s ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  ACCEPT_TAC block_sim_function_error_bb_proof
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

(* General: function_map_transform preserves wf_function
   given per-block label/succs/bb_well_formed + inst_ids_distinct *)
Theorem fmt_preserves_wf_function:
  !bt fn.
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. bb_well_formed bb ==> bb_well_formed (bt bb)) /\
    (!bb. bb_succs (bt bb) = bb_succs bb) /\
    fn_inst_ids_distinct (function_map_transform bt fn)
    ==>
    wf_function fn ==> wf_function (function_map_transform bt fn)
Proof
  ACCEPT_TAC fmt_preserves_wf_function_proof
QED

(* General: function_map_transform preserves ssa_form
   given instruction set equality *)
Theorem fmt_preserves_ssa_form:
  !bt fn.
    fn_insts (function_map_transform bt fn) = fn_insts fn
    ==>
    ssa_form fn ==> ssa_form (function_map_transform bt fn)
Proof
  ACCEPT_TAC fmt_preserves_ssa_form_proof
QED

(* General SSA preservation for function_map_transform:
   per-instruction trace-back with id + output preservation *)
Theorem fmt_preserves_ssa_form_general:
  !bt fn.
    (!bb inst. MEM bb fn.fn_blocks /\
               MEM inst (bt bb).bb_instructions ==>
      ?orig. MEM orig bb.bb_instructions /\
             inst.inst_id = orig.inst_id /\
             (inst.inst_outputs = orig.inst_outputs \/
              inst.inst_outputs = [])) /\
    fn_inst_ids_distinct (function_map_transform bt fn) /\
    fn_inst_ids_distinct fn /\ ssa_form fn
    ==>
    ssa_form (function_map_transform bt fn)
Proof
  ACCEPT_TAC fmt_preserves_ssa_form_general_proof
QED

(* Instruction sublist preserves SSA *)
Theorem ssa_form_sublist:
  !fn fn'.
    ssa_form fn /\
    sublist (fn_insts fn') (fn_insts fn)
    ==>
    ssa_form fn'
Proof
  ACCEPT_TAC ssa_form_sublist_proof
QED

(* General SSA preservation for 1:1 transforms that preserve IDs and
   either preserve or clear outputs *)
Theorem ssa_form_preserved_by_output_subset:
  !fn fn'.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    fn_inst_ids_distinct fn' /\
    (!inst. MEM inst (fn_insts fn') ==>
      ?orig. MEM orig (fn_insts fn) /\
             inst.inst_id = orig.inst_id /\
             (inst.inst_outputs = orig.inst_outputs \/
              inst.inst_outputs = []))
    ==>
    ssa_form fn'
Proof
  ACCEPT_TAC ssa_form_preserved_by_output_subset_proof
QED

(* MAPi transform: each instruction traces to an original *)
Theorem mapi_transform_fn_insts_trace:
  !h fn inst.
    MEM inst (fn_insts (function_map_transform
      (\bb. bb with bb_instructions :=
        MAPi (\idx i. h bb idx i) bb.bb_instructions) fn)) ==>
    ?bb idx. MEM bb fn.fn_blocks /\
             idx < LENGTH bb.bb_instructions /\
             inst = h bb idx (EL idx bb.bb_instructions)
Proof
  ACCEPT_TAC mapi_transform_fn_insts_trace_proof
QED

(* LAST of MAPi equals f applied to last element *)
Theorem last_mapi:
  !(f:num -> 'a -> 'b) (l:'a list).
    l <> [] ==>
    LAST (MAPi f l) = f (PRE (LENGTH l)) (LAST l)
Proof
  rpt strip_tac >>
  `0 < LENGTH l` by (Cases_on `l` >> fs[]) >>
  `MAPi f l <> []`
    by metis_tac[LENGTH_MAPi, LENGTH_NIL,
                 DECIDE ``0n < n ==> n <> 0n``] >>
  simp[LAST_EL, LENGTH_MAPi, EL_MAPi]
QED

(* Helpers for mapi_transform_bb_well_formed - standalone to avoid dispatch issues *)
Triviality mapi_bb_nonempty[local]:
  !(f:num -> instruction -> instruction) l.
    l <> [] ==> MAPi f l <> []
Proof
  Cases_on `l` >> fs[MAPi_def]
QED

Triviality mapi_bb_last_term[local]:
  !(f:num -> instruction -> instruction) l.
    l <> [] /\
    is_terminator (LAST l).inst_opcode /\
    (!i. i < LENGTH l /\ is_terminator (EL i l).inst_opcode ==>
         is_terminator (f i (EL i l)).inst_opcode)
    ==>
    is_terminator (LAST (MAPi f l)).inst_opcode
Proof
  rpt strip_tac >>
  qspecl_then [`f`, `l`] mp_tac last_mapi >> impl_tac >- fs[] >>
  strip_tac >> fs[] >>
  `LAST l = EL (PRE (LENGTH l)) l` by simp[LAST_EL] >> fs[] >>
  first_x_assum match_mp_tac >>
  Cases_on `l` >> fs[]
QED

Triviality mapi_bb_only_last_term[local]:
  !(f:num -> instruction -> instruction) l.
    (!i. i < LENGTH l /\ is_terminator (EL i l).inst_opcode ==>
         i = PRE (LENGTH l)) /\
    (!i. i < LENGTH l /\ ~is_terminator (EL i l).inst_opcode ==>
         ~is_terminator (f i (EL i l)).inst_opcode)
    ==>
    !i. i < LENGTH l /\ is_terminator (EL i (MAPi f l)).inst_opcode ==>
        i = PRE (LENGTH l)
Proof
  rpt strip_tac >> gvs[EL_MAPi, LENGTH_MAPi] >> CCONTR_TAC >>
  `~is_terminator (EL i l).inst_opcode`
    by (strip_tac >> res_tac >> fs[]) >>
  res_tac
QED

Triviality mapi_bb_phi_prefix[local]:
  !(f:num -> instruction -> instruction) l.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) /\
    (!i. i < LENGTH l /\ (EL i l).inst_opcode = PHI ==>
         (f i (EL i l)).inst_opcode = PHI) /\
    (!i. i < LENGTH l /\ (EL i l).inst_opcode <> PHI ==>
         (f i (EL i l)).inst_opcode <> PHI)
    ==>
    !i j. i < j /\ j < LENGTH l /\
          (EL j (MAPi f l)).inst_opcode = PHI ==>
          (f i (EL i l)).inst_opcode = PHI
Proof
  rpt strip_tac >> gvs[EL_MAPi, LENGTH_MAPi] >>
  `(EL j l).inst_opcode = PHI`
    by (CCONTR_TAC >> res_tac >> fs[]) >>
  first_x_assum match_mp_tac >>
  first_x_assum (qspecl_then [`i`, `j`] mp_tac) >> simp[]
QED

(* bb_well_formed preservation for MAPi instruction transforms *)
Theorem mapi_transform_bb_well_formed:
  !f bb.
    bb_well_formed bb /\
    (!i. i < LENGTH bb.bb_instructions /\
         is_terminator (EL i bb.bb_instructions).inst_opcode ==>
         is_terminator (f i (EL i bb.bb_instructions)).inst_opcode) /\
    (!i. i < LENGTH bb.bb_instructions /\
         ~is_terminator (EL i bb.bb_instructions).inst_opcode ==>
         ~is_terminator (f i (EL i bb.bb_instructions)).inst_opcode) /\
    (!i. i < LENGTH bb.bb_instructions /\
         (EL i bb.bb_instructions).inst_opcode = PHI ==>
         (f i (EL i bb.bb_instructions)).inst_opcode = PHI) /\
    (!i. i < LENGTH bb.bb_instructions /\
         (EL i bb.bb_instructions).inst_opcode <> PHI ==>
         (f i (EL i bb.bb_instructions)).inst_opcode <> PHI)
    ==>
    bb_well_formed (bb with bb_instructions := MAPi f bb.bb_instructions)
Proof
  rpt strip_tac >> fs[bb_well_formed_def, LENGTH_MAPi] >>
  rpt conj_tac
  >- (Cases_on `bb.bb_instructions` >> fs[MAPi_def])
  >- (irule mapi_bb_last_term >> metis_tac[])
  >- (match_mp_tac (SPEC_ALL mapi_bb_only_last_term) >> metis_tac[])
  >- (match_mp_tac (SPEC_ALL mapi_bb_phi_prefix) >> metis_tac[])
QED

(* bb_succs preserved when terminators are unchanged and
   non-terminators map to non-terminators *)
Theorem mapi_transform_bb_succs:
  !f bb.
    (!i inst. is_terminator inst.inst_opcode ==> f i inst = inst) /\
    (!i inst. ~is_terminator inst.inst_opcode ==>
              ~is_terminator (f i inst).inst_opcode)
    ==>
    bb_succs (bb with bb_instructions := MAPi f bb.bb_instructions) =
    bb_succs bb
Proof
  rpt strip_tac >>
  Cases_on `bb.bb_instructions` >> simp[bb_succs_def, MAPi_def] >>
  qspecl_then [`f`, `h::t`] mp_tac last_mapi >> simp[] >> strip_tac >>
  fs[] >>
  Cases_on `is_terminator (LAST (h::t)).inst_opcode`
  >- (res_tac >> fs[])
  >- (`~is_terminator (f (LENGTH t) (LAST (h::t))).inst_opcode`
        by metis_tac[] >>
      fs[get_successors_def, is_terminator_def])
QED

(* fn_inst_ids_distinct preserved when inst_id preserved *)
Theorem mapi_transform_fn_inst_ids:
  !f fn.
    (!i inst. (f i inst).inst_id = inst.inst_id) /\
    fn_inst_ids_distinct fn
    ==>
    fn_inst_ids_distinct (function_map_transform
      (\bb. bb with bb_instructions := MAPi f bb.bb_instructions) fn)
Proof
  rpt strip_tac >>
  fs[fn_inst_ids_distinct_def, function_map_transform_def,
     MAP_MAP_o, combinTheory.o_DEF] >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP g _))` >>
  qmatch_goalsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP g' _))` >>
  `g = g'` by (unabbrev_all_tac >> simp[FUN_EQ_THM, MAP_EQ_f]) >>
  fs[]
QED

(* Per-block variant: inst_id condition may depend on the block.
   Needed when the MAPi transform varies per block (e.g. analysis-driven). *)
Theorem mapi_transform_fn_inst_ids_bb:
  !(g : basic_block -> num -> instruction -> instruction) fn.
    (!bb i inst. (g bb i inst).inst_id = inst.inst_id) /\
    fn_inst_ids_distinct fn
    ==>
    fn_inst_ids_distinct (function_map_transform
      (\bb. bb with bb_instructions := MAPi (g bb) bb.bb_instructions) fn)
Proof
  rpt strip_tac >>
  fs[fn_inst_ids_distinct_def, function_map_transform_def,
     MAP_MAP_o, combinTheory.o_DEF] >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP h _))` >>
  qmatch_goalsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP h' _))` >>
  `h = h'` by (unabbrev_all_tac >> simp[FUN_EQ_THM, MAP_EQ_f]) >>
  fs[]
QED

(* Per-block variant of preserves_wf: transform may vary per block.
   Conditions on g : basic_block -> num -> instruction -> instruction. *)
Theorem mapi_transform_preserves_wf_bb:
  !(g : basic_block -> num -> instruction -> instruction) fn.
    (!bb i inst. (g bb i inst).inst_id = inst.inst_id) /\
    (!bb i inst. is_terminator inst.inst_opcode ==> g bb i inst = inst) /\
    (!bb i inst. ~is_terminator inst.inst_opcode ==>
                 ~is_terminator (g bb i inst).inst_opcode) /\
    (!bb i inst. inst.inst_opcode = PHI ==> (g bb i inst).inst_opcode = PHI) /\
    (!bb i inst. inst.inst_opcode <> PHI ==> (g bb i inst).inst_opcode <> PHI)
    ==>
    wf_function fn ==>
    wf_function (function_map_transform
      (\bb. bb with bb_instructions := MAPi (g bb) bb.bb_instructions) fn)
Proof
  rpt strip_tac >>
  irule fmt_preserves_wf_function >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule mapi_transform_bb_succs >> simp[] >>
      metis_tac[])
  >- (rpt strip_tac >> irule mapi_transform_bb_well_formed >> simp[] >>
      metis_tac[])
  >- (irule mapi_transform_fn_inst_ids_bb >> simp[] >>
      fs[wf_function_def])
QED

(* Combined: MAPi transform preserves wf_function.
   Conditions: inst_id preserved, terminators unchanged (identity),
   non-terminators stay non-terminators, PHI/non-PHI preserved. *)
Theorem mapi_transform_preserves_wf:
  !f fn.
    (!i inst. (f i inst).inst_id = inst.inst_id) /\
    (!i inst. is_terminator inst.inst_opcode ==> f i inst = inst) /\
    (!i inst. ~is_terminator inst.inst_opcode ==>
              ~is_terminator (f i inst).inst_opcode) /\
    (!i inst. inst.inst_opcode = PHI ==> (f i inst).inst_opcode = PHI) /\
    (!i inst. inst.inst_opcode <> PHI ==> (f i inst).inst_opcode <> PHI)
    ==>
    wf_function fn ==>
    wf_function (function_map_transform
      (\bb. bb with bb_instructions := MAPi f bb.bb_instructions) fn)
Proof
  rpt strip_tac >>
  irule fmt_preserves_wf_function >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule mapi_transform_bb_succs >> simp[] >>
      metis_tac[])
  >- (rpt strip_tac >> irule mapi_transform_bb_well_formed >> simp[] >>
      metis_tac[])
  >- (irule mapi_transform_fn_inst_ids >> simp[] >>
      fs[wf_function_def])
QED

(* General: FLAT (MAPi (\i x. [f i x]) l) = MAPi f l *)
Theorem flat_mapi_singleton:
  !(f:num -> 'a -> 'b) (l:'a list).
    FLAT (MAPi (\i x. [f i x]) l) = MAPi f l
Proof
  Induct_on `l`
  >- simp[MAPi_def]
  >- (rpt strip_tac >> simp[MAPi_def, combinTheory.o_DEF] >>
      first_x_assum (qspec_then `\n x. f (SUC n) x` mp_tac) >>
      strip_tac >>
      irule MAPi_CONG >> simp[])
QED

(* analysis_block_transform with singleton f = MAPi transform *)
Theorem abt_singleton_eq_mapi:
  !bottom result (f : 'a -> instruction -> instruction) bb.
    analysis_block_transform bottom result (\ll inst. [f ll inst]) bb =
    bb with bb_instructions :=
      MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
           bb.bb_instructions
Proof
  simp[analysis_block_transform_def, flat_mapi_singleton]
QED

(* Function-level: analysis_function_transform with singleton = fmt with MAPi *)
Theorem aft_singleton_eq_fmt_mapi:
  !bottom result (f : 'a -> instruction -> instruction) fn.
    analysis_function_transform bottom result (\v inst. [f v inst]) fn =
    function_map_transform
      (\bb. bb with bb_instructions :=
        MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
             bb.bb_instructions) fn
Proof
  simp[analysis_function_transform_def, function_map_transform_def,
       ir_function_component_equality] >>
  simp[MAP_EQ_f, abt_singleton_eq_mapi]
QED

(* ===== block_map_transform (MAP) toolkit ===== *)

(* block_map_transform = MAPi with index-ignoring function *)
Theorem bmt_eq_mapi[local]:
  !f bb. block_map_transform f bb =
         bb with bb_instructions := MAPi (\i x. f x) bb.bb_instructions
Proof
  simp[block_map_transform_def]
QED

(* WF preservation for function_map_transform (block_map_transform f) *)
Theorem map_transform_preserves_wf:
  !f fn.
    (!inst. (f inst).inst_id = inst.inst_id) /\
    (!inst. is_terminator inst.inst_opcode ==> f inst = inst) /\
    (!inst. ~is_terminator inst.inst_opcode ==>
            ~is_terminator (f inst).inst_opcode) /\
    (!inst. inst.inst_opcode = PHI ==> (f inst).inst_opcode = PHI) /\
    (!inst. inst.inst_opcode <> PHI ==> (f inst).inst_opcode <> PHI) /\
    wf_function fn ==>
    wf_function (function_map_transform (block_map_transform f) fn)
Proof
  rpt strip_tac >>
  `function_map_transform (block_map_transform f) fn =
   function_map_transform
     (\bb. bb with bb_instructions := MAPi (\i x. f x) bb.bb_instructions) fn`
    by (simp[function_map_transform_def, ir_function_component_equality,
             MAP_EQ_f, bmt_eq_mapi]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule mapi_transform_preserves_wf >> simp[]
QED

(* SSA preservation for function_map_transform (block_map_transform f) *)
Theorem map_transform_preserves_ssa:
  !f fn.
    (!inst. (f inst).inst_id = inst.inst_id) /\
    (!inst. inst.inst_outputs = (f inst).inst_outputs \/
            (f inst).inst_outputs = []) /\
    wf_function fn /\ ssa_form fn ==>
    ssa_form (function_map_transform (block_map_transform f) fn)
Proof
  rpt strip_tac >>
  `function_map_transform (block_map_transform f) fn =
   function_map_transform
     (\bb. bb with bb_instructions := MAPi (\i x. f x) bb.bb_instructions) fn`
    by (simp[function_map_transform_def, ir_function_component_equality,
             MAP_EQ_f, bmt_eq_mapi]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule fmt_preserves_ssa_form_general >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> fs[MEM_MAP] >>
      qexists_tac `y` >> simp[] >> metis_tac[])
  >- fs[wf_function_def]
  >- (`fn_inst_ids_distinct fn` by fs[wf_function_def] >>
      fs[fn_inst_ids_distinct_def, function_map_transform_def,
         block_map_transform_def, MAP_MAP_o, combinTheory.o_DEF] >>
      qmatch_asmsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP g _))` >>
      qmatch_goalsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP g' _))` >>
      `g = g'` by (unabbrev_all_tac >> simp[FUN_EQ_THM, MAP_EQ_f]) >>
      fs[])
QED
