(*
 * Range Analysis — Definitions
 *
 * Ports vyper/venom/analysis/variable_range/analysis.py to HOL4.
 *
 * Forward dataflow with widening-aware iteration.
 * Uses its own iteration loop (not wl_iterate) because widening
 * needs per-block visit counts and custom convergence logic.
 *
 * TOP-LEVEL:
 *   range_result             — analysis result record
 *   range_analyze            — top-level analysis
 *   range_get_range          — query: range of operand before instruction
 *   range_entry_state        — entry state at block start
 *   range_exit_state         — exit state at block end
 *
 * Helper:
 *   range_join_states        — join predecessor states
 *   range_widen_states       — per-variable widening
 *   range_run_block          — transfer function: run block forward
 *   range_evaluate_inst      — evaluate one instruction
 *   range_handle_phi         — handle PHI instructions at block entry
 *   range_edge_state         — state on a CFG edge (with branch refinement)
 *   range_apply_condition    — narrow state based on branch condition
 *   range_apply_iszero/eq/compare — specific branch refinement
 *   range_narrow_var         — narrow variable for comparison
 *   range_process_block      — process one block in the worklist
 *   range_one_pass           — one worklist pass
 *   range_iterate            — widening-aware fixpoint iteration
 *
 * WIDEN_THRESHOLD = 2: iterate normally for 2 visits, then widen.
 *)

Theory rangeAnalysisDefs
Ancestors
  rangeEvalDefs cfgDefs dfgDefs venomInst

(* ===== Constants ===== *)

Definition WIDEN_THRESHOLD_def:
  WIDEN_THRESHOLD = 2 : num
End

(* ===== Analysis Result ===== *)

Datatype:
  range_result = <|
    ra_entry : (string, range_state) fmap;    (* block label → entry state *)
    ra_exit  : (string, range_state) fmap;    (* block label → exit state *)
    ra_inst  : (num, range_state) fmap;       (* inst_id → state before inst *)
    ra_visits : (string, num) fmap            (* block label → visit count *)
  |>
End

Definition range_result_empty_def:
  range_result_empty = <|
    ra_entry := FEMPTY;
    ra_exit := FEMPTY;
    ra_inst := FEMPTY;
    ra_visits := FEMPTY
  |>
End

(* ===== Query API ===== *)

(* Get the range state at block entry *)
Definition range_entry_state_def:
  range_entry_state ra lbl =
    case FLOOKUP ra.ra_entry lbl of
      NONE => FEMPTY
    | SOME rs => rs
End

(* Get the range state at block exit *)
Definition range_exit_state_def:
  range_exit_state ra lbl =
    case FLOOKUP ra.ra_exit lbl of
      NONE => FEMPTY
    | SOME rs => rs
End

(* Get range of an operand just before an instruction.
   Matches Python VariableRangeAnalysis.get_range. *)
Definition range_get_range_def:
  range_get_range ra op inst_id =
    case op of
      Lit v => vr_constant (w2i v)
    | Var v =>
        (case FLOOKUP ra.ra_inst inst_id of
          NONE => VR_Top
        | SOME rs => rs_lookup rs v)
    | Label _ => VR_Top
End

(* Get visit count for a block *)
Definition ra_visit_count_def:
  ra_visit_count ra lbl =
    case FLOOKUP ra.ra_visits lbl of
      NONE => 0
    | SOME n => n
End

(* ===== State Join / Widen ===== *)

(* Join multiple predecessor states.
   Only variables present in ALL states are kept (intersection of keys).
   Ranges are unioned. Missing var in any pred → TOP → dropped.
   Matches Python _join_states. *)
Definition range_join_two_def:
  range_join_two (s1 : range_state) (s2 : range_state) =
    FUN_FMAP
      (λv. vr_union (rs_lookup s1 v) (rs_lookup s2 v))
      (FDOM s1 ∩ FDOM s2)
End

Definition range_join_states_def:
  range_join_states [] = FEMPTY ∧
  range_join_states [s] = s ∧
  range_join_states (s :: rest) = range_join_two s (range_join_states rest)
End

(* Per-variable widening. Matches Python _widen_states. *)
Definition range_widen_states_def:
  range_widen_states (old_st : range_state) (new_st : range_state) =
    FUN_FMAP
      (λv. vr_widen (rs_lookup old_st v) (rs_lookup new_st v))
      (FDOM new_st)
End

(* Normalize: remove TOP entries (matching Python _normalize_state). *)
Definition range_normalize_def:
  range_normalize (rs : range_state) =
    DRESTRICT rs { v | v ∈ FDOM rs ∧ ¬vr_is_top (rs_lookup rs v) }
End

(* ===== Branch Refinement ===== *)

(* Apply iszero-based refinement.
   True branch: value = 0. False branch: value ≠ 0.
   Matches Python _apply_iszero. *)
Definition range_apply_iszero_def:
  range_apply_iszero target_var is_true (rs : range_state) =
    if is_true then
      rs_write rs target_var (vr_constant 0)
    else
      let current = rs_lookup rs target_var in
      case current of
        VR_Top => rs
      | VR_Bottom => rs
      | VR_Range lo hi =>
          if lo < 0 then
            if hi < 0 then rs
            else if hi = 0 then
              (* [lo, 0] → [lo, -1] *)
              rs_write rs target_var (vr_clamp current (SOME lo) (SOME (-1)))
            else rs  (* spans zero, can't represent [lo,-1] ∪ [1,hi] *)
          else
            (* non-negative: intersect with [1, INT256_MAX] — excludes zero *)
            rs_write rs target_var
              (vr_intersect current (VR_Range 1 INT256_MAX))
End

(* Apply eq-based refinement.
   True branch: lhs = rhs → intersect ranges.
   False branch: no useful narrowing.
   Matches Python _apply_eq. *)
Definition range_apply_eq_def:
  range_apply_eq lhs rhs is_true (rs : range_state) =
    if ¬is_true then rs
    else
      case (lhs, rhs) of
        (Var v, Lit w) =>
          rs_write rs v (vr_constant (w2i w))
      | (Lit w, Var v) =>
          rs_write rs v (vr_constant (w2i w))
      | (Var v1, Var v2) =>
          let r1 = rs_lookup rs v1 in
          let r2 = rs_lookup rs v2 in
          let nr = vr_intersect r1 r2 in
          rs_write (rs_write rs v1 nr) v2 nr
      | _ => rs
End

(* Narrow variable for comparison.
   Matches Python _narrow_var. *)
Definition range_narrow_var_def:
  range_narrow_var rs var bound op is_true min_bound max_bound left_side =
    let current = rs_lookup rs var in
    if op = LT ∨ op = SLT then
      if left_side then
        if is_true then
          rs_write rs var (vr_clamp current (SOME min_bound) (SOME (bound - 1)))
        else
          rs_write rs var (vr_clamp current (SOME bound) (SOME max_bound))
      else
        if is_true then
          rs_write rs var (vr_clamp current (SOME (bound + 1)) (SOME max_bound))
        else
          rs_write rs var (vr_clamp current (SOME min_bound) (SOME bound))
    else (* GT or SGT *)
      if left_side then
        if is_true then
          rs_write rs var (vr_clamp current (SOME (bound + 1)) (SOME max_bound))
        else
          rs_write rs var (vr_clamp current (SOME min_bound) (SOME bound))
      else
        if is_true then
          rs_write rs var (vr_clamp current (SOME min_bound) (SOME (bound - 1)))
        else
          rs_write rs var (vr_clamp current (SOME bound) (SOME max_bound))
End

(* Apply comparison-based refinement.
   Matches Python _apply_compare. *)
(* For unsigned: bounds are [0, INT256_MAX] (non-negative signed range).
   For signed: bounds are [INT256_MIN, INT256_MAX] (full signed range). *)
Definition range_apply_compare_def:
  range_apply_compare op lhs rhs is_true (rs : range_state) =
    let min_bound = if op = SLT ∨ op = SGT then INT256_MIN else (0 : int) in
    let max_bound = INT256_MAX in
    case (lhs, rhs) of
      (Var v, Lit w) =>
        if ¬(op = SLT ∨ op = SGT) ∧
           (vr_is_top (rs_lookup rs v) ∨ vr_lo (rs_lookup rs v) < 0) then
          if ¬(((op = LT) ∧ is_true) ∨ (¬(op = LT) ∧ ¬is_true)) ∨
             w2i w > INT256_MAX then rs
          else range_narrow_var rs v (w2i w) op is_true 0 max_bound T
        else
          range_narrow_var rs v (w2i w) op is_true min_bound max_bound T
    | (Lit w, Var v) =>
        if ¬(op = SLT ∨ op = SGT) ∧
           (vr_is_top (rs_lookup rs v) ∨ vr_lo (rs_lookup rs v) < 0) then
          if ¬((¬(op = LT) ∧ is_true) ∨ ((op = LT) ∧ ¬is_true)) ∨
             w2i w > INT256_MAX then rs
          else range_narrow_var rs v (w2i w) op is_true 0 max_bound F
        else
          range_narrow_var rs v (w2i w) op is_true min_bound max_bound F
    | _ => rs
End

(* Apply condition: dispatch by producing instruction opcode.
   Matches Python _apply_condition (recursive for ASSIGN). *)
(* Fuel-bounded recursion through ASSIGN chains in DFG.
   In practice, ASSIGN chains are short (1-2 deep). *)
Definition range_apply_condition_def:
  range_apply_condition dfg (0 : num) op is_true (rs : range_state) = rs ∧
  range_apply_condition dfg (SUC fuel) op is_true rs =
    case op of
      Lit _ => rs
    | Label _ => rs
    | Var v =>
        case dfg_get_def dfg v of
          NONE => rs
        | SOME inst =>
            if inst.inst_opcode = ASSIGN then
              (case inst.inst_operands of
                [inner_op] =>
                  range_apply_condition dfg fuel inner_op is_true rs
              | _ => rs)
            else if inst.inst_opcode = ISZERO then
              (case inst.inst_operands of
                [target_op] =>
                  (case target_op of
                    Var tv => range_apply_iszero tv is_true rs
                  | _ => rs)
              | _ => rs)
            else if inst.inst_opcode = EQ then
              (case inst.inst_operands of
                [lhs_op; rhs_op] =>
                  range_apply_eq lhs_op rhs_op is_true rs
              | _ => rs)
            else if inst.inst_opcode = LT ∨ inst.inst_opcode = GT ∨
                    inst.inst_opcode = SLT ∨ inst.inst_opcode = SGT then
              (case inst.inst_operands of
                [lhs_op; rhs_op] =>
                  range_apply_compare inst.inst_opcode lhs_op rhs_op
                    is_true rs
              | _ => rs)
            else rs
End

(* Default fuel for ASSIGN chain depth *)
Definition ASSIGN_CHAIN_FUEL_def:
  ASSIGN_CHAIN_FUEL = 5 : num
End

(* Edge state: state on CFG edge pred→succ, with branch refinement on JNZ.
   Matches Python _edge_state. *)
Definition range_edge_state_def:
  range_edge_state dfg fn ra pred succ =
    case FLOOKUP ra.ra_exit pred of
      NONE => FEMPTY
    | SOME pred_exit =>
        case lookup_block pred fn.fn_blocks of
          NONE => pred_exit
        | SOME bb =>
            if NULL bb.bb_instructions then pred_exit
            else
              let term = LAST bb.bb_instructions in
                if term.inst_opcode ≠ JNZ then pred_exit
                else
                  case term.inst_operands of
                    [cond_op; Label true_lbl; Label false_lbl] =>
                      if true_lbl = succ then
                        range_apply_condition dfg ASSIGN_CHAIN_FUEL
                          cond_op T pred_exit
                      else if false_lbl = succ then
                        range_apply_condition dfg ASSIGN_CHAIN_FUEL
                          cond_op F pred_exit
                      else pred_exit
                  | _ => pred_exit
End

(* ===== Transfer Function ===== *)

(* Extract literal value from operand for evaluator precision *)
Definition operand_lit_def:
  operand_lit (Lit v) = SOME (w2i v) ∧
  operand_lit _ = NONE
End

(* Evaluate one instruction in the current state.
   Matches Python _evaluate_inst. *)
Definition range_evaluate_inst_def:
  range_evaluate_inst dfg inst (rs : range_state) =
    if inst.inst_opcode = PHI ∨ inst.inst_outputs = [] then rs
    else
      let ranges = MAP (operand_range rs) inst.inst_operands in
      let lits = MAP operand_lit inst.inst_operands in
      let result_range = eval_range inst.inst_opcode ranges lits in
      case inst.inst_outputs of
        [out] => rs_write rs out result_range
      | _ => rs  (* multi-output: don't track *)
End

(* Run block forward: evaluate each instruction, recording pre-inst state.
   Matches Python _run_block. *)
Definition range_run_block_def:
  range_run_block dfg [] rs imap = (rs, imap) ∧
  range_run_block dfg (inst :: rest) rs imap =
    let imap' = imap |+ (inst.inst_id, rs) in
    let rs' = range_evaluate_inst dfg inst rs in
    range_run_block dfg rest rs' imap'
End

(* ===== PHI Handling ===== *)

(* Compute range for one PHI instruction from predecessor exit states.
   Matches Python _phi_range. Uses phi_pairs to extract (label, var) pairs
   from the alternating [Label, Var, Label, Var, ...] operand list. *)
Definition range_phi_range_def:
  range_phi_range ra inst =
    if inst.inst_opcode ≠ PHI then VR_Top
    else
      let pairs = phi_pairs inst.inst_operands in
      FOLDL (λacc (lbl, v).
        let pred_exit =
          case FLOOKUP ra.ra_exit lbl of
            NONE => FEMPTY
          | SOME rs => rs
        in
        vr_union acc (rs_lookup pred_exit v))
      VR_Bottom
      pairs
End

(* Handle PHI instructions at block entry: fold phi results into state.
   Matches the phi loop in Python _compute_entry_state. *)
Definition range_handle_phis_def:
  range_handle_phis ra [] rs = rs ∧
  range_handle_phis ra (inst :: rest) rs =
    if inst.inst_opcode ≠ PHI then rs
    else
      let phi_range = range_phi_range ra inst in
      let phi_range' = if vr_is_bottom phi_range then VR_Top
                        else phi_range in
      let rs' = case inst.inst_outputs of
                  [out] => rs_write rs out phi_range'
                | _ => rs in
      range_handle_phis ra rest rs'
End

(* ===== Block Processing ===== *)

(* Compute entry state for a block.
   Matches Python _compute_entry_state. *)
Definition range_compute_entry_def:
  range_compute_entry cfg dfg fn ra lbl (bb : basic_block) =
    let preds = cfg_preds_of cfg lbl in
    let base_state =
      if NULL preds then FEMPTY
      else
        let pred_states = MAP (λp.
          range_edge_state dfg fn ra p lbl) preds in
        let joined = range_join_states pred_states in
        let normalized = range_normalize joined in
        let visits = ra_visit_count ra lbl in
        if visits > WIDEN_THRESHOLD then
          let old_entry = range_entry_state ra lbl in
          range_widen_states old_entry normalized
        else normalized in
    range_handle_phis ra bb.bb_instructions base_state
End

(* Process one block: compute entry, run transfer, update result.
   Returns (changed, updated_result).
   Matches Python logic in analyze() main loop. *)
Definition range_process_block_def:
  range_process_block cfg dfg fn ra lbl =
    case lookup_block lbl fn.fn_blocks of
      NONE => (F, ra)
    | SOME bb =>
        let ra' = ra with ra_visits :=
          ra.ra_visits |+ (lbl, ra_visit_count ra lbl + 1) in
        let entry_state = range_compute_entry cfg dfg fn ra' lbl bb in
        let run_result =
          range_run_block dfg bb.bb_instructions entry_state ra'.ra_inst in
        let exit_state = FST run_result in
        let imap = SND run_result in
        (¬(exit_state = range_exit_state ra lbl) ∨ lbl ∉ FDOM ra.ra_exit,
         ra' with <|
           ra_entry := ra'.ra_entry |+ (lbl, entry_state);
           ra_exit := ra'.ra_exit |+ (lbl, exit_state);
           ra_inst := imap
         |>)
End

(* ===== Worklist Iteration ===== *)

(* Process worklist: one pass through all queued blocks.
   Returns (updated_result, new_worklist).
   Matches Python analyze() worklist loop. *)
Definition range_one_pass_def:
  range_one_pass cfg dfg fn ra [] = (ra, []) ∧
  range_one_pass cfg dfg fn ra (lbl :: rest) =
    let (changed, ra') = range_process_block cfg dfg fn ra lbl in
    let (ra'', more) = range_one_pass cfg dfg fn ra' rest in
    if changed then
      (ra'', cfg_succs_of cfg lbl ++ more)
    else (ra'', more)
End

(* Widening-aware fixpoint iteration with fuel.
   The fuel ensures termination in HOL4; in practice, widening
   guarantees convergence in O(|blocks| * WIDEN_THRESHOLD) steps.
   Matches Python analyze() while-loop. *)
Definition range_iterate_def:
  range_iterate cfg dfg fn ra (0 : num) wl = ra ∧
  range_iterate cfg dfg fn ra (SUC fuel) [] = ra ∧
  range_iterate cfg dfg fn ra (SUC fuel) wl =
    let (ra', new_wl) = range_one_pass cfg dfg fn ra wl in
    if ra' = ra then ra
    else range_iterate cfg dfg fn ra' fuel new_wl
End

(* ===== Top-Level ===== *)

(* Run the full variable range analysis.
   Matches Python VariableRangeAnalysis.analyze(). *)
Definition range_analyze_def:
  range_analyze fn iter_fuel =
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let ra0 = range_result_empty in
    let wl = fn_labels fn in
    range_iterate cfg dfg fn ra0 iter_fuel wl
End
