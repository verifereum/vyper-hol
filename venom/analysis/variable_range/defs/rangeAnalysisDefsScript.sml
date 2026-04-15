(*
 * Range Analysis — Definitions
 *
 * Ports vyper/venom/analysis/variable_range/analysis.py to HOL4.
 * Upstream: vyperlang/vyper@8092fe67f (algebraic representation for range analysis)
 *
 * Forward dataflow with widening, expressed as an instance of
 * df_analyze_widen from the generic dataflow framework.
 *
 * TOP-LEVEL:
 *   range_analyze            — top-level analysis (via df_analyze_widen)
 *   range_get_range          — query: range of operand before instruction
 *   range_at_inst             — query: range state before instruction
 *   range_entry_state        — entry state at block start
 *   range_exit_state         — exit state at block end
 *
 * Helper:
 *   range_join_two           — binary join (intersect domains, union ranges)
 *   range_widen_states       — per-variable widening
 *   range_evaluate_inst      — evaluate one instruction (per-inst transfer)
 *   range_branch_refine      — branch refinement on JNZ edges
 *   range_phi_edge_rename    — PHI renaming per CFG edge
 *   range_edge_transfer_opt  — combined edge transfer (branch + PHI + option)
 *   range_join_opt           — option-wrapped join (NONE = identity)
 *   range_widen_opt          — option-wrapped widening
 *   range_transfer_opt       — option-wrapped per-instruction transfer
 *   range_apply_condition    — narrow state based on branch condition
 *   range_apply_iszero/eq/compare — specific branch refinement
 *   range_narrow_var         — narrow variable for comparison
 *
 * WIDEN_THRESHOLD = 2: iterate normally for 2 visits, then widen.
 *)

Theory rangeAnalysisDefs
Ancestors
  rangeEvalDefs cfgDefs dfgDefs dfAnalyzeWidenDefs venomInst

(* ===== Constants ===== *)

Definition WIDEN_THRESHOLD_def:
  WIDEN_THRESHOLD = 2 : num
End

(* Default fuel for ASSIGN chain depth *)
Definition ASSIGN_CHAIN_FUEL_def:
  ASSIGN_CHAIN_FUEL = 5 : num
End

(* ===== State Join / Widen ===== *)

(* Join two predecessor states.
   Only variables present in BOTH states are kept (intersection of keys).
   Ranges are unioned. Missing var in any pred → TOP → dropped.
   Matches Python _join_states. *)
Definition range_join_two_def:
  range_join_two (s1 : range_state) (s2 : range_state) =
    FUN_FMAP
      (λv. vr_union (rs_lookup s1 v) (rs_lookup s2 v))
      (FDOM s1 ∩ FDOM s2)
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
              rs_write rs target_var (vr_clamp current (SOME lo) (SOME (-1)))
            else rs
          else
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
Definition range_apply_compare_def:
  range_apply_compare op lhs rhs is_true (rs : range_state) =
    let min_bound = if op = SLT ∨ op = SGT then INT256_MIN else (0 : int) in
    let max_bound = INT256_MAX in
    case (lhs, rhs) of
      (Var v, Lit w) =>
        if ¬(op = SLT ∨ op = SGT) ∧
           (vr_is_top (rs_lookup rs v) ∨ vr_lo (rs_lookup rs v) < 0) then
          if ¬(((op = LT) ∧ is_true) ∨ (¬(op = LT) ∧ ¬is_true)) ∨
             w2i w ≤ 0 ∨ w2i w > INT256_MAX then rs
          else range_narrow_var rs v (w2i w) op is_true 0 max_bound T
        else if ¬(op = SLT ∨ op = SGT) ∧
                (w2i w ≤ 0 ∨ w2i w > INT256_MAX) then rs
        else
          range_narrow_var rs v (w2i w) op is_true min_bound max_bound T
    | (Lit w, Var v) =>
        if ¬(op = SLT ∨ op = SGT) ∧
           (vr_is_top (rs_lookup rs v) ∨ vr_lo (rs_lookup rs v) < 0) then
          if ¬((¬(op = LT) ∧ is_true) ∨ ((op = LT) ∧ ¬is_true)) ∨
             w2i w ≤ 0 ∨ w2i w > INT256_MAX then rs
          else range_narrow_var rs v (w2i w) op is_true 0 max_bound F
        else if ¬(op = SLT ∨ op = SGT) ∧
                (w2i w ≤ 0 ∨ w2i w > INT256_MAX) then rs
        else
          range_narrow_var rs v (w2i w) op is_true min_bound max_bound F
    | _ => rs
End

(* Apply condition: dispatch by producing instruction opcode.
   Matches Python _apply_condition (recursive for ASSIGN). *)
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

(* ===== Transfer Function ===== *)

(* Evaluate one instruction in the current state.
   Matches Python _evaluate_inst. PHIs delete their output variable;
   PHI output ranges are re-established by subsequent instructions, not by edge transfer. *)
Definition range_evaluate_inst_def:
  range_evaluate_inst dfg inst (rs : range_state) =
    if inst.inst_opcode = PHI then
      (case inst.inst_outputs of
         [out] => rs \\ out
       | _ => FEMPTY)
    else if inst.inst_outputs = [] then rs
    else
      let ranges = MAP (operand_range rs) inst.inst_operands in
      let lits = MAP operand_lit inst.inst_operands in
      let result_range = eval_range inst.inst_opcode ranges lits in
      case inst.inst_outputs of
        [out] => rs_write rs out result_range
      | _ => FEMPTY
End

(* ===== Option-wrapped lattice for df_analyze_widen ===== *)

(* NONE = unprocessed / identity for join.
   SOME rs = processed range state. *)

(* Unwrap option state, returning FEMPTY for NONE *)
Definition range_unwrap_def:
  range_unwrap NONE = (FEMPTY : range_state) ∧
  range_unwrap (SOME rs) = rs
End

(* Option-wrapped join: NONE is bottom (unprocessed blocks don't
   contribute to join). Always normalizes the result to strip VR_Top entries,
   ensuring absorption: join(join(a,b),b) = join(a,b). *)
Definition range_join_opt_def:
  range_join_opt NONE NONE = NONE ∧
  range_join_opt NONE (SOME x) = SOME (range_normalize x) ∧
  range_join_opt (SOME x) NONE = SOME (range_normalize x) ∧
  range_join_opt (SOME a) (SOME b) =
    SOME (range_normalize (range_join_two a b))
End

(* Option-wrapped widening.
   Any disagreement → SOME FEMPTY (no variable constraints).
   Agreement → identity (fixpoint reached).
   This is sound because FEMPTY is trivially satisfiable by any environment.
   Convergence: FEMPTY is absorbing under widen_opt, so once entry reaches
   FEMPTY it stays FEMPTY, guaranteeing fixpoint after O(threshold) visits. *)
Definition range_widen_opt_def:
  range_widen_opt NONE NONE = NONE ∧
  range_widen_opt NONE (SOME x) = SOME FEMPTY ∧
  range_widen_opt (SOME x) NONE = SOME FEMPTY ∧
  range_widen_opt (SOME old_st) (SOME new_st) =
    if old_st = new_st then SOME old_st
    else SOME FEMPTY
End

(* Option-wrapped per-instruction transfer.
   Context = (dfg, bbs) — only dfg is used by transfer. *)
Definition range_transfer_opt_def:
  range_transfer_opt (ctx : dfg_analysis # basic_block list)
                     (inst : instruction)
                     (rs_opt : range_state option) =
    let dfg = FST ctx in
    case rs_opt of
      NONE => SOME (range_evaluate_inst dfg inst FEMPTY)
    | SOME rs => SOME (range_evaluate_inst dfg inst rs)
End

(* ===== Edge Transfer ===== *)

(* Branch refinement on a CFG edge pred→succ.
   If the predecessor's terminator is JNZ, narrow ranges based on
   which branch was taken. Matches Python _edge_state. *)
Definition range_branch_refine_def:
  range_branch_refine dfg bbs pred succ pred_exit =
    case lookup_block pred bbs of
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

(* PHI renaming on a CFG edge pred→succ.
   For each PHI instruction in succ's block, find the operand associated
   with pred's label and assign its range to the PHI output variable.
   This replaces range_handle_phis: instead of post-join PHI handling,
   we rename per-edge so that join correctly combines per-predecessor
   PHI contributions. *)
Definition range_phi_edge_rename_def:
  range_phi_edge_rename bbs pred succ (rs : range_state) =
    case lookup_block succ bbs of
      NONE => rs
    | SOME bb =>
        FOLDL (λst inst.
          if inst.inst_opcode ≠ PHI then st
          else
            case inst.inst_outputs of
              [out] =>
                let pairs = phi_pairs inst.inst_operands in
                (case ALOOKUP pairs pred of
                  NONE => st
                | SOME v => rs_write st out (rs_lookup rs v))
            | _ => st
        ) rs bb.bb_instructions
End

(* Edge transfer: branch refinement, wrapped for the option lattice.
   Context = (dfg, fn.fn_blocks).
   Note: PHI output ranges are handled by intra-block transfer
   (range_evaluate_inst deletes PHI outputs, subsequent instructions
   re-establish ranges). Putting PHI renaming here would be unsound
   because the entry value at position 0 is checked against the
   predecessor exit state, before PHIs have executed. *)
Definition range_edge_transfer_opt_def:
  range_edge_transfer_opt (ctx : dfg_analysis # basic_block list)
                          pred succ (rs_opt : range_state option) =
    case rs_opt of
      NONE => NONE
    | SOME rs =>
        let (dfg, bbs) = ctx in
        SOME (range_branch_refine dfg bbs pred succ rs)
End

(* ===== Top-level analysis via df_analyze_widen ===== *)

(* Variable range analysis via the generic widening dataflow framework.
   Forward direction, option-wrapped range_state lattice.
   Context = (dfg, fn.fn_blocks).
   Entry block: SOME FEMPTY (no ranges known at entry). *)
Definition range_analyze_def:
  range_analyze fn =
    let dfg = dfg_build_function fn in
    let entry_val =
      OPTION_MAP (λlbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) in
    df_analyze_widen Forward NONE range_join_opt range_widen_opt
                     WIDEN_THRESHOLD range_transfer_opt
                     range_edge_transfer_opt (dfg, fn.fn_blocks)
                     entry_val fn
End

(* ===== Query API ===== *)

(* Entry state at block start *)
Definition range_entry_state_def:
  range_entry_state ra lbl =
    range_unwrap (df_widen_entry NONE ra lbl)
End

(* Exit state at block end (= boundary for forward analysis) *)
Definition range_exit_state_def:
  range_exit_state ra lbl =
    range_unwrap (df_widen_boundary NONE ra lbl)
End

(* Range state at instruction point (block lbl, instruction index idx) *)
Definition range_at_inst_def:
  range_at_inst ra lbl idx =
    range_unwrap (df_widen_at NONE ra lbl idx)
End

(* Get range of an operand before instruction at (lbl, idx).
   Matches Python VariableRangeAnalysis.get_range. *)
Definition range_get_range_def:
  range_get_range ra lbl idx op =
    case op of
      Lit v => vr_constant (w2i v)
    | Var v => rs_lookup (range_at_inst ra lbl idx) v
    | Label _ => VR_Top
End
