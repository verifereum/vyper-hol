(*
 * Liveness Analysis — Definitions
 *
 * Backward liveness analysis via generic df_analyze framework.
 *
 * TOP-LEVEL:
 *   liveness_analyze      — run full liveness analysis on a function
 *   live_vars_at          — query live variables before instruction idx
 *   input_vars_from       — live vars entering target from source (PHI-aware)
 *
 * Soundness statement helpers:
 *   cfg_exec_path         — valid execution path through CFG
 *   var_used_at           — variable read at position
 *   var_defined_at        — variable written at position
 *   used_before_defined   — used before redefined along path
 *   fn_all_vars           — all variable names in a function
 *)

Theory livenessDefs
Ancestors
  list finite_map pred_set
  venomInst cfgDefs dfAnalyzeDefs dfHelperDefs

(* ==========================================================================
   Transfer function: (live \ defs) ∪ uses
   ========================================================================== *)

Definition live_update_def:
  live_update defs uses live =
    let live' = FILTER (λv. ¬MEM v defs) live in
    live' ++ FILTER (λv. ¬MEM v live') uses
End

Definition liveness_transfer_def:
  liveness_transfer (bbs : basic_block list) (inst : instruction)
                    (live : string list) =
    live_update (inst_defs inst) (inst_uses inst) live
End

(* ==========================================================================
   PHI-aware edge transfer
   ========================================================================== *)

Definition input_vars_from_def:
  input_vars_from src_label target_instrs base_liveness =
    FOLDL
      (λlive inst.
        if inst.inst_opcode ≠ PHI then live
        else
          let pairs = phi_pairs inst.inst_operands in
          let add_vars = MAP SND (FILTER (λ(l,v). l = src_label) pairs) in
          let rm_vars  = MAP SND (FILTER (λ(l,v). l ≠ src_label) pairs) in
          let live' = FILTER (λv. ¬MEM v rm_vars) live in
          list_union live' add_vars)
      base_liveness
      target_instrs
End

Definition liveness_edge_transfer_def:
  liveness_edge_transfer (bbs : basic_block list) succ_lbl cur_lbl
                         (live : string list) =
    case lookup_block succ_lbl bbs of
      NONE => live
    | SOME succ_bb =>
        input_vars_from cur_lbl succ_bb.bb_instructions live
End

(* ==========================================================================
   Top-level analysis (backward, set union lattice)
   ========================================================================== *)

Definition liveness_analyze_def:
  liveness_analyze fn =
    df_analyze Backward [] list_union liveness_transfer
              liveness_edge_transfer fn.fn_blocks NONE fn
End

(* ==========================================================================
   Query API
   ========================================================================== *)

(* Live variables before instruction idx in block lbl.
   idx = LENGTH instrs gives the exit liveness (live-out). *)
Definition live_vars_at_def:
  live_vars_at st lbl idx = df_at [] st lbl idx
End

(* ==========================================================================
   Variable universe (for boundedness statement)
   ========================================================================== *)

Definition fn_all_vars_def:
  fn_all_vars bbs =
    FLAT (MAP (λbb.
      FLAT (MAP (λinst. inst_uses inst ++ inst_defs inst)
                bb.bb_instructions))
      bbs)
End

(* ==========================================================================
   Execution path and use/def at a point (for soundness statement)
   ========================================================================== *)

Definition cfg_exec_path_def:
  cfg_exec_path cfg ([] : (string # num) list) = T ∧
  cfg_exec_path cfg [(lbl, idx)] = T ∧
  cfg_exec_path cfg ((lbl1, idx1) :: (lbl2, idx2) :: rest) =
    (((lbl1 = lbl2 ∧ idx2 = idx1 + 1) ∨
      (MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0)) ∧
     cfg_exec_path cfg ((lbl2, idx2) :: rest))
End

Definition var_used_at_def:
  var_used_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      MEM v (inst_uses inst))
End

Definition var_defined_at_def:
  var_defined_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      inst.inst_opcode ≠ PHI ∧
      MEM v (inst_defs inst))
End

Definition used_before_defined_def:
  used_before_defined bbs v positions =
    (∃k. k < LENGTH positions ∧
         var_used_at bbs (FST (EL k positions)) (SND (EL k positions)) v ∧
         ∀j. j < k ==>
             ¬var_defined_at bbs (FST (EL j positions))
                                 (SND (EL j positions)) v)
End
