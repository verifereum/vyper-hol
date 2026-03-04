(*
 * Variable Definition (Reaching Definitions) Analysis — Definitions
 *
 * Ports vyper/venom/analysis/var_definition.py to HOL4.
 *
 * Forward dataflow: at each program point, which variables are
 * guaranteed defined on ALL paths from entry.
 *
 * Lattice: (P(all_assignments), ⊇) — top = all_assignments, meet = ∩.
 * Variables can only be removed during iteration; convergence follows
 * from finite height.
 *
 * Used by check_venom.py to validate that all used variables are defined.
 *
 * TOP-LEVEL:
 *   vardef_result          — record: vd_out (per-block), vd_inst (per-inst)
 *   vardef_analyze         — run full analysis via wl_iterate
 *   vardef_out_of          — query defined vars at block exit
 *   vardef_at              — query defined vars before an instruction
 *   fn_all_assignments     — all variables assigned anywhere in the function
 *   var_assigned_in_block  — v is assigned by some instruction in a block
 *   is_cfg_path           — block-level path: consecutive labels are CFG edges
 *
 * Helper:
 *   vardef_process         — transfer function for one block (for wl_iterate)
 *   vardef_init            — initial state (all_assignments everywhere)
 *)

Theory varDefDefs
Ancestors
  venomInst cfgDefs worklistDefs dfHelperDefs

(* ===== All assigned variable names in a function ===== *)

Definition fn_all_assignments_def:
  fn_all_assignments fn =
    nub (FLAT (MAP (λbb.
      FLAT (MAP inst_defs bb.bb_instructions))
      fn.fn_blocks))
End

(* ===== Result type ===== *)

Datatype:
  vardef_result = <|
    vd_out  : (string, string list) fmap;
    vd_inst : (num, string list) fmap
  |>
End

(* ===== Query API ===== *)

(* Defined variables at block exit. [] if block absent. *)
Definition vardef_out_of_def:
  vardef_out_of vd lbl = fmap_lookup_list vd.vd_out lbl
End

(* Defined variables before instruction inst_id. [] if absent. *)
Definition vardef_at_def:
  vardef_at vd inst_id = fmap_lookup_list vd.vd_inst inst_id
End

(* ===== Transfer function for one block ===== *)

(* Process one block: intersect predecessor outputs, then accumulate
   instruction outputs forward through the block.
   Matches Python _handle_bb exactly. *)
Definition vardef_process_def:
  vardef_process cfg fn lbl (vd : vardef_result) =
    case lookup_block lbl fn.fn_blocks of
      NONE => vd
    | SOME bb =>
        let preds = cfg_preds_of cfg lbl in
        let input_defs =
          if NULL preds then []
          else list_intersect_all
                 (MAP (λp. fmap_lookup_list vd.vd_out p) preds) in
        let (imap, exit_defs) =
          FOLDL (λ(im, defs) inst.
            (im |+ (inst.inst_id, defs),
             list_union defs (inst_defs inst)))
          (vd.vd_inst, input_defs) bb.bb_instructions in
        vd with <| vd_out := vd.vd_out |+ (lbl, exit_defs);
                    vd_inst := imap |>
End

(* ===== Initialization ===== *)

(* Python: defined_vars_bb = {bb: all_variables.copy() for bb in bbs}
   Top of lattice: every block starts with all vars defined. *)
Definition vardef_init_def:
  vardef_init fn =
    let all_vars = fn_all_assignments fn in
    <| vd_out :=
         FOLDL (λm bb. m |+ (bb.bb_label, all_vars))
               FEMPTY fn.fn_blocks;
       vd_inst := FEMPTY |>
End

(* ===== Soundness predicates ===== *)

(* Variable v is assigned by some instruction in block lbl. *)
Definition var_assigned_in_block_def:
  var_assigned_in_block fn lbl v =
    case lookup_block lbl fn.fn_blocks of
      NONE => F
    | SOME bb =>
        EXISTS (λinst. MEM v (inst_defs inst)) bb.bb_instructions
End

(* A block-level CFG path: consecutive labels are CFG edges. *)
Definition is_cfg_path_def:
  is_cfg_path cfg [] = T /\
  is_cfg_path cfg [l] = T /\
  is_cfg_path cfg (l1 :: l2 :: rest) =
    (MEM l2 (cfg_succs_of cfg l1) /\ is_cfg_path cfg (l2 :: rest))
End

(* ===== Top-level analysis ===== *)

(* Worklist-based iteration matching the Python implementation.
   deps = cfg_succs_of: when a block's output changes, re-process successors.
   Initial worklist = all block labels. *)
Definition vardef_analyze_def:
  vardef_analyze fn =
    let cfg = cfg_analyze fn in
    let process = vardef_process cfg fn in
    let deps = cfg_succs_of cfg in
    let vd0 = vardef_init fn in
    let wl = fn_labels fn in
    SND (wl_iterate process deps wl vd0)
End
