(*
 * Variable Definition (Reaching Definitions) Analysis — Definitions
 *
 * Ports vyper/venom/analysis/var_definition.py to HOL4.
 * Uses df_analyze (generic dataflow framework).
 *
 * Forward dataflow: at each program point, which variables are
 * guaranteed defined on ALL paths from entry.
 *
 * Lattice: (P(all_assignments), ⊇) — top = all_assignments, meet = ∩.
 * Variables can only be removed during iteration; convergence follows
 * from finite height.
 *
 * TOP-LEVEL:
 *   vardef_analyze         — run analysis via df_analyze Forward
 *   vardef_out_of          — query defined vars at block exit
 *   vardef_at              — query defined vars before an instruction
 *   vardef_transfer        — per-instruction transfer: add inst_defs
 *   vardef_edge_transfer   — edge transfer: identity (no edge-specific flow)
 *   var_assigned_in_block  — v is assigned by some instruction in a block
 *)

Theory varDefDefs
Ancestors
  venomInst cfgDefs dfAnalyzeDefs dfHelperDefs

(* ===== Per-instruction transfer ===== *)

(* Forward transfer: add newly defined variables.
   defs_before → transfer → defs_after.
   Context is unit (no analysis-specific context needed). *)
Definition vardef_transfer_def:
  vardef_transfer (() : unit) (inst : instruction)
                  (defs : string list) =
    list_union defs (inst_defs inst)
End

(* Edge transfer: identity. No edge-specific handling needed.
   (Unlike liveness PHI, var_def doesn't have edge-sensitive flow.) *)
Definition vardef_edge_transfer_def:
  vardef_edge_transfer (() : unit) (src : string) (dst : string)
                       (defs : string list) = defs
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

(* ===== Top-level analysis via df_analyze ===== *)

(* Variable definition analysis via the generic dataflow framework.
   Forward direction, list_intersect join, fn_all_assignments as bottom
   (identity for ∩). Entry block starts with [] (no vars defined). *)
Definition vardef_analyze_def:
  vardef_analyze fn =
    let all_vars = fn_all_assignments fn in
    let entry_val =
      OPTION_MAP (λlbl. (lbl, [] : string list)) (fn_entry_label fn) in
    df_analyze Forward all_vars list_intersect vardef_transfer
              vardef_edge_transfer () entry_val fn
End

(* ===== Query API ===== *)

(* Defined variables at block exit = boundary value (forward). *)
Definition vardef_out_of_def:
  vardef_out_of fn lbl =
    df_boundary (fn_all_assignments fn) (vardef_analyze fn) lbl
End

(* Defined variables before instruction idx in block lbl. *)
Definition vardef_at_def:
  vardef_at fn lbl idx =
    df_at (fn_all_assignments fn) (vardef_analyze fn) lbl idx
End
