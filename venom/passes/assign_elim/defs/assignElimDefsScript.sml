(*
 * Assign Elimination — Definitions
 *
 * Ports vyper/venom/passes/assign_elimination.py to HOL4.
 *
 * Forwards variables through ASSIGN (copy) instructions:
 *   %x = assign %y  →  replace all uses of %x with %y, NOP the assign.
 *   %x = assign 42  →  replace all uses of %x with 42, NOP the assign.
 *
 * Modeled as a forward dataflow analysis (copy propagation):
 *   Lattice: (string, operand) fmap option
 *     NONE = ⊤ (identity for meet, used for unreached blocks)
 *     SOME fm = concrete copy map
 *   Transfer: on `%x = assign src`, record x ↦ src (unless PHI uses exist).
 *   Transform: for each instruction, replace Var x with the source operand.
 *
 * The OPTION wrapping is needed because copy propagation is a must-analysis
 * (join = intersection). The identity for intersection is ⊤ (universal set),
 * which can't be represented as a finite map. NONE serves as ⊤.
 *
 * Framework: analysis_inst_simulates + df_analysis_pass_correct_sound.
 * Soundness: copy_sound copies s ⟺ ∀x op. FLOOKUP copies x = SOME op ⟹
 *            FLOOKUP s.vs_vars x = eval_operand op s.
 *
 * TOP-LEVEL:
 *   copy_prop_transfer    — dataflow transfer function
 *   copy_prop_join        — lattice join (intersection, NONE = ⊤)
 *   assign_elim_inst      — per-instruction transform
 *   assign_elim_function  — function-level transform
 *)

Theory assignElimDefs
Ancestors
  analysisSimDefs dfAnalyzeDefs passSharedDefs venomExecSemantics

(* ===== Copy propagation lattice ===== *)

(* Maps variable name → source operand (Var or Lit).
   Handles both variable-source and literal-source assigns,
   matching Python's _process_store which handles any operand type. *)
Type copy_lattice = ``:(string, operand) fmap``

(* Join on raw fmaps: intersection — keep only copies that agree *)
Definition copy_agree_def:
  copy_agree (c1 : copy_lattice) (c2 : copy_lattice) x =
    case (FLOOKUP c1 x, FLOOKUP c2 x) of
      (SOME op1, SOME op2) => op1 = op2
    | _ => F
End

Definition copy_prop_join_raw_def:
  copy_prop_join_raw (c1 : copy_lattice) (c2 : copy_lattice) =
    DRESTRICT c1 { x | copy_agree c1 c2 x }
End

(* OPTION-wrapped join: NONE = ⊤ (identity for meet).
   SOME FEMPTY = ⊥ (no copies known, annihilator for meet).
   This is needed because df_analyze uses FOLDL join bottom edge_vals:
   with bottom = NONE, FOLDL meet NONE [v1,v2] = meet(v1,v2). *)
Definition copy_prop_join_def:
  copy_prop_join (c1 : copy_lattice option)
                 (c2 : copy_lattice option) =
    case (c1, c2) of
      (NONE, _) => c2
    | (_, NONE) => c1
    | (SOME m1, SOME m2) => SOME (copy_prop_join_raw m1 m2)
End

(* Transfer: after executing instruction, update copies.
   Unwraps SOME, applies raw transfer, wraps back.
   NONE (⊤) → treat as FEMPTY (function entry has no known copies). *)
Definition copy_prop_transfer_def:
  copy_prop_transfer (phi_vars : string set) inst
                     (copies_opt : copy_lattice option) =
    let copies = case copies_opt of NONE => FEMPTY | SOME c => c in
    let killed = set (inst_defs inst) in
    let copies' = DRESTRICT copies (COMPL killed) in
    SOME (
    if is_forwardable_assign phi_vars inst then
      (case (inst.inst_operands, inst.inst_outputs) of
        ([src_op], [dst]) =>
          (* Transitive: resolve Var source through existing copies.
             Python achieves this by in-place mutation during iteration.
             Lit sources don't need resolution. *)
          let root = case src_op of
                       Var v =>
                         (case FLOOKUP copies' v of
                            SOME r => r | NONE => Var v)
                     | _ => src_op in
          copies' |+ (dst, root)
      | _ => copies')
    else copies')
    (* Non-forwardable: just kill outputs, don't add to copies.
       Applies to non-ASSIGN instructions and ASSIGNs failing guards. *)
End

(* Edge transfer: identity (copies are not branch-dependent) *)
Definition copy_prop_edge_transfer_def:
  copy_prop_edge_transfer (phi_vars : string set) src dst
    (copies_opt : copy_lattice option) = copies_opt
End

(* Top-level analysis.
   bottom = NONE (⊤, identity for meet). Unreached blocks get NONE.
   entry_val = SOME (entry_lbl, SOME FEMPTY): the entry block starts
   with no known copies (SOME FEMPTY), not ⊤. *)
Definition copy_prop_analyze_def:
  copy_prop_analyze fn =
    let pv = phi_used_vars fn in
    let entry_val = OPTION_MAP (\lbl. (lbl, SOME FEMPTY))
                      (fn_entry_label fn) in
    df_analyze Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer pv entry_val fn
End

(* phi_value_vars and phi_used_vars are in passSharedDefs *)

(* ===== Per-instruction transform ===== *)

(* Operand substitution uses subst_op_map from passSharedDefs.
   copy_lattice = (string, operand) fmap matches subst_op_map's type. *)

(* Unwrap option lattice value for transform.
   NONE (⊤ / unreached) → no substitutions (FEMPTY). *)
Definition unwrap_copies_def:
  unwrap_copies (copies_opt : copy_lattice option) =
    case copies_opt of NONE => FEMPTY | SOME c => c
End

(* Substitution only: replace operands according to copy map.
   Does NOT NOP any instructions — both sides write the same outputs.
   Used in per-instruction simulation proof (state_equiv {} works). *)
Definition assign_subst_inst_def:
  assign_subst_inst (copies_opt : copy_lattice option) inst =
    let copies = unwrap_copies copies_opt in
    if inst.inst_opcode = PHI then inst
    else inst with inst_operands :=
      MAP (subst_op_map copies) inst.inst_operands
End

(* Combined substitution + NOP: matches Python's single-pass behavior.
   Forwardable ASSIGNs are NOP'd (output is dead after substitution).
   Non-forwardable: operands substituted, instruction kept.
   Note: NOP decision uses is_forwardable_assign guards directly,
   NOT `FLOOKUP copies out`, because df_at returns the PRE-instruction
   value and in SSA the output hasn't been defined yet. *)
Definition assign_elim_inst_def:
  assign_elim_inst (phi_vars : string set)
                   (copies_opt : copy_lattice option) inst =
    let copies = unwrap_copies copies_opt in
    if inst.inst_opcode = PHI then inst
    else if is_forwardable_assign phi_vars inst then
      mk_nop_inst inst
    else
      inst with inst_operands :=
        MAP (subst_op_map copies) inst.inst_operands
End

(* ===== Function-level transform ===== *)

Definition assign_elim_function_def:
  assign_elim_function fn =
    let result = copy_prop_analyze fn in
    let pv = phi_used_vars fn in
    clear_nops_function
      (analysis_function_transform NONE result
        (\v inst. [assign_elim_inst pv v inst]) fn)
End

(* Variables eliminated by assign_elim: outputs of ASSIGN instructions
   that are NOP'd (both PHI guards pass). These variables are dead after
   copy propagation substitutes all their uses. The correctness theorem
   excludes these from state equivalence since they're never written
   in the transformed function. *)
Definition assign_elim_eliminated_vars_def:
  assign_elim_eliminated_vars fn =
    let pv = phi_used_vars fn in
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        if is_forwardable_assign pv inst then inst.inst_outputs
        else [])
        bb.bb_instructions))
      fn.fn_blocks))
End
