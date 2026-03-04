(*
 * Available Expression Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors availExprAnalysisProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   canon_expr_idempotent          — canon is idempotent
 *   canon_expr_comm                — commutative ops are order-independent
 *   mk_expr_canonical              — mk_expr returns canonical form
 *   avail_remove_effect_empty      — empty effect is identity
 *   avail_remove_effect_preserves  — disjoint effects preserved
 *   avail_remove_effect_kills      — overlapping effects killed
 *   avail_remove_effect_FDOM_SUBSET — domain only shrinks
 *   avail_meet_nil                 — meet of [] is FEMPTY
 *   avail_meet_two_FDOM            — meet domain = intersection
 *   avail_meet_FDOM                — meet result in all inputs
 *   avail_transfer_inst_skip       — pseudo/assign/terminator unchanged
 *   avail_transfer_inst_nonidempotent_no_add — nonidempotent doesn't add
 *   avail_transfer_inst_preserves  — disjoint effects preserved through transfer
 *   avail_transfer_inst_adds       — new expression added by transfer
 *   avail_add_FDOM                 — add extends domain
 *   avail_get_expression_diff      — source ≠ target
 *   avail_get_expression_recorded  — expression was recorded
 *   avail_get_expression_available — source was available
 *)

Theory availExprAnalysisProps
Ancestors
  availExprDefs availExprProofs

(* ===== Canonicalization ===== *)

Theorem canon_expr_idempotent:
  ∀e. canon_expr (canon_expr e) = canon_expr e
Proof ACCEPT_TAC availExprProofsTheory.canon_expr_idempotent
QED

Theorem canon_expr_comm:
  ∀op a b.
    is_commutative op ⇒
    canon_expr (ExprOp op [a; b]) = canon_expr (ExprOp op [b; a])
Proof ACCEPT_TAC availExprProofsTheory.canon_expr_comm
QED

Theorem mk_expr_canonical:
  ∀dfg inst. canon_expr (mk_expr dfg inst) = mk_expr dfg inst
Proof ACCEPT_TAC availExprProofsTheory.mk_expr_canonical
QED

(* ===== Kill / Remove-Effect ===== *)

Theorem avail_remove_effect_empty:
  ∀ae. avail_remove_effect ae empty_effects = ae
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_empty
QED

Theorem avail_remove_effect_preserves:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = SOME insts
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_preserves
QED

Theorem avail_remove_effect_kills:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    ¬DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = NONE
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_kills
QED

Theorem avail_remove_effect_FDOM_SUBSET:
  ∀ae eff. FDOM (avail_remove_effect ae eff) ⊆ FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_FDOM_SUBSET
QED

(* ===== Meet / Lattice ===== *)

Theorem avail_meet_nil:
  avail_meet [] = FEMPTY
Proof ACCEPT_TAC availExprProofsTheory.avail_meet_nil
QED

Theorem avail_meet_two_FDOM:
  ∀a b. FDOM (avail_meet_two a b) = FDOM a ∩ FDOM b
Proof ACCEPT_TAC availExprProofsTheory.avail_meet_two_FDOM
QED

Theorem avail_meet_two_FDOM_SUBSET_l:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM a
Proof ACCEPT_TAC availExprProofsTheory.avail_meet_two_FDOM_SUBSET_l
QED

Theorem avail_meet_two_FDOM_SUBSET_r:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM b
Proof ACCEPT_TAC availExprProofsTheory.avail_meet_two_FDOM_SUBSET_r
QED

Theorem avail_meet_FDOM:
  ∀aes expr.
    aes ≠ [] ∧ expr ∈ FDOM (avail_meet aes) ⇒
    ∀ae. MEM ae aes ⇒ expr ∈ FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_meet_FDOM
QED

(* ===== Transfer ===== *)

Theorem avail_transfer_inst_skip:
  ∀dfg inst ae.
    (is_pseudo inst.inst_opcode ∨
     inst.inst_opcode = ASSIGN ∨
     is_terminator inst.inst_opcode) ⇒
    avail_transfer_inst dfg inst ae = ae
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_skip
QED

Theorem avail_transfer_inst_nonidempotent_no_add:
  ∀dfg inst ae.
    is_nonidempotent inst.inst_opcode ⇒
    FDOM (avail_transfer_inst dfg inst ae) ⊆ FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_nonidempotent_no_add
QED

Theorem avail_transfer_inst_preserves:
  ∀dfg inst ae expr insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) (write_effects inst.inst_opcode) ∧
    ¬is_pseudo inst.inst_opcode ∧
    inst.inst_opcode ≠ ASSIGN ∧
    ¬is_terminator inst.inst_opcode ∧
    LENGTH inst.inst_outputs ≤ 1 ∧
    expr ≠ mk_expr dfg inst ⇒
    FLOOKUP (avail_transfer_inst dfg inst ae) expr = SOME insts
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_preserves
QED

Theorem avail_transfer_inst_adds:
  ∀dfg inst ae.
    ¬is_pseudo inst.inst_opcode ∧
    inst.inst_opcode ≠ ASSIGN ∧
    ¬is_terminator inst.inst_opcode ∧
    LENGTH inst.inst_outputs ≤ 1 ∧
    ¬is_nonidempotent inst.inst_opcode ∧
    ¬has_conflicting_effects inst.inst_opcode ∧
    mk_expr dfg inst ∉ FDOM (avail_remove_effect ae
                               (write_effects inst.inst_opcode)) ⇒
    FLOOKUP (avail_transfer_inst dfg inst ae)
            (mk_expr dfg inst) = SOME [inst]
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_adds
QED

(* ===== avail_add ===== *)

Theorem avail_add_FDOM:
  ∀ae expr inst. FDOM (avail_add ae expr inst) = expr INSERT FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_add_FDOM
QED

(* ===== Query API ===== *)

Theorem avail_get_expression_diff:
  ∀ar inst expr src.
    avail_get_expression ar inst = SOME (expr, src) ⇒
    src.inst_id ≠ inst.inst_id
Proof ACCEPT_TAC availExprProofsTheory.avail_get_expression_diff
QED

Theorem avail_get_expression_recorded:
  ∀ar inst expr src.
    avail_get_expression ar inst = SOME (expr, src) ⇒
    FLOOKUP ar.ae_inst_expr inst.inst_id = SOME expr
Proof ACCEPT_TAC availExprProofsTheory.avail_get_expression_recorded
QED

Theorem avail_get_expression_available:
  ∀ar inst expr src.
    avail_get_expression ar inst = SOME (expr, src) ⇒
    ∃insts. FLOOKUP (ae_lookup_inst ar inst.inst_id) expr = SOME insts ∧
            MEM src insts
Proof ACCEPT_TAC availExprProofsTheory.avail_get_expression_available
QED
