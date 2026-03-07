(*
 * Available Expression Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors availExprAnalysisProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   canon_expr_idempotent          — canon is idempotent
 *   canon_expr_comm                — commutative binary ops: order-independent
 *   mk_expr_canonical              — mk_expr returns canonical form
 *   avail_remove_effect_empty      — empty effect is identity
 *   avail_remove_effect_preserves  — disjoint effects preserved
 *   avail_remove_effect_kills      — overlapping effects killed
 *   avail_remove_effect_FDOM_SUBSET — domain only shrinks
 *   avail_meet_two_FDOM            — meet domain = intersection of input domains
 *   avail_transfer_inst_skip       — pseudo/assign/terminator: unchanged
 *   avail_transfer_inst_nonidempotent_no_add — nonidempotent: domain doesn't grow
 *   avail_transfer_inst_preserves  — disjoint effects + distinct expr: preserved
 *   avail_transfer_inst_adds       — fresh expression maps to [inst]
 *   expr_effects_var/lit           — leaves have no effects
 *   expr_effects_pure_op           — pure op + pure args ⇒ pure expr
 *   avail_add_FDOM                 — domain = expr INSERT original
 *   avail_add_lookup_same          — fresh add maps to [inst]
 *   avail_add_lookup_other         — add doesn't affect other keys
 *   avail_get_expression_diff      — source ≠ target
 *   avail_get_expression_recorded  — expression was recorded
 *   avail_get_expression_available — source was available
 *)

Theory availExprAnalysisProps
Ancestors
  availExprDefs availExprProofs

(* ===== Canonicalization ===== *)

(* canon_expr is idempotent *)
Theorem canon_expr_idempotent:
  ∀e. canon_expr (canon_expr e) = canon_expr e
Proof ACCEPT_TAC availExprProofsTheory.canon_expr_idempotent
QED

(* Commutative binary ops: operand order doesn't matter after canonicalization *)
Theorem canon_expr_comm:
  ∀op a b.
    is_commutative op ⇒
    canon_expr (ExprOp op [a; b]) = canon_expr (ExprOp op [b; a])
Proof ACCEPT_TAC availExprProofsTheory.canon_expr_comm
QED

(* mk_expr always returns canonical form *)
Theorem mk_expr_canonical:
  ∀dfg inst. canon_expr (mk_expr dfg inst) = mk_expr dfg inst
Proof ACCEPT_TAC availExprProofsTheory.mk_expr_canonical
QED

(* ===== Kill / Remove-Effect ===== *)

(* Removing empty effects is identity *)
Theorem avail_remove_effect_empty:
  ∀ae. avail_remove_effect ae empty_effects = ae
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_empty
QED

(* Expressions with effects disjoint from the removed set are preserved *)
Theorem avail_remove_effect_preserves:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = SOME insts
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_preserves
QED

(* Expressions with overlapping effects are killed *)
Theorem avail_remove_effect_kills:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    ¬DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = NONE
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_kills
QED

(* Remove-effect domain is a subset of the original *)
Theorem avail_remove_effect_FDOM_SUBSET:
  ∀ae eff. FDOM (avail_remove_effect ae eff) ⊆ FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_remove_effect_FDOM_SUBSET
QED

(* ===== Meet / Lattice ===== *)

(* Binary meet domain equals intersection of input domains *)
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

(* ===== Transfer ===== *)

(* Pseudo, ASSIGN, and terminator instructions leave the available set unchanged *)
Theorem avail_transfer_inst_skip:
  ∀dfg inst ae.
    (is_pseudo inst.inst_opcode ∨
     inst.inst_opcode = ASSIGN ∨
     is_terminator inst.inst_opcode) ⇒
    avail_transfer_inst dfg inst ae = ae
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_skip
QED

(* Nonidempotent instructions don't grow the available set domain *)
Theorem avail_transfer_inst_nonidempotent_no_add:
  ∀dfg inst ae.
    is_nonidempotent inst.inst_opcode ⇒
    FDOM (avail_transfer_inst dfg inst ae) ⊆ FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_nonidempotent_no_add
QED

(* Transfer preserves expressions with disjoint effects, provided the
 * expression is distinct from the instruction's own computed expression *)
Theorem avail_transfer_inst_preserves:
  ∀dfg inst ae expr insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) (write_effects inst.inst_opcode) ∧
    expr ≠ mk_expr dfg inst ⇒
    FLOOKUP (avail_transfer_inst dfg inst ae) expr = SOME insts
Proof ACCEPT_TAC availExprProofsTheory.avail_transfer_inst_preserves
QED

(* For a non-pseudo, non-assign, non-terminator, single-output, idempotent,
 * non-conflicting instruction: if its expression is fresh (not already in
 * the post-removal map), transfer maps it to [inst] *)
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

(* ===== Expression Effects ===== *)

(* Variable and literal leaves have no effects *)
Theorem expr_effects_var:
  ∀v. expr_effects (ExprVar v) = empty_effects
Proof ACCEPT_TAC availExprProofsTheory.expr_effects_var
QED

Theorem expr_effects_lit:
  ∀l. expr_effects (ExprLit l) = empty_effects
Proof ACCEPT_TAC availExprProofsTheory.expr_effects_lit
QED

(* Pure opcode (no read/write effects) with pure args produces a pure expression *)
Theorem expr_effects_pure_op:
  ∀op args.
    read_effects op = empty_effects ∧
    write_effects op = empty_effects ∧
    EVERY (λe. expr_effects e = empty_effects) args ⇒
    expr_effects (ExprOp op args) = empty_effects
Proof ACCEPT_TAC availExprProofsTheory.expr_effects_pure_op
QED

(* ===== avail_add ===== *)

(* Domain after add is expr INSERT original domain *)
Theorem avail_add_FDOM:
  ∀ae expr inst. FDOM (avail_add ae expr inst) = expr INSERT FDOM ae
Proof ACCEPT_TAC availExprProofsTheory.avail_add_FDOM
QED

(* Adding a fresh expression maps it to [inst] *)
Theorem avail_add_lookup_same:
  ∀ae expr inst.
    FLOOKUP ae expr = NONE ⇒
    FLOOKUP (avail_add ae expr inst) expr = SOME [inst]
Proof ACCEPT_TAC availExprProofsTheory.avail_add_lookup_same
QED

(* Add doesn't affect other keys *)
Theorem avail_add_lookup_other:
  ∀ae expr expr' inst.
    expr' ≠ expr ⇒
    FLOOKUP (avail_add ae expr inst) expr' = FLOOKUP ae expr'
Proof ACCEPT_TAC availExprProofsTheory.avail_add_lookup_other
QED

(* ===== Query API ===== *)

(* If get_expression returns SOME, the source instruction differs from the target *)
Theorem avail_get_expression_diff:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    src.inst_id ≠ inst.inst_id
Proof ACCEPT_TAC availExprProofsTheory.avail_get_expression_diff
QED

(* If get_expression returns SOME, the expression matches mk_expr *)
Theorem avail_get_expression_recorded:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    expr = mk_expr (dfg_build_function fn) inst
Proof ACCEPT_TAC availExprProofsTheory.avail_get_expression_recorded
QED

(* If get_expression returns SOME, the source is in the available set at that point *)
Theorem avail_get_expression_available:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    ∃insts. FLOOKUP (ae_lookup_inst fn lbl idx) expr = SOME insts ∧
            MEM src insts
Proof ACCEPT_TAC availExprProofsTheory.avail_get_expression_available
QED
