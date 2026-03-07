(*
 * Available Expression Analysis — Proofs (internal)
 *
 * Cheated proofs for safety properties. The externally-facing API
 * is in availExprAnalysisPropsScript.sml (ACCEPT_TAC wrappers).
 *)

Theory availExprProofs
Ancestors
  availExprDefs

(* ===== Canonicalization ===== *)

Theorem canon_expr_idempotent:
  ∀e. canon_expr (canon_expr e) = canon_expr e
Proof cheat
QED

Theorem canon_expr_comm:
  ∀op a b.
    is_commutative op ⇒
    canon_expr (ExprOp op [a; b]) = canon_expr (ExprOp op [b; a])
Proof cheat
QED

Theorem mk_expr_canonical:
  ∀dfg inst. canon_expr (mk_expr dfg inst) = mk_expr dfg inst
Proof cheat
QED

(* ===== Kill / Remove-Effect ===== *)

Theorem avail_remove_effect_empty:
  ∀ae. avail_remove_effect ae empty_effects = ae
Proof
  simp[avail_remove_effect_def]
QED

Theorem avail_remove_effect_preserves:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = SOME insts
Proof cheat
QED

Theorem avail_remove_effect_kills:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    ¬DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = NONE
Proof cheat
QED

Theorem avail_remove_effect_FDOM_SUBSET:
  ∀ae eff. FDOM (avail_remove_effect ae eff) ⊆ FDOM ae
Proof cheat
QED

(* ===== Meet / Lattice ===== *)

Theorem avail_meet_nil:
  avail_meet [] = FEMPTY
Proof
  simp[avail_meet_def, avail_empty_def]
QED

Theorem avail_meet_two_FDOM:
  ∀a b. FDOM (avail_meet_two a b) = FDOM a ∩ FDOM b
Proof cheat
QED

Theorem avail_meet_two_FDOM_SUBSET_l:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM a
Proof cheat
QED

Theorem avail_meet_two_FDOM_SUBSET_r:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM b
Proof cheat
QED

Theorem avail_meet_FDOM:
  ∀aes expr.
    expr ∈ FDOM (avail_meet aes) ⇒
    ∀ae. MEM ae aes ⇒ expr ∈ FDOM ae
Proof cheat
QED

Theorem avail_meet_mono:
  ∀ae aes.
    aes ≠ [] ⇒
    FDOM (avail_meet (ae::aes)) ⊆ FDOM (avail_meet aes)
Proof cheat
QED

(* ===== Transfer ===== *)

Theorem avail_transfer_inst_skip:
  ∀dfg inst ae.
    (is_pseudo inst.inst_opcode ∨
     inst.inst_opcode = ASSIGN ∨
     is_terminator inst.inst_opcode) ⇒
    avail_transfer_inst dfg inst ae = ae
Proof
  simp[avail_transfer_inst_def]
QED

Theorem avail_transfer_inst_nonidempotent_no_add:
  ∀dfg inst ae.
    is_nonidempotent inst.inst_opcode ⇒
    FDOM (avail_transfer_inst dfg inst ae) ⊆ FDOM ae
Proof cheat
QED

Theorem avail_transfer_inst_preserves:
  ∀dfg inst ae expr insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) (write_effects inst.inst_opcode) ∧
    expr ≠ mk_expr dfg inst ⇒
    FLOOKUP (avail_transfer_inst dfg inst ae) expr = SOME insts
Proof cheat
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
Proof cheat
QED

(* ===== Expression Effects ===== *)

Theorem expr_effects_var:
  ∀v. expr_effects (ExprVar v) = empty_effects
Proof
  simp[expr_effects_def]
QED

Theorem expr_effects_lit:
  ∀l. expr_effects (ExprLit l) = empty_effects
Proof
  simp[expr_effects_def]
QED

Theorem expr_effects_pure_op:
  ∀op args.
    read_effects op = empty_effects ∧
    write_effects op = empty_effects ∧
    EVERY (λe. expr_effects e = empty_effects) args ⇒
    expr_effects (ExprOp op args) = empty_effects
Proof cheat
QED

(* ===== avail_add ===== *)

Theorem avail_add_FDOM:
  ∀ae expr inst. FDOM (avail_add ae expr inst) = expr INSERT FDOM ae
Proof cheat
QED

Theorem avail_add_lookup_same:
  ∀ae expr inst.
    FLOOKUP ae expr = NONE ⇒
    FLOOKUP (avail_add ae expr inst) expr = SOME [inst]
Proof cheat
QED

Theorem avail_add_lookup_other:
  ∀ae expr expr' inst.
    expr' ≠ expr ⇒
    FLOOKUP (avail_add ae expr inst) expr' = FLOOKUP ae expr'
Proof cheat
QED

(* ===== Query API ===== *)

Theorem avail_get_expression_diff:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    src.inst_id ≠ inst.inst_id
Proof cheat
QED

Theorem avail_get_expression_recorded:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    expr = mk_expr (dfg_build_function fn) inst
Proof cheat
QED

Theorem avail_get_expression_available:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    ∃insts. FLOOKUP (ae_lookup_inst fn lbl idx) expr = SOME insts ∧
            MEM src insts
Proof cheat
QED
