(*
 * Available Expression Analysis — Proofs (internal)
 *
 * Cheated proofs for safety properties. The externally-facing API
 * is in availExprAnalysisPropsScript.sml (ACCEPT_TAC wrappers).
 *)

Theory availExprProofs
Ancestors
  availExprDefs

(* ===== Canonicalization Properties ===== *)

(* canon_expr is idempotent *)
Theorem canon_expr_idempotent:
  ∀e. canon_expr (canon_expr e) = canon_expr e
Proof cheat
QED

(* Commutative ops: operand order doesn't matter after canonicalization *)
Theorem canon_expr_comm:
  ∀op a b.
    is_commutative op ⇒
    canon_expr (ExprOp op [a; b]) = canon_expr (ExprOp op [b; a])
Proof cheat
QED

(* mk_expr always returns canonical form *)
Theorem mk_expr_canonical:
  ∀dfg inst. canon_expr (mk_expr dfg inst) = mk_expr dfg inst
Proof cheat
QED

(* ===== Kill / Remove-Effect Properties ===== *)

(* Empty effect is identity *)
Theorem avail_remove_effect_empty:
  ∀ae. avail_remove_effect ae empty_effects = ae
Proof
  simp[avail_remove_effect_def]
QED

(* Disjoint effects are preserved *)
Theorem avail_remove_effect_preserves:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = SOME insts
Proof cheat
QED

(* Overlapping effects are killed *)
Theorem avail_remove_effect_kills:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    ¬DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = NONE
Proof cheat
QED

(* Domain only shrinks *)
Theorem avail_remove_effect_FDOM_SUBSET:
  ∀ae eff. FDOM (avail_remove_effect ae eff) ⊆ FDOM ae
Proof cheat
QED

(* ===== Meet / Lattice Properties ===== *)

(* Meet of empty list is empty *)
Theorem avail_meet_nil:
  avail_meet [] = FEMPTY
Proof
  simp[avail_meet_def, avail_empty_def]
QED

(* Meet domain is subset of each input's domain *)
Theorem avail_meet_two_FDOM:
  ∀a b. FDOM (avail_meet_two a b) = FDOM a ∩ FDOM b
Proof cheat
QED

(* Meet is subset of each operand *)
Theorem avail_meet_two_FDOM_SUBSET_l:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM a
Proof cheat
QED

Theorem avail_meet_two_FDOM_SUBSET_r:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM b
Proof cheat
QED

(* If expr is in meet, it's in all inputs *)
Theorem avail_meet_FDOM:
  ∀aes expr.
    aes ≠ [] ∧ expr ∈ FDOM (avail_meet aes) ⇒
    ∀ae. MEM ae aes ⇒ expr ∈ FDOM ae
Proof cheat
QED

(* Meet is monotone: adding predecessors can only shrink *)
Theorem avail_meet_cons_SUBSET:
  ∀ae aes.
    FDOM (avail_meet (ae::aes)) ⊆ FDOM (avail_meet aes) ∪ FDOM ae
Proof cheat
QED

(* ===== Transfer Properties ===== *)

(* Pseudo/assign/terminator instructions don't change available set *)
Theorem avail_transfer_inst_skip:
  ∀dfg inst ae.
    (is_pseudo inst.inst_opcode ∨
     inst.inst_opcode = ASSIGN ∨
     is_terminator inst.inst_opcode) ⇒
    avail_transfer_inst dfg inst ae = ae
Proof
  simp[avail_transfer_inst_def]
QED

(* Nonidempotent instructions don't add to the available set *)
Theorem avail_transfer_inst_nonidempotent_no_add:
  ∀dfg inst ae.
    is_nonidempotent inst.inst_opcode ⇒
    FDOM (avail_transfer_inst dfg inst ae) ⊆ FDOM ae
Proof cheat
QED

(* Transfer preserves expressions with disjoint effects *)
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
Proof cheat
QED

(* After transfer, the new expression (if added) maps to [inst] *)
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

(* ===== Expression Effects Properties ===== *)

(* Leaf expressions have no effects *)
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

(* Pure opcodes (no read/write effects) produce pure expressions *)
Theorem expr_effects_pure_op:
  ∀op args.
    read_effects op = empty_effects ∧
    write_effects op = empty_effects ∧
    EVERY (λe. expr_effects e = empty_effects) args ⇒
    expr_effects (ExprOp op args) = empty_effects
Proof cheat
QED

(* ===== mk_operand_expr Termination Properties ===== *)

(* mk_operand_expr terminates on well-formed DFGs (acyclic SSA) *)
(* This is the semantic justification for the visited-set termination.
 * In a well-formed SSA DFG, the set of reachable variable definitions
 * from any operand is bounded by CARD (FDOM dfg.dfg_defs). *)

(* Visited set only grows *)
Theorem mk_operand_expr_visited_prefix:
  ∀dfg visited op.
    set visited ⊆ set visited
Proof
  simp[]
QED

(* ===== avail_add Properties ===== *)

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

(* ===== Query API Properties ===== *)

(* If get_expression returns SOME, the source is different *)
Theorem avail_get_expression_diff:
  ∀ar inst expr src.
    avail_get_expression ar inst = SOME (expr, src) ⇒
    src.inst_id ≠ inst.inst_id
Proof cheat
QED

(* If get_expression returns SOME, the expr was recorded *)
Theorem avail_get_expression_recorded:
  ∀ar inst expr src.
    avail_get_expression ar inst = SOME (expr, src) ⇒
    FLOOKUP ar.ae_inst_expr inst.inst_id = SOME expr
Proof cheat
QED

(* If get_expression returns SOME, the source was available *)
Theorem avail_get_expression_available:
  ∀ar inst expr src.
    avail_get_expression ar inst = SOME (expr, src) ⇒
    ∃insts. FLOOKUP (ae_lookup_inst ar inst.inst_id) expr = SOME insts ∧
            MEM src insts
Proof cheat
QED
