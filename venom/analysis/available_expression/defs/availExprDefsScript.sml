(*
 * Available Expression Analysis — Definitions
 *
 * Ports vyper/venom/analysis/available_expression.py to HOL4.
 *
 * TOP-LEVEL:
 *   avail_expr, canon_expr, mk_expr, avail_exprs,
 *   avail_transfer_inst, avail_analyze, avail_get_expression
 *
 * Helper:
 *   is_pseudo, expr_leq, mk_operand_expr, mk_inst_expr,
 *   expr_effects, avail_remove_effect, avail_add, avail_get_source,
 *   avail_meet_two, avail_meet_opt, avail_transfer_opt,
 *   avail_edge_transfer, avail_unwrap
 *)

Theory availExprDefs
Ancestors
  venomEffects dfgDefs cfgDefs dfAnalyzeDefs

(* is_pseudo from venomInstTheory *)

(* ===== Expression Tree ===== *)

Datatype:
  avail_expr =
    ExprVar string
  | ExprLit bytes32
  | ExprOp opcode (avail_expr list)
End

(* Total order for canonical sorting *)
Definition expr_leq_def:
  (expr_leq (ExprVar v1) (ExprVar v2) = (v1 <= v2)) /\
  (expr_leq (ExprVar _) _ = T) /\
  (expr_leq (ExprLit _) (ExprVar _) = F) /\
  (expr_leq (ExprLit l1) (ExprLit l2) = (w2n l1 <= w2n l2)) /\
  (expr_leq (ExprLit _) (ExprOp _ _) = T) /\
  (expr_leq (ExprOp _ _) (ExprVar _) = F) /\
  (expr_leq (ExprOp _ _) (ExprLit _) = F) /\
  (expr_leq (ExprOp op1 args1) (ExprOp op2 args2) =
    if opcode2num op1 < opcode2num op2 then T
    else if opcode2num op1 > opcode2num op2 then F
    else expr_list_leq args1 args2) /\
  (expr_list_leq [] _ = T) /\
  (expr_list_leq _ [] = F) /\
  (expr_list_leq (e1::es1) (e2::es2) =
    if e1 = e2 then expr_list_leq es1 es2
    else expr_leq e1 e2)
End

(* Canonical form: sort operands for commutative ops *)
Definition canon_expr_def:
  (canon_expr (ExprOp op args) =
    let args' = MAP canon_expr args in
    if is_commutative op then ExprOp op (QSORT expr_leq args')
    else ExprOp op args') /\
  (canon_expr e = e)
Termination
  WF_REL_TAC `measure avail_expr_size` >>
  rpt strip_tac >>
  Induct_on `args` >> rw[fetch "-" "avail_expr_size_def"] >>
  res_tac >> simp[]
End

(* ===== Build Expression from Instruction + DFG ===== *)

(* Recursion through DFG is bounded by instruction count (SSA: each var
 * has one def, PHI breaks cycles). visited set tracks seen variables. *)
Definition mk_operand_expr_def:
  (mk_operand_expr dfg visited (Lit v) = ExprLit v) /\
  (mk_operand_expr dfg visited (Label l) = ExprVar l) /\
  (mk_operand_expr dfg visited (Var v) =
    if MEM v visited then ExprVar v
    else case dfg_get_def dfg v of
      NONE => ExprVar v
    | SOME def_inst =>
        if is_pseudo def_inst.inst_opcode then ExprVar v
        else if def_inst.inst_opcode = ASSIGN then
          (case def_inst.inst_operands of
            [src] => mk_operand_expr dfg (v::visited) src
          | _ => ExprVar v)
        else if LENGTH def_inst.inst_outputs > 1 then ExprVar v
        else mk_inst_expr dfg (v::visited) def_inst) /\
  (mk_inst_expr dfg visited inst =
    let args = MAP (mk_operand_expr dfg visited) inst.inst_operands in
    canon_expr (ExprOp inst.inst_opcode args))
Termination
  WF_REL_TAC `measure (λx. case x of
    INL (dfg, visited, op) =>
      CARD (FDOM dfg.dfg_defs DIFF set visited) * 2 + 1
  | INR (dfg, visited, inst) =>
      CARD (FDOM dfg.dfg_defs DIFF set visited) * 2 + 2)` >>
  cheat
End

Definition mk_expr_def:
  mk_expr dfg inst = mk_inst_expr dfg [] inst
End

(* ===== Expression Effects ===== *)

Definition expr_effects_def:
  (expr_effects (ExprVar _) = empty_effects) /\
  (expr_effects (ExprLit _) = empty_effects) /\
  (expr_effects (ExprOp op args) =
    (read_effects op UNION write_effects op) UNION
    BIGUNION (set (MAP expr_effects args)))
Termination
  WF_REL_TAC `measure avail_expr_size` >>
  rpt strip_tac >>
  Induct_on `args` >> rw[fetch "-" "avail_expr_size_def"] >>
  res_tac >> simp[]
End

(* ===== Available Expression Lattice ===== *)

Type avail_exprs = ``:(avail_expr, instruction list) fmap``

Definition avail_empty_def:
  avail_empty : avail_exprs = FEMPTY
End

Definition avail_add_def:
  avail_add (ae : avail_exprs) expr inst =
    case FLOOKUP ae expr of
      NONE => ae |+ (expr, [inst])
    | SOME insts => ae |+ (expr, insts ++ [inst])
End

Definition avail_remove_effect_def:
  avail_remove_effect (ae : avail_exprs) (eff : effects) =
    if eff = empty_effects then ae
    else DRESTRICT ae
      { expr | expr IN FDOM ae /\
               DISJOINT (expr_effects expr) eff }
End

Definition avail_meet_two_def:
  avail_meet_two (a : avail_exprs) (b : avail_exprs) =
    FUN_FMAP
      (λexpr.
        case (FLOOKUP a expr, FLOOKUP b expr) of
          (SOME insts_a, SOME insts_b) =>
            FILTER (λi. MEM i insts_b) insts_a
        | _ => [])
      (FDOM a INTER FDOM b)
End

Definition avail_get_source_def:
  avail_get_source (ae : avail_exprs) expr =
    case FLOOKUP ae expr of
      NONE => NONE
    | SOME [] => NONE
    | SOME (inst :: _) => SOME inst
End

(* ===== Transfer Function ===== *)

Definition avail_transfer_inst_def:
  avail_transfer_inst dfg inst (ae : avail_exprs) =
    if is_pseudo inst.inst_opcode ∨
       inst.inst_opcode = ASSIGN ∨
       is_terminator inst.inst_opcode then ae
    else if LENGTH inst.inst_outputs > 1 then ae
    else
      let expr = mk_expr dfg inst in
      let we = write_effects inst.inst_opcode in
      let ae' = avail_remove_effect ae we in
      if is_nonidempotent inst.inst_opcode then ae'
      else if has_conflicting_effects inst.inst_opcode then ae'
      else avail_add ae' expr inst
End

(* ===== Option-wrapped lattice for df_analyze ===== *)

(* Meet with option wrapping: NONE = top (all expressions available).
   FOLDL avail_meet_opt NONE [...] gives the intersection of non-NONE values.
   This is needed because avail_meet_two has no finite identity element. *)
Definition avail_meet_opt_def:
  avail_meet_opt NONE x = x ∧
  avail_meet_opt x NONE = x ∧
  avail_meet_opt (SOME a) (SOME b) = SOME (avail_meet_two a b)
End

(* Per-instruction transfer wrapped for option lattice.
   NONE (top = unprocessed) → SOME (transfer starting from empty).
   SOME ae → SOME (transfer ae). *)
Definition avail_transfer_opt_def:
  avail_transfer_opt (d : dfg_analysis) (inst : instruction)
                     (ae_opt : avail_exprs option) =
    case ae_opt of
      NONE => SOME (avail_transfer_inst d inst avail_empty)
    | SOME ae => SOME (avail_transfer_inst d inst ae)
End

(* Edge transfer: identity (no edge-specific handling). *)
Definition avail_edge_transfer_def:
  avail_edge_transfer (d : dfg_analysis) (src : string) (dst : string)
                      (ae_opt : avail_exprs option) = ae_opt
End

(* ===== Top-level analysis via df_analyze ===== *)

(* Available expression analysis via the generic dataflow framework.
   Forward direction, avail_meet_opt join, NONE bottom (= top of lattice).
   Context = dfg (needed by avail_transfer_inst for expression lookup).
   Entry block: SOME avail_empty (no expressions available at entry). *)
Definition avail_analyze_def:
  avail_analyze fn =
    let dfg = dfg_build_function fn in
    let entry_lbl =
      case entry_block fn of
        NONE => ""
      | SOME bb => bb.bb_label in
    df_analyze Forward NONE avail_meet_opt avail_transfer_opt
              avail_edge_transfer dfg
              (SOME (entry_lbl, SOME avail_empty)) fn
End

(* ===== Query API ===== *)

(* Unwrap option lattice value to avail_exprs. *)
Definition avail_unwrap_def:
  avail_unwrap NONE = avail_empty ∧
  avail_unwrap (SOME ae) = ae
End

(* Available expressions at block exit = boundary value. *)
Definition ae_lookup_bb_out_def:
  ae_lookup_bb_out fn lbl =
    avail_unwrap (df_boundary NONE (avail_analyze fn) lbl)
End

(* Available expressions before instruction idx in block lbl. *)
Definition ae_lookup_inst_def:
  ae_lookup_inst fn lbl idx =
    avail_unwrap (df_at NONE (avail_analyze fn) lbl idx)
End

(* Query: find a prior instruction computing the same expression.
   dfg needed to compute mk_expr for the queried instruction. *)
Definition avail_get_expression_def:
  avail_get_expression fn lbl idx inst =
    let dfg = dfg_build_function fn in
    let expr = mk_expr dfg inst in
    let ae = ae_lookup_inst fn lbl idx in
    case avail_get_source ae expr of
      NONE => NONE
    | SOME src =>
        if src.inst_id = inst.inst_id then NONE
        else SOME (expr, src)
End
