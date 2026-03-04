(*
 * Available Expression Analysis — Definitions
 *
 * Ports vyper/venom/analysis/available_expression.py to HOL4.
 *
 * TOP-LEVEL:
 *   avail_expr, canon_expr, mk_expr, avail_exprs, avail_meet,
 *   avail_transfer_inst, avail_result, avail_analyze, avail_get_expression
 *
 * Helper:
 *   is_pseudo, expr_leq, mk_operand_expr, mk_inst_expr,
 *   expr_effects, avail_remove_effect, avail_add, avail_get_source,
 *   avail_transfer_bb_loop, avail_handle_bb, avail_one_pass, avail_iterate
 *)

Theory availExprDefs
Ancestors
  venomEffects dfgDefs cfgDefs dfIterateDefs

(* ===== Pseudo opcodes ===== *)

Definition is_pseudo_def:
  is_pseudo PHI = T /\
  is_pseudo PARAM = T /\
  is_pseudo _ = F
End

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

Definition avail_meet_def:
  (avail_meet [] = avail_empty) /\
  (avail_meet [ae] = ae) /\
  (avail_meet (ae :: rest) = avail_meet_two ae (avail_meet rest))
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

(* ===== Analysis Result ===== *)

Datatype:
  avail_result = <|
    ae_bb_ins  : (string, avail_exprs) fmap;
    ae_bb_outs : (string, avail_exprs) fmap;
    ae_inst    : (num, avail_exprs) fmap;
    ae_inst_expr : (num, avail_expr) fmap
  |>
End

Definition avail_result_empty_def:
  avail_result_empty = <|
    ae_bb_ins := FEMPTY;
    ae_bb_outs := FEMPTY;
    ae_inst := FEMPTY;
    ae_inst_expr := FEMPTY
  |>
End

Definition ae_lookup_bb_out_def:
  ae_lookup_bb_out ar lbl =
    case FLOOKUP ar.ae_bb_outs lbl of
      NONE => avail_empty
    | SOME ae => ae
End

Definition ae_lookup_bb_in_def:
  ae_lookup_bb_in ar lbl =
    case FLOOKUP ar.ae_bb_ins lbl of
      NONE => avail_empty
    | SOME ae => ae
End

Definition ae_lookup_inst_def:
  ae_lookup_inst ar inst_id =
    case FLOOKUP ar.ae_inst inst_id of
      NONE => avail_empty
    | SOME ae => ae
End

(* ===== Per-Block Transfer ===== *)

Definition avail_transfer_bb_loop_def:
  (avail_transfer_bb_loop dfg [] ae imap emap = (ae, imap, emap)) /\
  (avail_transfer_bb_loop dfg (inst::rest) ae imap emap =
    let imap' = imap |+ (inst.inst_id, ae) in
    let expr = mk_expr dfg inst in
    let emap' = emap |+ (inst.inst_id, expr) in
    let ae' = avail_transfer_inst dfg inst ae in
    avail_transfer_bb_loop dfg rest ae' imap' emap')
End

(* ===== Worklist-Based Analysis ===== *)

Definition avail_handle_bb_def:
  avail_handle_bb cfg dfg fn ar (bb : basic_block) =
    let preds = cfg_preds_of cfg bb.bb_label in
    let pred_outs = MAP (ae_lookup_bb_out ar) preds in
    let entry_ae = avail_meet pred_outs in
    let old_in = ae_lookup_bb_in ar bb.bb_label in
    if entry_ae = old_in ∧ bb.bb_label IN FDOM ar.ae_bb_ins then
      (F, ar)
    else
      let ar' = ar with ae_bb_ins := ar.ae_bb_ins |+ (bb.bb_label, entry_ae) in
      let (exit_ae, imap, emap) =
        avail_transfer_bb_loop dfg bb.bb_instructions entry_ae
          ar'.ae_inst ar'.ae_inst_expr in
      let ar'' = ar' with <|
        ae_bb_outs := ar'.ae_bb_outs |+ (bb.bb_label, exit_ae);
        ae_inst := imap;
        ae_inst_expr := emap
      |> in
      let old_out = ae_lookup_bb_out ar bb.bb_label in
      (exit_ae <> old_out ∨ bb.bb_label NOTIN FDOM ar.ae_bb_outs, ar'')
End

Definition avail_one_pass_def:
  (avail_one_pass cfg dfg fn ar [] = (ar, [])) /\
  (avail_one_pass cfg dfg fn ar (lbl::rest) =
    case lookup_block lbl fn.fn_blocks of
      NONE => avail_one_pass cfg dfg fn ar rest
    | SOME bb =>
        let (changed, ar') = avail_handle_bb cfg dfg fn ar bb in
        let (ar'', more) = avail_one_pass cfg dfg fn ar' rest in
        if changed then
          (ar'', cfg_succs_of cfg lbl ++ more)
        else (ar'', more))
End

Definition avail_iterate_def:
  (avail_iterate cfg dfg fn ar (0:num) worklist = ar) /\
  (avail_iterate cfg dfg fn ar (SUC n) [] = ar) /\
  (avail_iterate cfg dfg fn ar (SUC n) (lbl::rest) =
    let (ar', new_wl) = avail_one_pass cfg dfg fn ar (lbl::rest) in
    if ar' = ar then ar
    else avail_iterate cfg dfg fn ar' n new_wl)
End

(* ===== Top-Level ===== *)

Definition avail_analyze_def:
  avail_analyze fn iter_fuel =
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let ar0 = avail_result_empty in
    let worklist = fn_labels fn in
    avail_iterate cfg dfg fn ar0 iter_fuel worklist
End

(* ===== Query API ===== *)

Definition avail_get_expression_def:
  avail_get_expression ar inst =
    case FLOOKUP ar.ae_inst_expr inst.inst_id of
      NONE => NONE
    | SOME expr =>
        let ae = ae_lookup_inst ar inst.inst_id in
        case avail_get_source ae expr of
          NONE => NONE
        | SOME src =>
            if src.inst_id = inst.inst_id then NONE
            else SOME (expr, src)
End
