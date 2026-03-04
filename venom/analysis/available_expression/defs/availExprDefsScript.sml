(*
 * Available Expression Analysis — Definitions
 *
 * Ports vyper/venom/analysis/available_expression.py to HOL4.
 *
 * Forward dataflow: computes which expressions are available (already
 * computed and not invalidated) at each program point.
 *
 * TOP-LEVEL:
 *   avail_expr          — expression tree type
 *   is_commutative      — commutative opcodes (operand order irrelevant)
 *   is_expandable       — opcodes whose operands are recursively expanded
 *   canon_expr          — canonical form (sorted operands for commutative ops)
 *   mk_expr             — build expression from instruction + DFG
 *   avail_exprs         — available expression lattice (fmap: expr → inst list)
 *   avail_meet          — lattice meet (intersection)
 *   avail_transfer_inst — transfer function for one instruction
 *   avail_transfer_bb   — transfer function for one basic block
 *   avail_result        — analysis result record
 *   avail_handle_bb     — process one BB in the worklist iteration
 *   avail_analyze       — top-level analysis entry point
 *
 * Helper:
 *   expr_effects        — effects of all opcodes in an expression tree
 *   avail_remove_effect — kill expressions affected by a write effect
 *)

Theory availExprDefs
Ancestors
  venomEffects dfgAnalysis cfgDefs dfIterateDefs

(* is_commutative from venomEffectsTheory *)

(* ===== Pseudo / non-expandable opcodes ===== *)

(* In the Python, _get_operand returns the raw operand (not an expression)
 * for phi, param, source, and multi-output instructions.
 * For assign, it follows through to the source operand.
 * For all other single-output instructions, it returns the expression.
 *
 * We model this by: an opcode is "expandable" if mk_expr should recurse
 * into it (i.e. it's not phi/param/assign and produces exactly one output).
 * Assign is handled specially — we follow through it. *)
Definition is_pseudo_def:
  is_pseudo PHI = T /\
  is_pseudo PARAM = T /\
  is_pseudo _ = F
End

(* ===== Expression Tree ===== *)

(* An expression tree: opcode applied to sub-expressions or leaf operands.
 * Leaf operands are either variable references or literals.
 * This matches Python _Expression. *)
Datatype:
  avail_expr =
    ExprVar string
  | ExprLit bytes32
  | ExprOp opcode (avail_expr list)
End

(* Total order on expressions for canonical sorting.
 * ExprVar < ExprLit < ExprOp; within each, compare components. *)
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

(* Canonical form: sort operands for commutative ops.
 * Matches Python _Expression.__hash__ which sorts operand hashes,
 * and same() which checks reversed operands for commutative ops.
 * By canonicalizing, we get structural equality = semantic equality. *)
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

(* ===== Build Expression from Instruction ===== *)

(* Convert an operand to an expression leaf, possibly expanding through DFG.
 * Matches Python _get_operand:
 *   - Literal → ExprLit
 *   - Label → ExprVar (label name, won't match anything useful)
 *   - Var → look up producing instruction in DFG:
 *       - phi/param/multi-output → ExprVar (leaf)
 *       - assign → follow through to source operand
 *       - otherwise → recursively build expression
 *
 * The recursion through DFG is bounded by the DFG being acyclic (SSA).
 * We use a fuel parameter to ensure termination in HOL4. *)
Definition mk_operand_expr_def:
  (mk_operand_expr dfg fuel (Lit v) = ExprLit v) /\
  (mk_operand_expr dfg fuel (Label l) = ExprVar l) /\
  (mk_operand_expr dfg (0:num) (Var v) = ExprVar v) /\
  (mk_operand_expr dfg (SUC n) (Var v) =
    case dfg_get_def dfg v of
      NONE => ExprVar v
    | SOME def_inst =>
        if is_pseudo def_inst.inst_opcode then ExprVar v
        else if def_inst.inst_opcode = ASSIGN then
          (case def_inst.inst_operands of
            [src] => mk_operand_expr dfg n src
          | _ => ExprVar v)
        else if LENGTH def_inst.inst_outputs > 1 then ExprVar v
        else mk_inst_expr dfg n def_inst) /\
  (mk_inst_expr dfg fuel inst =
    let args = MAP (mk_operand_expr dfg fuel) inst.inst_operands in
    canon_expr (ExprOp inst.inst_opcode args))
Termination
  WF_REL_TAC `measure (λx. case x of
    INL (dfg, fuel, op) => fuel * 2 + 1
  | INR (dfg, fuel, inst) => fuel * 2 + 2)` >>
  simp[]
End

(* Top-level: build expression for an instruction with enough fuel *)
Definition mk_expr_def:
  mk_expr dfg fuel inst = mk_inst_expr dfg fuel inst
End

(* ===== Effects of an Expression Tree ===== *)

(* Collect all effects (read ∪ write) of opcodes appearing in an expression.
 * Used to determine if an expression is killed by a write effect. *)
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

(* Available expressions: map from canonical expression to list of
 * instructions that compute it.
 * Matches Python _AvailableExpressions. *)
Type avail_exprs = ``:(avail_expr, instruction list) fmap``

Definition avail_empty_def:
  avail_empty : avail_exprs = FEMPTY
End

(* Add an expression with its producing instruction *)
Definition avail_add_def:
  avail_add (ae : avail_exprs) expr inst =
    case FLOOKUP ae expr of
      NONE => ae |+ (expr, [inst])
    | SOME insts => ae |+ (expr, insts ++ [inst])
End

(* Remove all expressions whose effects overlap with the given write effect.
 * Matches Python remove_effect. *)
Definition avail_remove_effect_def:
  avail_remove_effect (ae : avail_exprs) (eff : effects) =
    if eff = empty_effects then ae
    else DRESTRICT ae
      { expr | expr IN FDOM ae /\
               DISJOINT (expr_effects expr) eff }
End

(* Lattice meet: intersection — keep only expressions available in ALL
 * predecessors (with instruction lists intersected too).
 * Matches Python lattice_meet. *)
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
  avail_meet [] = avail_empty /\
  avail_meet [ae] = ae /\
  avail_meet (ae :: rest) = avail_meet_two ae (avail_meet rest)
End

(* Query: get source instruction for an available expression *)
Definition avail_get_source_def:
  avail_get_source (ae : avail_exprs) expr =
    case FLOOKUP ae expr of
      NONE => NONE
    | SOME [] => NONE
    | SOME (inst :: _) => SOME inst
End

(* ===== Transfer Function ===== *)

(* Process one instruction: kill invalidated expressions, then add new one.
 * Matches Python _handle_bb's per-instruction logic. *)
Definition avail_transfer_inst_def:
  avail_transfer_inst dfg fuel inst (ae : avail_exprs) =
    (* Skip pseudo instructions and terminators *)
    if is_pseudo inst.inst_opcode ∨
       inst.inst_opcode = ASSIGN ∨
       is_terminator inst.inst_opcode then ae
    (* Skip multi-output instructions *)
    else if LENGTH inst.inst_outputs > 1 then ae
    else
      let expr = mk_expr dfg fuel inst in
      (* Kill expressions affected by write effects *)
      let we = write_effects inst.inst_opcode in
      let ae' = avail_remove_effect ae we in
      (* Don't add nonidempotent instructions *)
      if is_nonidempotent inst.inst_opcode then ae'
      (* Don't add if opcode has conflicting effects *)
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

(* Process all instructions in a block, threading available expressions
 * and recording per-instruction state and expressions.
 * Returns updated (ae, inst_map, expr_map). *)
Definition avail_transfer_bb_loop_def:
  avail_transfer_bb_loop dfg fuel [] ae imap emap = (ae, imap, emap) /\
  avail_transfer_bb_loop dfg fuel (inst::rest) ae imap emap =
    let imap' = imap |+ (inst.inst_id, ae) in
    let expr = mk_expr dfg fuel inst in
    let emap' = emap |+ (inst.inst_id, expr) in
    let ae' = avail_transfer_inst dfg fuel inst ae in
    avail_transfer_bb_loop dfg fuel rest ae' imap' emap'
End

(* ===== Worklist-Based Analysis ===== *)

(* Handle one basic block: compute entry state from predecessors,
 * check for change, run transfer.
 * Returns (changed, updated_result).
 * Matches Python _handle_bb. *)
Definition avail_handle_bb_def:
  avail_handle_bb cfg dfg fuel fn ar (bb : basic_block) =
    let preds = cfg_preds_of cfg bb.bb_label in
    let pred_outs = MAP (ae_lookup_bb_out ar) preds in
    let entry_ae = avail_meet pred_outs in
    (* Check if entry changed *)
    let old_in = ae_lookup_bb_in ar bb.bb_label in
    if entry_ae = old_in ∧ bb.bb_label IN FDOM ar.ae_bb_ins then
      (F, ar)
    else
      let ar' = ar with ae_bb_ins := ar.ae_bb_ins |+ (bb.bb_label, entry_ae) in
      let (exit_ae, imap, emap) =
        avail_transfer_bb_loop dfg fuel bb.bb_instructions entry_ae
          ar'.ae_inst ar'.ae_inst_expr in
      let ar'' = ar' with <|
        ae_bb_outs := ar'.ae_bb_outs |+ (bb.bb_label, exit_ae);
        ae_inst := imap;
        ae_inst_expr := emap
      |> in
      (* Changed if output differs *)
      let old_out = ae_lookup_bb_out ar bb.bb_label in
      (exit_ae <> old_out ∨ bb.bb_label NOTIN FDOM ar.ae_bb_outs, ar'')
End

(* One pass: process blocks in order, collecting successors to revisit.
 * Returns (updated_result, worklist_additions). *)
Definition avail_one_pass_def:
  avail_one_pass cfg dfg fuel fn ar [] = (ar, []) /\
  avail_one_pass cfg dfg fuel fn ar (lbl::rest) =
    case lookup_block lbl fn.fn_blocks of
      NONE => avail_one_pass cfg dfg fuel fn ar rest
    | SOME bb =>
        let (changed, ar') = avail_handle_bb cfg dfg fuel fn ar bb in
        let (ar'', more) = avail_one_pass cfg dfg fuel fn ar' rest in
        if changed then
          (ar'', cfg_succs_of cfg lbl ++ more)
        else (ar'', more)
End

(* Worklist iteration: process worklist items until empty or fuel exhausted.
 * iter_fuel bounds the number of passes (convergence is guaranteed by
 * monotonicity of the lattice — available sets can only shrink — but
 * the termination argument is complex, so we use fuel). *)
Definition avail_iterate_def:
  (avail_iterate cfg dfg fuel fn ar (0:num) worklist = ar) /\
  (avail_iterate cfg dfg fuel fn ar (SUC n) [] = ar) /\
  (avail_iterate cfg dfg fuel fn ar (SUC n) (lbl::rest) =
    let (ar', new_wl) = avail_one_pass cfg dfg fuel fn ar (lbl::rest) in
    if ar' = ar then ar
    else avail_iterate cfg dfg fuel fn ar' n new_wl)
End

(* ===== Top-Level Analysis ===== *)

(* Run the available expression analysis on a function.
 * fuel bounds the DFG traversal depth in mk_expr.
 * iter_fuel bounds the number of worklist passes. *)
Definition avail_analyze_def:
  avail_analyze fn fuel iter_fuel =
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let ar0 = avail_result_empty in
    let worklist = fn_labels fn in
    avail_iterate cfg dfg fuel fn ar0 iter_fuel worklist
End

(* ===== Query API ===== *)

(* Get the expression and source instruction for an instruction,
 * if an equivalent expression is available. *)
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
