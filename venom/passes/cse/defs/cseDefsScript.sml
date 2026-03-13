(*
 * Common Subexpression Elimination — Definitions
 *
 * Ports vyper/venom/passes/common_subexpression_elimination.py to HOL4.
 *
 * Replaces instructions whose expression is already available with
 * ASSIGN from the existing result variable.
 *
 * Framework: analysis_inst_simulates + df_analysis_pass_correct_sound.
 * Uses the existing available expression analysis (availExprDefs).
 *
 * TOP-LEVEL:
 *   cse_inst              — per-instruction transform (given avail state)
 *   cse_function          — function-level transform
 *)

Theory cseDefs
Ancestors
  analysisSimDefs availExprDefs dfgDefs passSharedDefs venomEffects While

(* ===== Opcodes excluded from CSE ===== *)

(* Matches Python NO_SUBSTITUTE_OPCODES: instructions that are
   uninteresting for CSE (trivial, pseudo, or environment-reads
   that shouldn't be deduplicated). *)
Definition cse_skip_opcode_def:
  cse_skip_opcode ASSIGN = T /\
  cse_skip_opcode PHI = T /\
  cse_skip_opcode PARAM = T /\
  cse_skip_opcode NOP = T /\
  cse_skip_opcode GAS = T /\
  cse_skip_opcode MSIZE = T /\
  cse_skip_opcode CALLDATASIZE = T /\
  cse_skip_opcode GASLIMIT = T /\
  cse_skip_opcode ADDRESS = T /\
  cse_skip_opcode CODESIZE = T /\
  cse_skip_opcode RETURNDATASIZE = T /\
  cse_skip_opcode GASPRICE = T /\
  cse_skip_opcode ORIGIN = T /\
  cse_skip_opcode COINBASE = T /\
  cse_skip_opcode TIMESTAMP = T /\
  cse_skip_opcode NUMBER = T /\
  cse_skip_opcode PREVRANDAO = T /\
  cse_skip_opcode CHAINID = T /\
  cse_skip_opcode BASEFEE = T /\
  cse_skip_opcode BLOBBASEFEE = T /\
  cse_skip_opcode OFFSET = T /\
  cse_skip_opcode _ = F
End

(* ===== Expression depth ===== *)

(* Python: SMALL_EXPRESSION = 1.
   Only eliminate cross-block if expr.depth > SMALL_EXPRESSION.
   depth(Var/Lit) = 0, depth(Op _ args) = 1 + max(map depth args) *)
Definition expr_depth_def:
  (expr_depth (ExprVar _) = 0n) /\
  (expr_depth (ExprLit _) = 0n) /\
  (expr_depth (ExprOp _ args) = 1 + expr_depth_list args) /\
  (expr_depth_list [] = 0n) /\
  (expr_depth_list (e :: es) =
    let d = expr_depth e in
    let ds = expr_depth_list es in
    if d > ds then d else ds)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL e => avail_expr_size e
  | INR es => avail_expr1_size es)`
End

(* ===== Per-instruction transform ===== *)

(* The avail_exprs lattice maps canonical expressions to source
   instructions. To look up whether an instruction is available,
   we need the DFG (to canonicalize) and the avail state.
   We pair them as the lattice value: (dfg, avail_exprs). *)

(* Lookup with depth check. Returns SOME (src_inst, expr) if available. *)
(* Find any source for this expression, preferring same-block sources.
   Returns (src_inst, expr, is_same_block). *)
Definition cse_lookup_def:
  cse_lookup (dfg : dfg_analysis) (av : avail_exprs) inst =
    let expr = mk_expr dfg inst in
    case FLOOKUP av expr of
      NONE => NONE
    | SOME srcs =>
        let valid = FILTER (\s. s.inst_id <> inst.inst_id) srcs in
        case valid of
          [] => NONE
        | first :: _ => SOME (first, expr)
End

(* Find a same-block source for an expression.
   Python's get_from_same_bb: filter the instruction list for same BB. *)
Definition cse_lookup_same_bb_def:
  cse_lookup_same_bb (dfg : dfg_analysis) (av : avail_exprs)
                     (bb_inst_ids : num set) inst =
    let expr = mk_expr dfg inst in
    case FLOOKUP av expr of
      NONE => NONE
    | SOME srcs =>
        let same_bb = FILTER (\s. s.inst_id <> inst.inst_id /\
                                  s.inst_id IN bb_inst_ids) srcs in
        case same_bb of
          [] => NONE
        | first :: _ => SOME (first, expr)
End

(* Python: SMALL_EXPRESSION = 1.
   Cross-block: only if expr.depth > 1.
   Same-block: always.
   bb_inst_ids is the set of inst_ids in the current basic block. *)
Definition cse_inst_def:
  cse_inst (bb_inst_ids : num set)
           (dav : dfg_analysis # avail_exprs option) inst =
    case dav of (dfg, av_opt) =>
    let av = avail_unwrap av_opt in
    if cse_skip_opcode inst.inst_opcode then inst
    else if is_terminator inst.inst_opcode then inst
    else if inst.inst_opcode = INVOKE then inst
    else if is_nonidempotent inst.inst_opcode then inst
    else
    (* Python logic:
       1. If depth > 1: use any available source (cross-block OK)
       2. If depth <= 1: only use a same-block source *)
    let try_replace = \make_replacement.
      case cse_lookup dfg av inst of
        NONE => inst
      | SOME (src_inst, expr) =>
          if expr_depth expr > 1 then make_replacement src_inst
          else if src_inst.inst_id IN bb_inst_ids then
            make_replacement src_inst
          else
            (* Fallback: search for same-block source *)
            case cse_lookup_same_bb dfg av bb_inst_ids inst of
              SOME (bb_src, _) => make_replacement bb_src
            | NONE => inst
    in
    case inst.inst_outputs of
      [out] =>
        try_replace (\src_inst.
          case src_inst.inst_outputs of
            [src_var] => mk_assign_inst inst (Var src_var)
          | _ => inst)
    | [] =>
        try_replace (\src_inst. mk_nop_inst inst)
    | _ => inst
End

(* ===== Function-level transform ===== *)

(* CSE block transform: structurally matches analysis_block_transform
   (MAPi + df_at) but with extra per-block context (bb_inst_ids) for
   the same-block expression depth heuristic. The framework's
   f : 'a → inst → inst list doesn't support per-block context,
   so CSE uses its own block transform. *)
Definition cse_block_transform_def:
  cse_block_transform (dfg : dfg_analysis)
                      (result : avail_exprs option df_state) bb =
    let bb_ids = set (MAP (\inst. inst.inst_id) bb.bb_instructions) in
    bb with bb_instructions :=
      MAPi (\idx inst.
        cse_inst bb_ids
          (dfg, df_at NONE result bb.bb_label idx) inst)
        bb.bb_instructions
End

(* Single CSE pass *)
Definition cse_single_pass_def:
  cse_single_pass fn =
    let dfg = dfg_build_function fn in
    let result = avail_analyze fn in
    function_map_transform (cse_block_transform dfg result) fn
End

(* Python runs CSE in a loop until fixpoint.
   OWHILE returns SOME when the iteration terminates, NONE otherwise.
   Termination holds because each changed pass replaces at least one
   non-ASSIGN instruction with ASSIGN, strictly decreasing the count. *)
Definition cse_iterate_def:
  cse_iterate fn =
    OWHILE (\fn. (cse_single_pass fn).fn_blocks <> fn.fn_blocks)
           cse_single_pass fn
End

Definition cse_function_def:
  cse_function fn =
    case cse_iterate fn of
      SOME fn' => clear_nops_function fn'
    | NONE => clear_nops_function fn
End
