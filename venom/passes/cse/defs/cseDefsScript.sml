(*
 * Common Subexpression Elimination — Definitions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * Ports vyper/venom/passes/common_subexpression_elimination.py to HOL4.
 *
 * Replaces instructions whose expression is already available with
 * ASSIGN from the existing result variable.
 *
 * Uses the available expression analysis (availExprDefs) as a candidate
 * pool with root-only effect removal (overapproximation). Correctness
 * is ensured by a canon map + operand identity check that models
 * Python's object identity (`is`) in same_ops.
 *
 * TOP-LEVEL:
 *   cse_inst              — per-instruction transform (given avail + canon)
 *   cse_function          — function-level transform
 *
 * Helper (canon map):
 *   operand_producer      — follow ASSIGN chains to ultimate producer id
 *   canonical_id          — transitive canon lookup with identity fallback
 *   canonical_operand_ids — list of canonical producer ids for operands
 *   compute_canon_block   — build canon entries for one block
 *   compute_canon         — build canon map for entire function
 *
 * Helper (lookup):
 *   cse_lookup            — find ae match with operand identity check
 *   cse_lookup_same_bb    — same-block variant
 *   cse_skip_opcode       — opcodes excluded from CSE
 *   expr_depth            — expression depth for cross-block heuristic
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
  cse_skip_opcode MEMTOP = T /\
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

(* ===== Canon Map: Operand Identity ===== *)

(* Models Python's inst_to_expr cache + object identity in same_ops.
   canon : num |-> num maps instruction IDs to their canonical
   representative — the earliest instruction computing the same
   expression with provably identical operand sources. *)

Type canon_map = ``:(num, num) fmap``

(* Follow ASSIGN chains in the DFG to find the ultimate non-ASSIGN
   producing instruction's ID. Returns NONE for literals/labels or
   if the variable has no DFG entry. visited set for termination. *)
Definition operand_producer_def:
  operand_producer (dfg : dfg_analysis) visited (Var v) =
    (if v IN visited then NONE
     else case FLOOKUP dfg.dfg_defs v of
       NONE => NONE
     | SOME inst =>
         if inst.inst_opcode = ASSIGN then
           (case inst.inst_operands of
              [op] => operand_producer dfg (v INSERT visited) op
            | _ => SOME inst.inst_id)
         else SOME inst.inst_id) /\
  operand_producer dfg visited (Lit _) = NONE /\
  operand_producer dfg visited (Label _) = NONE
Termination
  WF_REL_TAC `measure (λ(dfg, visited, op).
    CARD (FDOM dfg.dfg_defs DIFF visited))` >>
  rw[] >>
  irule pred_setTheory.CARD_PSUBSET >> conj_tac
  >- simp[pred_setTheory.FINITE_DIFF, finite_mapTheory.FDOM_FINITE]
  >> simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF,
          pred_setTheory.EXTENSION]
  >> qexists_tac `v` >> fs[finite_mapTheory.FLOOKUP_DEF]
End

(* Transitive canon lookup. If id is in the map, return its
   representative; otherwise id is its own representative. *)
Definition canonical_id_def:
  canonical_id (canon : canon_map) id =
    case FLOOKUP canon id of
      SOME rep => rep
    | NONE => id
End

(* Canonical operand producer IDs for an instruction's operands.
   Each operand is resolved to its ultimate producer via the DFG,
   then mapped through the canon map for transitive canonicalization. *)
Definition canonical_operand_ids_def:
  canonical_operand_ids (canon : canon_map) (dfg : dfg_analysis)
                        (inst : instruction) =
    MAP (\op. OPTION_MAP (canonical_id canon)
                         (operand_producer dfg {} op))
        inst.inst_operands
End

(* Check that two instructions have matching canonical operand IDs.
   This models Python's same_ops `is` check: two expressions match
   only if their sub-expression operands come from the same canonical
   producing instructions. *)
Definition operand_ids_match_def:
  operand_ids_match canon dfg inst src =
    (canonical_operand_ids canon dfg inst =
     canonical_operand_ids canon dfg src)
End

(* ===== Compute Canon Map ===== *)

(* Process one instruction: if its expression is in ae and the operand
   producers match the source's, record canon[inst.id] = canonical source.
   inst_ae is the ae state BEFORE this instruction (from df_at). *)
Definition compute_canon_inst_def:
  compute_canon_inst (dfg : dfg_analysis) (canon : canon_map)
                     (inst_ae : avail_exprs) (inst : instruction) =
    if is_pseudo inst.inst_opcode ∨
       inst.inst_opcode = ASSIGN ∨
       is_terminator inst.inst_opcode then canon
    else if LENGTH inst.inst_outputs > 1 then canon
    else
      let expr = mk_expr dfg inst in
      case avail_get_source inst_ae expr of
        NONE => canon
      | SOME src =>
          if src.inst_id = inst.inst_id then canon
          else if operand_ids_match canon dfg inst src then
            canon |+ (inst.inst_id, canonical_id canon src.inst_id)
          else canon
End

(* Process one block: fold compute_canon_inst over instructions,
   using df_at for each instruction's ae state. *)
Definition compute_canon_block_def:
  compute_canon_block (dfg : dfg_analysis)
                      (result : avail_exprs option df_state)
                      (canon : canon_map) (bb : basic_block) =
    let lbl = bb.bb_label in
    FST (FOLDL
      (\(c, idx) inst.
        let ae = avail_unwrap (df_at NONE result lbl idx) in
        (compute_canon_inst dfg c ae inst, idx + 1n))
      (canon, 0n)
      bb.bb_instructions)
End

(* Compute canon map for entire function: fold over blocks. *)
Definition compute_canon_def:
  compute_canon (dfg : dfg_analysis)
                (result : avail_exprs option df_state)
                (fn : ir_function) =
    FOLDL (compute_canon_block dfg result) FEMPTY fn.fn_blocks
End

(* ===== CSE Lookup with Operand Identity ===== *)

(* Find an ae source for inst's expression, filtered by operand identity.
   After structural ae match, verify canonical operand IDs agree. *)
Definition cse_lookup_def:
  cse_lookup (canon : canon_map) (dfg : dfg_analysis)
             (av : avail_exprs) inst =
    let expr = mk_expr dfg inst in
    case FLOOKUP av expr of
      NONE => NONE
    | SOME srcs =>
        let valid = FILTER (\s. s.inst_id <> inst.inst_id /\
                                operand_ids_match canon dfg inst s) srcs in
        case valid of
          [] => NONE
        | first :: _ => SOME (first, expr)
End

(* Same-block variant: additionally filter for same-block sources. *)
Definition cse_lookup_same_bb_def:
  cse_lookup_same_bb (canon : canon_map) (dfg : dfg_analysis)
                     (av : avail_exprs) (bb_inst_ids : num set) inst =
    let expr = mk_expr dfg inst in
    case FLOOKUP av expr of
      NONE => NONE
    | SOME srcs =>
        let same_bb = FILTER (\s. s.inst_id <> inst.inst_id /\
                                  s.inst_id IN bb_inst_ids /\
                                  operand_ids_match canon dfg inst s)
                             srcs in
        case same_bb of
          [] => NONE
        | first :: _ => SOME (first, expr)
End

(* ===== Per-instruction transform ===== *)

(* Python: SMALL_EXPRESSION = 1.
   Cross-block: only if expr.depth > 1.
   Same-block: always.
   bb_inst_ids is the set of inst_ids in the current basic block. *)
Definition cse_inst_def:
  cse_inst (bb_inst_ids : num set) (canon : canon_map)
           (dav : dfg_analysis # avail_exprs option) inst =
    case dav of (dfg, av_opt) =>
    let av = avail_unwrap av_opt in
    if cse_skip_opcode inst.inst_opcode then inst
    else if is_terminator inst.inst_opcode then inst
    else if inst.inst_opcode = INVOKE then inst
    else if is_nonidempotent inst.inst_opcode then inst
    else
    let try_replace = \make_replacement.
      case cse_lookup canon dfg av inst of
        NONE => inst
      | SOME (src_inst, expr) =>
          if expr_depth expr > 1 then make_replacement src_inst
          else if src_inst.inst_id IN bb_inst_ids then
            make_replacement src_inst
          else
            (* Fallback: search for same-block source *)
            case cse_lookup_same_bb canon dfg av bb_inst_ids inst of
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

(* CSE block transform: MAPi + df_at with per-block bb_inst_ids context
   and the canon map for operand identity checks. *)
Definition cse_block_transform_def:
  cse_block_transform (canon : canon_map) (dfg : dfg_analysis)
                      (result : avail_exprs option df_state) bb =
    let bb_ids = set (MAP (\inst. inst.inst_id) bb.bb_instructions) in
    bb with bb_instructions :=
      MAPi (\idx inst.
        cse_inst bb_ids canon
          (dfg, df_at NONE result bb.bb_label idx) inst)
        bb.bb_instructions
End

(* Single CSE pass: analyze, compute canon, transform. *)
Definition cse_single_pass_def:
  cse_single_pass fn =
    let dfg = dfg_build_function fn in
    let result = avail_analyze fn in
    let canon = compute_canon dfg result fn in
    function_map_transform (cse_block_transform canon dfg result) fn
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
