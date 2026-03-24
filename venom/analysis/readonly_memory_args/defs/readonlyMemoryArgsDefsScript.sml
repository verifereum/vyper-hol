(*
 * Readonly Memory Args Analysis — Definitions
 *
 * Upstream: vyperlang/vyper@cff4f6822
 *
 * Interprocedural analysis inferring which invoke memory parameters
 * of each function are read-only (never written to).
 *
 * The analysis iterates to fixpoint over all functions. For each function,
 * it traces memory operands back through assign/phi/add/sub/gep chains
 * to find which invoke parameter indices may alias a memory write.
 * Parameters never aliased are read-only.
 *
 * Consumed by both invoke copy forwarding passes.
 *
 * TOP-LEVEL:
 *   invoke_fn_meta         — per-function invoke metadata
 *   fn_param_info          — collected parameter info
 *   collect_param_info     — extract invoke params from entry block
 *   has_ret_instruction    — check if function has a RET terminator
 *   root_param_indices     — trace variable origins to param indices
 *   root_param_indices_op  — trace operand origins to param indices
 *   rma_analyze_fn         — analyze one function for mutable params
 *   rma_fixpoint_step      — one iteration over all functions
 *   rma_analyze            — fixpoint computation
 *   rma_get_readonly_idxs  — extract readonly indices from result
 *
 * Helper:
 *   entry_param_outputs    — PARAM outputs from entry block
 *   root_from_inst_ops     — extract variable operands for origin tracing
 *)

Theory readonlyMemoryArgsDefs
Ancestors
  dfgDefs memLocDefs venomInst venomEffects While

(* ===== Invoke Function Metadata ===== *)

(* Per-function invoke metadata, set during codegen (lowering from Vyper AST).
   These fields model Python's IRFunction._invoke_param_count and
   IRFunction._has_memory_return_buffer_param.

   Stored in a map (string, invoke_fn_meta) fmap keyed by function name.
   Functions not in the map have no metadata (conservative: no forwarding). *)
Datatype:
  invoke_fn_meta = <|
    ifm_invoke_param_count : num;
    ifm_has_memory_return_buffer : bool
  |>
End

(* ===== Parameter Collection ===== *)

(* Extract leading PARAM instruction outputs from a block.
   Matches Python IRBasicBlock.param_instructions: yields PARAM instructions
   at the start of the block, stopping at the first non-PARAM. *)
Definition entry_param_outputs_def:
  entry_param_outputs [] = [] /\
  entry_param_outputs (inst::rest) =
    if inst.inst_opcode = PARAM then
      inst.inst_outputs ++ entry_param_outputs rest
    else []
End

(* Check if any block in the function has a RET terminator.
   Matches Python _has_ret_instruction. *)
Definition has_ret_instruction_def:
  has_ret_instruction fn =
    EXISTS (\bb.
      EXISTS (\inst. inst.inst_opcode = RET) bb.bb_instructions)
      fn.fn_blocks
End

(* Collected parameter info for a function.
   invoke_params: the subset of PARAM outputs that are invoke parameters.
   invoke_param_index: maps variable name → parameter index. *)
Datatype:
  fn_param_info = <|
    fpi_invoke_params : string list;
    fpi_invoke_param_index : (string, num) fmap
  |>
End

(* Build invoke param index from a list of param names.
   Maps param name → its position (0-based). *)
Definition build_param_index_def:
  build_param_index params =
    FST (FOLDL (\(fm, i) v. (fm |+ (v, i), i + 1))
      (FEMPTY, 0n) params)
End

(* Collect parameter info for a function.
   Matches Python _collect_param_info:
   - Get PARAM outputs from entry block
   - Determine invoke param count from metadata or RET heuristic
   - Take that many leading params as invoke params *)
Definition collect_param_info_def:
  collect_param_info (fn_meta : (string, invoke_fn_meta) fmap)
                     (fn : ir_function) =
    let params =
      case entry_block fn of
        NONE => []
      | SOME bb => entry_param_outputs bb.bb_instructions in
    if NULL params then
      <| fpi_invoke_params := [];
         fpi_invoke_param_index := FEMPTY |>
    else
    let invoke_count =
      case FLOOKUP fn_meta fn.fn_name of
        SOME meta => MIN meta.ifm_invoke_param_count (LENGTH params)
      | NONE =>
          if has_ret_instruction fn then
            PRE (LENGTH params)
          else LENGTH params in
    let invoke_params = TAKE invoke_count params in
    <| fpi_invoke_params := invoke_params;
       fpi_invoke_param_index := build_param_index invoke_params |>
End

(* ===== Origin Tracing ===== *)

(* Extract variable names from operands that should be traced for
   origin analysis. Depends on the producing instruction's opcode.
   Matches Python _root_from_inst / _root_from_add / _root_from_sub /
   _root_from_gep dispatch.

   ASSIGN: trace through source
   PHI: trace all variable operands
   ADD: trace all variable operands
   SUB: trace both operands (EVM order: [b; a] → a - b)
   GEP: trace base and offset
   Other: empty (not a param alias) *)
Definition root_from_inst_ops_def:
  root_from_inst_ops inst =
    case inst.inst_opcode of
      ASSIGN =>
        (case inst.inst_operands of
           [Var src] => [src]
         | _ => [])
    | PHI =>
        FLAT (MAP (\op. case op of Var v => [v] | _ => [])
                  inst.inst_operands)
    | ADD =>
        FLAT (MAP (\op. case op of Var v => [v] | _ => [])
                  inst.inst_operands)
    | SUB =>
        (case inst.inst_operands of
           [op_b; op_a] =>
             FLAT (MAP (\op. case op of Var v => [v] | _ => [])
                       [op_a; op_b])
         | _ => [])
    | GEP =>
        (case inst.inst_operands of
           [op_base; op_off] =>
             FLAT (MAP (\op. case op of Var v => [v] | _ => [])
                       [op_base; op_off])
         | _ => [])
    | _ => []
End

(* Trace variable origins through DFG to find param indices.
   Uses visited set for termination (same pattern as normalize_operand).
   all_count: number of invoke params (for cycle fallback).

   On cycle (v IN visited): return {0..all_count-1} conservatively.
   If v is an invoke param: return {its index}.
   Otherwise: look up producing instruction, extract child vars,
   recursively trace all of them, and union results.

   Uses mutual recursion with root_param_indices_list for HOL4's
   termination checker (avoids FOLDL with recursive calls). *)
Definition root_param_indices_def:
  root_param_indices (dfg : dfg_analysis)
    (param_idx : (string, num) fmap)
    (all_count : num)
    (visited : string set)
    (v : string) =
  (if v IN visited then
    count all_count
  else
    case FLOOKUP param_idx v of
      SOME idx => {idx}
    | NONE =>
        case dfg_get_def dfg v of
          NONE => {}
        | SOME inst =>
            root_param_indices_list dfg param_idx all_count
              (v INSERT visited) (root_from_inst_ops inst)) /\
  root_param_indices_list dfg param_idx all_count visited [] = {} /\
  root_param_indices_list dfg param_idx all_count visited (cv::cvs) =
    root_param_indices dfg param_idx all_count visited cv UNION
    root_param_indices_list dfg param_idx all_count visited cvs
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\x. case x of
    INL (dfg, param_idx, all_count, visited, v) =>
      (CARD (FDOM dfg.dfg_defs DIFF visited), 0)
  | INR (dfg, param_idx, all_count, visited, cvs) =>
      (CARD (FDOM dfg.dfg_defs DIFF visited), SUC (LENGTH cvs)))`
  >> rw[]
  >> irule pred_setTheory.CARD_PSUBSET >> conj_tac
  >- simp[pred_setTheory.FINITE_DIFF, finite_mapTheory.FDOM_FINITE]
  >> simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF,
          pred_setTheory.EXTENSION]
  >> qexists_tac `v`
  >> fs[finite_mapTheory.FLOOKUP_DEF, dfgDefsTheory.dfg_get_def_def]
End

(* Trace an operand (not just a variable) to param indices. *)
Definition root_param_indices_op_def:
  root_param_indices_op dfg param_idx all_count visited op =
    case op of
      Var v => root_param_indices dfg param_idx all_count visited v
    | _ => {}
End

(* ===== Per-Function Analysis ===== *)

(* Check if a callee arg at position callee_arg_idx is readonly
   in the current fixpoint state.
   readonly_by_fn: maps function name → list of bools (T = readonly). *)
Definition callee_arg_readonly_def:
  callee_arg_readonly (readonly_by_fn : (string, bool list) fmap)
                      callee_name callee_arg_idx =
    case FLOOKUP readonly_by_fn callee_name of
      NONE => F
    | SOME state =>
        if callee_arg_idx < LENGTH state then
          EL callee_arg_idx state
        else F
End

(* Handle an INVOKE instruction: for each arg, check if the callee
   considers that position readonly. If not (or if callee unknown),
   the caller's aliased param indices become mutable.

   Returns set of param indices made mutable by this invoke. *)
Definition rma_handle_invoke_def:
  rma_handle_invoke (functions : ir_function list)
                    (readonly_by_fn : (string, bool list) fmap)
                    (root_fn : operand -> num set)
                    (inst : instruction) =
    case inst.inst_operands of
      [] => {}
    | (target :: args) =>
        let callee_name =
          case target of
            Label lbl => SOME lbl
          | _ => NONE in
        let callee_exists =
          case callee_name of
            NONE => F
          | SOME name => EXISTS (\fn. fn.fn_name = name) functions in
        BIGUNION (set (MAPi (\i op.
          let caller_idxs = root_fn op in
          if caller_idxs = {} then {}
          else if ~callee_exists then caller_idxs
          else
            case callee_name of
              NONE => caller_idxs
            | SOME name =>
                if callee_arg_readonly readonly_by_fn name i
                then {}
                else caller_idxs)
          args))
End

(* Analyze one function: find which invoke params are mutable.
   Returns a list of bools (T = readonly, F = mutable). *)
Definition rma_analyze_fn_def:
  rma_analyze_fn (functions : ir_function list)
                 (readonly_by_fn : (string, bool list) fmap)
                 (dfg : dfg_analysis)
                 (info : fn_param_info)
                 (fn : ir_function) =
    let n = LENGTH info.fpi_invoke_params in
    if n = 0 then [] else
    let root_fn = root_param_indices_op dfg info.fpi_invoke_param_index n {} in
    (* Collect all mutable indices across all instructions *)
    let mutable_idxs =
      BIGUNION (set (MAP (\bb.
        BIGUNION (set (MAP (\inst.
          if inst.inst_opcode = INVOKE then
            rma_handle_invoke functions readonly_by_fn root_fn inst
          else
            case mem_write_ops inst of
              NONE => {}
            | SOME ops => root_fn ops.iao_ofst)
          bb.bb_instructions)))
        fn.fn_blocks)) in
    GENLIST (\i. i NOTIN mutable_idxs) n
End

(* ===== Fixpoint Iteration ===== *)

(* One step of the fixpoint: analyze all functions, update readonly_by_fn.
   Returns (changed, new_state). *)
Definition rma_fixpoint_step_def:
  rma_fixpoint_step (functions : ir_function list)
                    (infos : (string, fn_param_info) fmap)
                    (dfgs : (string, dfg_analysis) fmap)
                    (readonly_by_fn : (string, bool list) fmap) =
    FOLDL (\(changed, st) fn.
      case (FLOOKUP infos fn.fn_name, FLOOKUP dfgs fn.fn_name) of
        (SOME info, SOME dfg) =>
          let new_state =
            rma_analyze_fn functions st dfg info fn in
          let old_state =
            case FLOOKUP st fn.fn_name of
              NONE => []
            | SOME s => s in
          if new_state = old_state then (changed, st)
          else (T, st |+ (fn.fn_name, new_state))
      | _ => (changed, st))
      (F, readonly_by_fn) functions
End

(* Initialize: all params are readonly (T).
   Matches Python: readonly_by_fn[fn] = tuple(True for _ in range(n)) *)
Definition rma_init_state_def:
  rma_init_state (functions : ir_function list)
                 (infos : (string, fn_param_info) fmap) =
    FOLDL (\fm fn.
      case FLOOKUP infos fn.fn_name of
        SOME info =>
          fm |+ (fn.fn_name,
                 GENLIST (\i. T) (LENGTH info.fpi_invoke_params))
      | NONE => fm)
      FEMPTY functions
End

(* Top-level readonly memory args analysis.
   Iterates rma_fixpoint_step until no change (OWHILE).
   Returns map from function name → list of bools (T = readonly). *)
Definition rma_analyze_def:
  rma_analyze (fn_meta : (string, invoke_fn_meta) fmap)
              (ctx : ir_context) =
    let functions = ctx.ctx_functions in
    let infos = FOLDL (\fm fn.
      fm |+ (fn.fn_name, collect_param_info fn_meta fn))
      FEMPTY functions in
    let dfgs = FOLDL (\fm fn.
      fm |+ (fn.fn_name, dfg_build_function fn))
      FEMPTY functions in
    let init = rma_init_state functions infos in
    let result = OWHILE (\(changed, _). changed)
      (\(_, st). rma_fixpoint_step functions infos dfgs st)
      (T, init) in
    case result of
      NONE => FEMPTY  (* non-termination: conservative *)
    | SOME (_, final_st) => final_st
End

(* Extract readonly parameter indices from the analysis result.
   Returns the list of indices that are readonly.
   Matches Python get_readonly_invoke_arg_idxs. *)
Definition rma_get_readonly_idxs_def:
  rma_get_readonly_idxs (result : (string, bool list) fmap)
                        (fn_name : string) =
    case FLOOKUP result fn_name of
      NONE => ([] : num list)
    | SOME state =>
        FLAT (MAPi (\i is_ro. if is_ro then [i] else []) state)
End

(* Check if a specific parameter index is readonly. *)
Definition rma_is_readonly_def:
  rma_is_readonly (result : (string, bool list) fmap)
                  (fn_name : string)
                  (param_idx : num) =
    MEM param_idx (rma_get_readonly_idxs result fn_name)
End
