(*
 * Function Call Graph (FCG) Analysis
 *
 * Computes which functions call which via INVOKE instructions,
 * starting from the entry function. Tracks:
 *  - Callees: function name -> list of callee function names
 *  - Call sites: function name -> INVOKE instructions that call it
 *  - Reachable: function names reachable from entry
 *
 *
 * API contract:
 *  - Use fcg_get_callees / fcg_get_call_sites / fcg_is_reachable to query
 *    results; these return sensible defaults for absent keys.
 *  - Do not inspect fmap domains directly; maps are sparse (only populated
 *    for functions with at least one edge). Python pre-initializes empty
 *    entries for every visited function, but the getter-based API hides
 *    this difference.
 *  - Well-formed IR is assumed: every INVOKE's first operand is a Label,
 *    and every callee label names a function in the context. Malformed
 *    cases are silently skipped; future well-formedness predicates should
 *    rule them out.
 *)

Theory fcgAnalysis
Ancestors
  venomInst dfgAnalysis

(* ==========================================================================
   FCG Analysis Result Type
   ========================================================================== *)

Datatype:
  fcg_analysis = <|
    fcg_callees : (string, string list) fmap;
    fcg_call_sites : (string, instruction list) fmap;
    fcg_reachable : string list
  |>
End

Definition fcg_empty_def:
  fcg_empty = <|
    fcg_callees := FEMPTY;
    fcg_call_sites := FEMPTY;
    fcg_reachable := []
  |>
End

(* ==========================================================================
   Query Helpers
   ========================================================================== *)

Definition fcg_get_callees_def:
  fcg_get_callees fcg fn_name =
    case FLOOKUP fcg.fcg_callees fn_name of
      NONE => []
    | SOME callees => callees
End

Definition fcg_get_call_sites_def:
  fcg_get_call_sites fcg fn_name =
    case FLOOKUP fcg.fcg_call_sites fn_name of
      NONE => []
    | SOME sites => sites
End

Definition fcg_is_reachable_def:
  fcg_is_reachable fcg fn_name = MEM fn_name fcg.fcg_reachable
End

Definition fcg_get_unreachable_def:
  fcg_get_unreachable ctx fcg =
    FILTER (\f. ~MEM f.fn_name fcg.fcg_reachable) ctx.ctx_functions
End

(* ==========================================================================
   Instruction Scanning
   ========================================================================== *)

(* Extract (callee_name, instruction) pairs from INVOKE instructions.
 * Note: Python asserts that INVOKE's first operand is always a Label.
 * Here we silently skip malformed INVOKEs; a well-formedness predicate
 * should guarantee this case never arises. *)
Definition get_invoke_targets_def:
  get_invoke_targets [] = [] /\
  get_invoke_targets (inst::rest) =
    case inst.inst_opcode of
      INVOKE =>
        (case inst.inst_operands of
           (Label lbl)::_ => (lbl, inst) :: get_invoke_targets rest
         | _ => get_invoke_targets rest)
    | _ => get_invoke_targets rest
End

(* Scan all blocks of a function for INVOKE instructions *)
Definition fcg_scan_function_def:
  fcg_scan_function func =
    get_invoke_targets (fn_insts func)
End

(* ==========================================================================
   DFS Traversal
   ========================================================================== *)

(* Record edges from a single function's invoke targets into the analysis *)
Definition fcg_record_edges_def:
  fcg_record_edges fn_name [] fcg = fcg /\
  fcg_record_edges fn_name ((callee, inst)::rest) fcg =
    let callees = fcg_get_callees fcg fn_name in
    let sites = fcg_get_call_sites fcg callee in
    let fcg' = fcg with <|
      fcg_callees := fcg.fcg_callees |+ (fn_name,
        if MEM callee callees then callees else SNOC callee callees);
      fcg_call_sites := fcg.fcg_call_sites |+ (callee,
        if MEM inst sites then sites else SNOC inst sites)
    |> in
    fcg_record_edges fn_name rest fcg'
End

(* DFS worklist traversal
 * fuel: bound on recursion depth (set to number of functions in context)
 * stack: function names left to visit
 * visited: function names already processed
 * fcg: accumulator for results *)
Definition fcg_dfs_def:
  fcg_dfs ctx 0 stack visited fcg = fcg /\
  fcg_dfs ctx (SUC fuel) [] visited fcg = fcg /\
  fcg_dfs ctx (SUC fuel) (fn_name::stack) visited fcg =
    if MEM fn_name visited then
      fcg_dfs ctx (SUC fuel) stack visited fcg
    else
      case lookup_function fn_name ctx.ctx_functions of
        NONE => fcg_dfs ctx fuel stack (fn_name :: visited) fcg
      | SOME func =>
          let targets = fcg_scan_function func in
          let new_callees = MAP FST targets in
          let fcg' = fcg_record_edges fn_name targets fcg in
          let fcg'' = fcg' with
            fcg_reachable := SNOC fn_name fcg'.fcg_reachable in
          fcg_dfs ctx fuel (REVERSE new_callees ++ stack) (fn_name :: visited) fcg''
End

(* ==========================================================================
   Top-level Entry Point
   ========================================================================== *)

Definition fcg_analyze_def:
  fcg_analyze ctx =
    case ctx.ctx_entry of
      NONE => fcg_empty
    | SOME entry_name =>
        fcg_dfs ctx (LENGTH ctx.ctx_functions) [entry_name] [] fcg_empty
End

val _ = export_theory();
