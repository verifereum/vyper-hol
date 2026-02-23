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
 *  - Function names in ctx_functions are assumed distinct. lookup_function
 *    returns the first match; correctness proofs will likely need
 *    ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions).
 *)

Theory fcgAnalysis
Ancestors
  venomInst dfgAnalysis pred_set

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

(* Process a single unvisited function: scan for invokes, record edges *)
Definition fcg_visit_def:
  fcg_visit ctx fn_name fcg =
    case lookup_function fn_name ctx.ctx_functions of
      NONE => ([], fcg)
    | SOME func =>
        let targets = fcg_scan_function func in
        let new_callees = REVERSE (MAP FST targets) in
        let fcg' = fcg_record_edges fn_name targets fcg in
        let fcg'' = fcg' with
          fcg_reachable := SNOC fn_name fcg'.fcg_reachable in
        (new_callees, fcg'')
End

(* Helper: stricter predicate gives shorter or equal FILTER *)
Theorem filter_length_mono:
  (!x. P x ==> Q x) ==>
  LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls)
Proof
  strip_tac >> Induct_on `ls` >> simp[] >>
  rw[] >> simp[] >> res_tac >> simp[]
QED

(* Helper: adding a name to visited can only shrink or keep the filter *)
Theorem filter_visited_mono:
  LENGTH (FILTER (\f. ~MEM f.fn_name (name :: visited)) fns) <=
  LENGTH (FILTER (\f. ~MEM f.fn_name visited) fns)
Proof
  irule filter_length_mono >> simp[]
QED

(* Helper: if name matches some element, adding it strictly shrinks the filter *)
Theorem filter_visited_shrink:
  ~MEM name visited /\
  MEM name (MAP (\f. f.fn_name) fns) ==>
  LENGTH (FILTER (\f. ~MEM f.fn_name (name :: visited)) fns) <
  LENGTH (FILTER (\f. ~MEM f.fn_name visited) fns)
Proof
  Induct_on `fns` >> rw[] >> gvs[] >> simp[filter_visited_mono] >>
  Cases_on `MEM h.fn_name visited` >> gvs[] >> simp[] >>
  irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
  qexists_tac `LENGTH (FILTER (\f. ~MEM f.fn_name visited) fns)` >>
  simp[] >> irule filter_length_mono >> simp[]
QED

(* Helper: lookup_function success implies the name is in the function list *)
Theorem lookup_function_mem:
  lookup_function name fns = SOME func ==>
  MEM name (MAP (\f. f.fn_name) fns)
Proof
  Induct_on `fns` >> simp[lookup_function_def] >>
  rpt strip_tac >> rw[] >> gvs[] >>
  Cases_on `h.fn_name = name` >> gvs[]
QED

(* Helper: lookup_function failure implies name not in function list *)
Theorem lookup_function_not_mem:
  lookup_function name fns = NONE ==>
  ~MEM name (MAP (\f. f.fn_name) fns)
Proof
  Induct_on `fns` >> simp[lookup_function_def] >>
  rpt strip_tac >>
  Cases_on `h.fn_name = name` >> gvs[]
QED

(* Helper: if name not in function names, the neq conjunct is redundant *)
Theorem filter_neq_redundant:
  ~MEM name (MAP (\f. f.fn_name) fns) ==>
  FILTER (\f. f.fn_name <> name /\ P f) fns =
  FILTER P fns
Proof
  Induct_on `fns` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

(* DFS worklist traversal
 * stack: function names left to visit
 * visited: function names already processed
 * fcg: accumulator for results
 *
 * Terminates because:
 *  - visited names are skipped (stack shrinks)
 *  - new names are added to visited (unvisited set shrinks)
 *  - measure: (|context functions not in visited|, |stack|) lexicographic *)
Definition fcg_dfs_def:
  fcg_dfs ctx [] visited fcg = fcg /\
  fcg_dfs ctx (fn_name::stack) visited fcg =
    if MEM fn_name visited then
      fcg_dfs ctx stack visited fcg
    else
      let (new_callees, fcg') = fcg_visit ctx fn_name fcg in
      fcg_dfs ctx (new_callees ++ stack) (fn_name :: visited) fcg'
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\(ctx, stack, visited, fcg).
       (LENGTH (FILTER (\f. ~MEM f.fn_name visited) ctx.ctx_functions),
        LENGTH stack))` >>
  rpt strip_tac >- simp[] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >-
  (* NONE: new_callees = [], filter unchanged, stack shrinks *)
  (disj2_tac >>
   fs[fcg_visit_def] >> gvs[] >>
   imp_res_tac lookup_function_not_mem >>
   simp[filter_neq_redundant]) >>
  (* SOME: filter strictly shrinks *)
  (disj1_tac >>
   imp_res_tac lookup_function_mem >>
   irule filter_visited_shrink >> simp[])
End

(* ==========================================================================
   Top-level Entry Point
   ========================================================================== *)

Definition fcg_analyze_def:
  fcg_analyze ctx =
    case ctx.ctx_entry of
      NONE => fcg_empty
    | SOME entry_name =>
        fcg_dfs ctx [entry_name] [] fcg_empty
End

val _ = export_theory();
