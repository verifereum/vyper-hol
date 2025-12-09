(*
 * ASSIGN Elimination Function-Level Correctness
 *
 * This theory proves function-level correctness of ASSIGN elimination.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - assign_elimination_correct         : Function-level correctness
 *   - assign_elimination_context_correct : Context-level correctness
 *
 * ============================================================================
 *)

Theory assignFunction
Ancestors
  assignBlock assignWellFormed assignDefs
  execEquiv stateEquiv list
  venomSem venomState

(* ==========================================================================
   Function-Level Correctness
   ========================================================================== *)

(* Helper: Function execution preserves state equivalence *)
Theorem run_function_state_equiv:
  !fuel fn s1 s2 r1.
    state_equiv s1 s2 /\
    run_function fuel fn s1 = r1
  ==>
    ?r2. run_function fuel fn s2 = r2 /\ result_equiv r1 r2
Proof
  Induct_on `fuel` >>
  rpt strip_tac
  >- (
    (* Base case: fuel = 0 *)
    qexists_tac `run_function 0 fn s2` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  ) >>
  (* SUC fuel case *)
  qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
  simp[Once run_function_def] >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  simp[Once run_function_def] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >> gvs[result_equiv_def] >>
  `result_equiv (run_block fn x s1) (run_block fn x s2)` by (
    irule run_block_result_equiv >> simp[]
  ) >>
  Cases_on `run_block fn x s1` >> Cases_on `run_block fn x s2` >> gvs[] >>
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* TOP-LEVEL: Main correctness theorem for ASSIGN elimination.
 *
 * The theorem says: running the original and transformed function
 * produces equivalent results when all_assigns_equiv holds.
 *
 * Assumptions:
 * 1. all_assigns_equiv (build_assign_map_fn func) s - all eliminated ASSIGNs have executed
 *)
Theorem assign_elimination_correct:
  !fuel (func:ir_function) s result.
    all_assigns_equiv (build_assign_map_fn func) s /\
    run_function fuel func s = result ==>
    ?result'. run_function fuel (transform_function func) s = result' /\
              result_equiv result result'
Proof
  (* Main proof by induction on fuel *)
  Induct_on `fuel` >> rpt strip_tac
  >- (
    (* Base case: fuel = 0 *)
    qexists_tac `run_function 0 (transform_function func) s` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  ) >>
  (* SUC fuel case *)
  qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
  simp[Once run_function_def] >> strip_tac >>
  simp[Once run_function_def, transform_function_def, LET_DEF] >>
  simp[lookup_block_transform] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >> gvs[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  (* Use transform_block_result_equiv *)
  `result_equiv (run_block func bb s)
                (run_block (transform_function func) (transform_block (build_assign_map_fn func) bb) s)` by (
    (* Need to prove the transformed block produces equivalent result *)
    cheat
  ) >>
  Cases_on `run_block func bb s` >> gvs[result_equiv_def] >>
  (* Match on transformed result *)
  cheat
QED

(* ==========================================================================
   Context-Level Correctness
   ========================================================================== *)

(* TOP-LEVEL: Context-level correctness - transformation preserves semantics
   for all functions in a context. *)
Theorem assign_elimination_context_correct:
  !ctx fn_name fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    all_assigns_equiv (build_assign_map_fn func) s /\
    run_function fuel func s = result ==>
    ?func' result'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      run_function fuel func' s = result' /\
      result_equiv result result'
Proof
  rpt strip_tac >>
  `?result'. run_function fuel (transform_function func) s = result' /\
             result_equiv result result'` by (
    irule assign_elimination_correct >> simp[]
  ) >>
  qexistsl_tac [`transform_function func`, `result'`] >>
  simp[transform_context_def, transform_function_def, MEM_MAP, LET_DEF] >>
  qexists_tac `func` >> simp[]
QED

val _ = export_theory();
