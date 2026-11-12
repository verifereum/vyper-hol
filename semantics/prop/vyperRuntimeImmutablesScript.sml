(*
 * A runtime call of a checked single-module contract writes no immutables.
 *)
Theory vyperRuntimeImmutables
Ancestors
  vyperInterpreter vyperState vyperTypeContract vyperCall vyperContext
  vyperCheckedRuntimeWriteSafety vyperRuntimeWriteSafetyFrame
  vyperRuntimeCallFrame rich_list

(* Intuition: st.immutables changes only through set_immutable, reached from
   write_place / pop_place on an ImmutablePlace, which lookup_global yields
   only for a name with no storage, transient or hashmap declaration.
   check_contract F checks every non-Deploy body and default argument of the
   (fully live) main module with no assignable bare globals, so every write
   target type-checks to a storage, transient or hashmap declaration. The
   entry is a checked External function or a getter; internal calls reach
   only Internal functions (lookup_callable_function F); eval_create keeps
   immutables (eval_create_preserves_scopes_immutables); external calls are
   oracle outcomes; constants are not evaluated outside deployment; error
   paths return am, and finalize_pending_deletions keeps immutables. *)
Theorem call_external_runtime_preserves_immutables:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  am'.immutables = am.immutables
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_external _ _ _ _ = _` mp_tac >>
  simp[call_external_def, call_external_trace_def] >>
  qabbrev_tac `src = find_function_module am tx.target tx.function_name` >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  `(case src of NONE => get_self_code cx | SOME sid => get_module_code cx (SOME sid)) =
    get_module_code cx src` by (Cases_on `src` >> simp[get_self_code_def]) >>
  simp[] >>
  Cases_on `get_module_code cx src` >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `lookup_exported_function cx am tx.function_name`
  >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `lookup_exported_function cx am tx.function_name = SOME entry` >>
  PairCases_on `entry` >>
  rename1 `lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,dflts,ret,bdy)` >>
  `?R. runtime_callable_writes_ok (get_module_code cx) R /\
       runtime_write_roots_resolve cx R /\
       EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
       stmts_writes_ok (runtime_write_root R) bdy` by
    (unabbrev_all_tac >> metis_tac[checked_singleton_runtime_write_safety]) >>
  `!st r st'. eval_exprs cx (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
      st = (r,st') ==> st'.immutables = st.immutables` by
    (metis_tac[cj 6 runtime_writes_frame_mutual, EVERY_DROP]) >>
  `!st r st'. eval_stmts cx bdy st = (r,st') ==>
      st'.immutables = st.immutables` by
    (metis_tac[cj 2 runtime_writes_frame_mutual]) >>
  Cases_on `call_external_function_trace orc gobs am cx nr mut ts [(NONE,tops)]
    args dflts tx.args bdy ret` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = result` >>
  PairCases_on `result` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (out,am1,requests,observations)` >>
  `am1.immutables = am.immutables` by
    (drule_all call_external_function_trace_runtime_frame >> simp[]) >>
  namedCases_on `out` ["value", "exc"]
  >- (simp[] >> strip_tac >> gvs[]) >>
  Cases_on `exc` >> simp[] >> strip_tac >> gvs[]
QED
