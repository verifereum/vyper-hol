(*
 * From per-function fuel bounds to a fuel bound for the whole context.
 *
 * Each function's runs are fuel-stable once its callees' are
 * (callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn).  The context's
 * call graph is acyclic on the functions reachable from the entry
 * (lowering_context_ok), so climbing the call graph's postorder from the
 * leaves gives one fuel G at which every reachable function is stable.
 *
 * TOP-LEVEL:
 *   fuel_stable_mono, ctx_fuel_bounded, run_context_fuel_stable
 *)

Theory fragFuelCtx
Ancestors
  fragFuel fcgPostorder fcgAnalysisProps fcgDefs vyperCompiler venomWf
  venomInst venomExecSemantics list

Theorem fuel_stable_mono:
  !G G' ctx fn. fuel_stable G ctx fn /\ G <= G' ==> fuel_stable G' ctx fn
Proof
  rw[fuel_stable_def] >>
  `run_blocks f ctx fn s = run_blocks G ctx fn s /\
   run_blocks G' ctx fn s = run_blocks G ctx fn s` by
    (conj_tac >> first_assum irule >> simp[]) >>
  simp[]
QED

Theorem lookup_function_fn_name[local]:
  !fns name fn. lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct >> rw[lookup_function_def, FIND_thm] >> gvs[lookup_function_def]
QED

Theorem lowering_context_ok_ctx_wf[local]:
  !ctx entry efn.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME entry /\
    lookup_function entry ctx.ctx_functions = SOME efn ==>
    ctx_wf ctx /\ wf_invoke_targets ctx /\
    reachable_fcg_acyclic ctx (fcg_analyze ctx)
Proof
  rpt gen_tac >> strip_tac >>
  fs[lowering_context_ok_def, ctx_wf_def, ctx_distinct_fn_names_def,
     ctx_has_entry_def, GSYM wf_invoke_targets_check_eq] >>
  drule lookup_function_mem >> simp[ctx_fn_names_def]
QED

(* The callees of a reachable function come earlier in the postorder. *)
Theorem callee_earlier[local]:
  !ctx entry name fn inst cname args callee n.
    ctx_wf ctx /\ wf_invoke_targets ctx /\
    reachable_fcg_acyclic ctx (fcg_analyze ctx) /\
    ctx.ctx_entry = SOME entry /\
    fcg_is_reachable (fcg_analyze ctx) name /\
    list_index name (fcg_postorder (fcg_analyze ctx) entry) = SOME n /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (cname, args) ==>
    fcg_is_reachable (fcg_analyze ctx) cname /\
    ?i. list_index cname (fcg_postorder (fcg_analyze ctx) entry) = SOME i /\
        i < n
Proof
  rpt gen_tac >> strip_tac >>
  `fn_directly_calls ctx name cname` by
    (simp[fn_directly_calls_def] >> qexistsl_tac [`inst`, `args`] >>
     fs[decode_invoke_def, AllCaseEqs()]) >>
  conj_tac >- metis_tac[fcg_reachable_direct_callee] >>
  qspecl_then [`fcg_analyze ctx`, `ctx`, `entry`, `name`, `cname`]
    mp_tac (Q.GENL [`fcg`, `ctx`, `entry`, `caller`, `callee`]
              reachable_fcg_acyclic_direct_edge_rank) >>
  simp[] >> strip_tac >> gvs[]
QED

(* Every reachable function whose postorder index is below n is stable at
   one common fuel. *)
Theorem ctx_fuel_bounded_upto[local]:
  !n ctx entry efn.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME entry /\
    lookup_function entry ctx.ctx_functions = SOME efn /\
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    ?G. !name fn i.
          fcg_is_reachable (fcg_analyze ctx) name /\
          list_index name (fcg_postorder (fcg_analyze ctx) entry) = SOME i /\
          i < n /\ lookup_function name ctx.ctx_functions = SOME fn ==>
          fuel_stable G ctx fn
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all lowering_context_ok_ctx_wf >> strip_tac >>
  last_x_assum (qspecl_then [`ctx`, `entry`, `efn`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  Cases_on `?name fn. fcg_is_reachable (fcg_analyze ctx) name /\
              list_index name (fcg_postorder (fcg_analyze ctx) entry) = SOME n /\
              lookup_function name ctx.ctx_functions = SOME fn`
  >- (
    fs[] >>
    `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
    `?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn` by
      metis_tac[] >>
    `callees_stable G ctx fn` by (
      rw[callees_stable_def] >>
      drule_all callee_earlier >> strip_tac >>
      first_x_assum irule >> metis_tac[]) >>
    qexists_tac `G + Kf` >> rpt strip_tac >>
    Cases_on `i = n`
    >- (
      `name' = name` by
        (gvs[list_index_def, INDEX_OF_eq_SOME]) >>
      gvs[]) >>
    irule fuel_stable_mono >> qexists_tac `G` >> simp[] >>
    first_x_assum irule >> qexistsl_tac [`i`, `name'`] >> simp[]) >>
  qexists_tac `G` >> rpt strip_tac >>
  Cases_on `i = n` >- metis_tac[] >>
  first_x_assum irule >> qexistsl_tac [`i`, `name`] >> simp[]
QED

Theorem ctx_fuel_bounded:
  !ctx entry efn.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME entry /\
    lookup_function entry ctx.ctx_functions = SOME efn /\
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    ?G. fuel_stable G ctx efn
Proof
  rpt strip_tac >>
  drule_all lowering_context_ok_ctx_wf >> strip_tac >>
  `fcg_is_reachable (fcg_analyze ctx) entry` by (
    irule fcg_analyze_reachable_complete >> fs[fcg_path_def, ctx_fn_names_def] >>
    drule lookup_function_mem >> simp[]) >>
  `MEM entry (fcg_postorder (fcg_analyze ctx) entry)` by
    metis_tac[fcg_reachable_mem_postorder] >>
  `?i. list_index entry (fcg_postorder (fcg_analyze ctx) entry) = SOME i` by
    (Cases_on `list_index entry (fcg_postorder (fcg_analyze ctx) entry)` >>
     gvs[list_index_def, INDEX_OF_eq_NONE]) >>
  qspecl_then [`SUC i`, `ctx`, `entry`, `efn`] mp_tac ctx_fuel_bounded_upto >>
  simp[] >> strip_tac >> qexists_tac `G` >> first_x_assum irule >>
  qexistsl_tac [`i`, `entry`] >> simp[]
QED

Theorem run_context_fuel_stable:
  !ctx entry efn.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME entry /\
    lookup_function entry ctx.ctx_functions = SOME efn /\
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    ?G. !f s. G <= f ==> run_context f ctx s = run_context G ctx s
Proof
  rpt strip_tac >> drule_all ctx_fuel_bounded >> strip_tac >>
  qexists_tac `G` >> rw[run_context_def, run_function_def] >>
  Cases_on `fn_entry_label efn` >> simp[] >>
  fs[fuel_stable_def] >> first_x_assum irule >>
  fs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
  Cases_on `efn.fn_blocks` >> fs[]
QED
