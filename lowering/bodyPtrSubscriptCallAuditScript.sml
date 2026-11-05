(* Internal-call feasibility: finite unvisited-node measure, not a new
   safety predicate. The graph witness must stay fixed across induction. *)
Theory bodyPtrSubscriptCallAudit
Ancestors
  vyperTypeCallStackSoundness vyperTypeCallGraphSoundness list arithmetic

Theorem unvisited_list_push_decreases:
  !nodes stk callee.
    MEM callee nodes /\ ~MEM callee stk ==>
    LENGTH (FILTER (\n. ~MEM n (callee::stk)) nodes) <
    LENGTH (FILTER (\n. ~MEM n stk) nodes)
Proof
  `!ns stk c.
     LENGTH (FILTER (\n. n <> c /\ ~MEM n stk) ns) <=
     LENGTH (FILTER (\n. ~MEM n stk) ns)` by
    (Induct >> simp[] >> rpt gen_tac >>
     first_x_assum (qspecl_then [`stk`, `c`] assume_tac) >>
     Cases_on `h = c` >> Cases_on `MEM h stk` >> simp[]) >>
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `h = callee`
  >- (gvs[] >>
      qpat_x_assum `!ns stk c. _` (qspecl_then [`nodes`, `stk`, `callee`] mp_tac) >>
      simp[]) >>
  gvs[] >> strip_tac >>
  first_x_assum drule_all >>
  Cases_on `MEM h stk` >> simp[]
QED

Theorem safe_call_unvisited_measure:
  call_evaluation_safe cx (callee::calls) ==>
  ?edges owner ancestors.
    cx.stk = owner::ancestors /\
    irreflexive (TC (call_edge_rel edges)) /\
    functions_follow_call_graph edges cx /\
    call_edge_rel edges owner callee /\
    LENGTH (FILTER (\n. ~MEM n (callee::cx.stk)) (MAP SND edges)) <
    LENGTH (FILTER (\n. ~MEM n cx.stk) (MAP SND edges))
Proof
  strip_tac >>
  `~MEM callee cx.stk` by
    (drule call_evaluation_safe_target_not_mem >> simp[]) >>
  fs[call_evaluation_safe_def] >>
  `LENGTH (FILTER (\n. ~MEM n (callee::cx.stk)) (MAP SND edges)) <
   LENGTH (FILTER (\n. ~MEM n cx.stk) (MAP SND edges))` by
    (irule unvisited_list_push_decreases >> simp[] >>
     gvs[call_edge_rel_def, MEM_MAP] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `edges` >> gvs[]
QED

(* Minimal slice / candidate interface, NOT an established safety theorem:
   key = Call (BaseT (UintT 256)) (IntCall (NONE,fn)) [] NONE.
   Select a callable declaration (mut,F,[],[],BaseT(UintT 256),body).
   The smaller-callee IH would be body_stmts_ptr_ok
     (cx with stk updated_by CONS (NONE,fn)) body,
   uniformly over target frames. It cannot be added as a target hypothesis.

   Checked decreasing boundary: safe_call_unvisited_measure supplies a finite
   edge-list witness and strict decrease of unvisited MAP SND edges. One must
   fix that witness for an entire induction: reselecting existential edges at
   each call does NOT validate a well-founded induction. Existing
   call_evaluation_safe_push_callable proves the same graph can be retained
   by its proof (vyperTypeCallStackSoundness 350-368), but its public conclusion
   re-existentializes it. A future strengthened induction must quantify over
   fixed edges, functions_follow_call_graph and calls_follow_call_graph.

   Obligation table (D = discharged, IH = proposed induction, M = missing):
   D caller declaration metadata: body_inv fixes func ids, param types,
     func_info and return types to build_* of supported tops (bodySim 61-87).
   D source recursion guard and callee call safety: existing
     call_evaluation_safe_target_not_mem / push_body. Not a syntax-size IH.
   D zero-arg prefix: compile_call (exprLowering 2626-2667) compiles [], then
     allocates return storage and emits INVOKE; a word return can still use
     returns_count > 0 and store_multi_results. Do NOT assume no buffer.
   M callee target identity/entry: derive lookup_function at internal_fn_label,
     setup_callee and entry after parameter instructions from actual lowered
     unit. body_inv alone is not a relation between arbitrary cs and source.
   M callee frame: body_inv for callee cenv, stmt_state_rel and expr_sim_inv
     after scopes become [env]. Empty args simplify env, not target setup.
   M return buffer provenance: compile_alloc_buffer coverage must be passed as
     PG = MAP (op_prov G) ops, then entry_prov must install it for callee PARAM.
     ptr_safe_step_invoke (ptrSafeRun 478) starts callee with FEMPTY provenance
     and tn with t_var := FEMPTY. Caller ghost_inv cannot just be reused.
   M return PC: ghost_inv requires untainted ce_return_pc; connect actual
     callee return convention to it, not a guessed caller variable.
   M storage taint: memory/storage components survive INVOKE entry, but
     stor_taint_ok uses cx. Need equality of cx_dead across pushed context and
     establish callee entry; on exit use callee invariant, not caller framing.
   IH callee body: counted execution, return-specific RetQ, storage invariant,
     and no new taint on caller live regions. A normal expression post alone
     does not express return behavior, nor exclude caller-region clobbering.
   M caller ghost preservation: ghost_step INVOKE restricts caller G and t_var
     only at outputs (ptrSafeRun 60-77), but imports callee memory/storage
     taint. Need returned memory framing for ghost_kept and fresh outputs;
     caller variable preservation by itself does not prove it.

   Exact target consumer: ptr_safe_step_invoke requires ptr_inst_ok plus
   ptr_safe_blocks at the actual setup_callee cs. gasIntCallBody's existing
   consumer gas_exempt_intcall_body is erased/S1, NOT counted pointer safety.
   No available counted pointer INVOKE/callee-return transport was used here.
   The measure experiment is positive; the complete callee-entry/return
   contract remains unproved. No broad independent safety theorem or frozen
   subscript proof follows from this audit. Stop for architecture review.
*)
