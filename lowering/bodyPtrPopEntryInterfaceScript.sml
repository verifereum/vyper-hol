Theory bodyPtrPopEntryInterface
Ancestors
  exprLoweringProps

(* alloca_room constrains the SAME func as the fragment judgment. This
   rules out an independently constructed containing function unless it also
   belongs to ctx; fn_has_code alone would not establish that obligation. *)
Theorem pop_entry_function_lookup:
  stmt_state_rel ctx func ce cx es s ==>
  lookup_function func.fn_name ctx.ctx_functions = SOME func
Proof
  simp[stmt_state_rel_def, alloca_room_def]
QED

(* Complete entry audit, using the SAME func/ctx/sa in each premise:

   bodyPtrPreds 20-25: body_expr_ptr_ok universally quantifies d,PG,tops,ctx,
   func,cenv,env,ty,es, then requires body_inv and expr_body_pre. It does not
   itself require supported_expr of e. body_base_target_ptr_ok at 92-99 is T
   at roots, inherited at Attribute, and requires the universal index judgment
   only when successful base evaluation exists. A concrete target fixture must
   discharge that universal judgment, not assume one successful trace suffices.

   bodySim 61-88 body_inv: supported_program tops; lowered runtime/deploy unit
   with ctx=unit.cu_context and target policy; module code, metadata, ctor and
   allocation-local mode agreement. No direct func premise at THIS level.
   exprSimHypsDefs 148-160 expr_body_pre: simulation invariant and typing,
   byte widths/allocation limits, call safety/main-module restrictions, no
   EVM-run, ABI target occurrence/dynamicity. No general source occurrence of
   e in tops or equality connecting sa with source lowering is stated here.

   bodyPtrDefs 298-311 expr_vv_sim_ptr entry (267-282 for value version):
   - exact compile_expr cenv ty e sa=(vv,sb), or lower_value=(op,sb);
   - fn_has_code sa sb func and fn_inst_ids_distinct func;
   - local_ptrs_reserved cenv sa, no DALLOCA in ctx, no constructor;
   - return buffer/PC Var reservations at sa;
   - source gas_admissible (value version includes read_result);
   - stmt_state_rel ctx func cenv cx es s0;
   - ghost_inv d cenv cx es G0 tn0 s0, runtime not halted;
   - runtime block=sa.cs_current_bb, index=LENGTH sa.cs_current_insts.
   All are antecedents, not freely supplied by body_inv.

   fragExec 112-118 fn_has_code: emitted blocks must be found in func, and
   sb's current instruction list prefixes a block in func. It does not alone
   assert source occurrence or sa compiler reachability. Distinct IDs adds a
   constraint on that SAME function, not a link to an independent fragment.

   exprLoweringProps 412-422 stmt_state_rel includes state_rel, alloca_inv,
   alloca_room, fmp_room, immutable separation/base and allocation sizes.
   CRITICAL: alloca_room 245-254 explicitly requires lookup_function of func
   in ctx, plus finite/acyclic reachable callees and allocation budget. The
   checked pop_entry_function_lookup projects this SAME-function obligation.
   fmp_room 258-267 supplies conditional scratch-margin inequalities.
   compileEnv 944-953 local_backed only constrains allocation witnesses or
   disjointness for locals; it is not itself a compiler-origin theorem.

   Consequences: entry func is in the lowered context via body_inv AND the
   state relation. An independent standalone containing function outside ctx
   cannot satisfy the full entry. The earlier arbitrary-function architectural
   claim is false. Nevertheless no premise says sa is a reachable compiler
   state or e occurs as source. A code-language exclusion theorem over ALL
   instruction blocks of the lowered ctx could still apply to arbitrary
   embedded fragments; proving it remains separate global work.

   Recommendation: ancestor review must correct the membership rationale,
   then compare a context-code invariant with the operational route. Neither
   a full-entry fixture nor a frozen-target counterexample is established by
   this audit. Do not infer exclusion from membership alone, and do not reject
   it on the disproved assertion that entry func is independent of ctx. *)
