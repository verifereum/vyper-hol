(* Initial allocation resources from the runtime validator. *)
Theory entryValidatedResources
Ancestors
  entryInitialResources vyperLoweringCorrect allocaHistory fcgPostorder fcgCorrectnessProof venomMemProofs vyperCompiler
  venomWf venomInst fcgDefs list exprLoweringProps

Theorem validated_entry_alloca_room:
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME func /\
  s.vs_alloca_next = 0 ==>
  alloca_room ctx func s
Proof
  strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  `ctx_wf ctx` by
    (simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, MEM_MAP] >>
     metis_tac[lookup_function_MEM, lookup_function_result_name]) >>
  `func.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `fcg_is_reachable (fcg_analyze ctx) name` by
    (irule fcg_analyze_reachable_complete_proof >>
     simp[fcg_path_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_mem]) >>
  irule initial_alloca_room >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable (fcg_analyze ctx) g` by
        metis_tac[reachable_fcg_acyclic_tc_rank] >>
      metis_tac[reachable_fcg_acyclic_no_reachable_cycle]) >>
  metis_tac[lowering_context_ok_alloca_budget]
QED
