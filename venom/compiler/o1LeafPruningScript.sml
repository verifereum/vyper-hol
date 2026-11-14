(* A call-free entry is the only function retained by FCG pruning. *)
Theory o1LeafPruning
Ancestors
  fcgPruning fcgCorrectnessProof fcgDefs venomInst venomWf
  o1ScheduleDecompHelpers relation

Theorem prune_unit_fcg_leaf_entry:
  ctx_wf u.cu_context /\
  u.cu_context.ctx_entry = SOME e.fn_name /\
  lookup_function e.fn_name u.cu_context.ctx_functions = SOME e /\
  (!i. MEM i (fn_insts e) ==> i.inst_opcode <> INVOKE) ==>
  !f. MEM f
    (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context)).cu_context.ctx_functions
    ==> f = e
Proof
  rpt strip_tac >>
  `!callee. ~fn_directly_calls u.cu_context e.fn_name callee` by
    (simp[fn_directly_calls_def] >> metis_tac[]) >>
  drule (iffLR MEM_prune_unit_fcg_unreachable_functions) >> strip_tac >>
  drule_all fcg_analyze_reachable_sound_proof >> strip_tac >>
  `f.fn_name = e.fn_name` by
    (gvs[fcg_path_def] >>
     qpat_x_assum `RTC _ _ _` mp_tac >>
     once_rewrite_tac[RTC_CASES1] >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) u.cu_context.ctx_functions)` by
    gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  drule lookup_function_member_iff >>
  disch_then (qspec_then `e.fn_name` mp_tac) >>
  simp[] >> metis_tac[]
QED
