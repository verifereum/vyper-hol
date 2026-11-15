Theory contextStaticAbortRel
Ancestors
  contextCodegenRel staticAbortDefs

(* The generated pending-abort companion supplies progress after this cut;
   ordinary context obligations and their existing consumers stay unchanged. *)
Definition codegen_memory_obligations_abort_def:
  codegen_memory_obligations_abort Inv ctx cp <=>
    !fn inst vs1 vs2 fuel.
      Inv ctx fn inst vs1 /\
      MEM fn ctx.ctx_functions /\
      MEM inst (fn_insts fn) /\ ~in_revert_forward fn vs1 /\
      ~in_static_abort_prefix fn vs1 ==>
      source_memory_reads_disjoint cp inst vs1 /\
      context_source_memory_writes_disjoint cp inst vs1 /\
      (step_inst fuel ctx inst vs1 = OK vs2 ==>
       context_spill_step_safe cp vs1 vs2)
End

Definition codegen_context_obligations_abort_def:
  codegen_context_obligations_abort Inv ctx cp <=>
    generate_context_plan ctx = SOME cp /\
    context_plan_layout_wf cp /\
    codegen_ready ctx /\ ctx_wf ctx /\ fmp_lowered_context_wf ctx /\
    reachable_call_graph_acyclic ctx /\
    (!name efn. ctx.ctx_entry = SOME name /\
       lookup_function name ctx.ctx_functions = SOME efn ==>
       entry_fn_no_ret efn) /\
    codegen_memory_obligations_abort Inv ctx cp
End
