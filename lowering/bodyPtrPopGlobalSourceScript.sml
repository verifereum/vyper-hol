Theory bodyPtrPopGlobalSource
Ancestors
  bodyPtrPopGlobalUnit bodyPtrPopGlobalLegality bodyPtrPopGlobalOperand
  vyperContext vyperState vyperTypeInvariants vyperTypeCallStackSoundness
  bodyPtrPreds vyperTypeCallGraphSoundness vyperTypeCallGraph

(* Closed diagnostic context fixes the actual module and declared slot layout.
   The enclosing expression is tested in its own nonrecursive call frame. *)
Definition pop_global_cx_def:
  pop_global_cx = empty_evaluation_context with
    <| stk := [(NONE,"probe")];
       sources := [(0w,pop_global_mods)];
       layouts := [(0w,([((NONE,"A"),0);((NONE,"B"),4)],[]))] |>
End

Theorem pop_global_source_module:
  get_module_code pop_global_cx NONE = SOME pop_global_tops
Proof
  EVAL_TAC
QED

Theorem pop_global_source_callable:
  lookup_callable_function pop_global_cx.in_deploy "replace" pop_global_tops =
    SOME (Nonpayable,F,[],[],BaseT (UintT 256),pop_global_body)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``pop_global_body``])
QED

Theorem pop_global_source_context_typed:
  context_well_typed pop_global_cx
Proof
  EVAL_TAC
QED

Theorem pop_global_source_operand:
  body_base_target_ptr_ok pop_global_cx pop_global_target
Proof
  irule pop_global_target_body_ptr >>
  simp[pop_global_source_module, pop_global_source_callable] >>
  qexists_tac `pop_global_tops` >>
  simp[pop_global_source_module, pop_global_source_callable]
QED

Theorem pop_global_source_module_cases:
  get_module_code pop_global_cx src = SOME ts <=>
    src = NONE /\ ts = pop_global_tops
Proof
  Cases_on `src` >>
  simp[pop_global_cx_def, empty_evaluation_context_def, empty_call_txn_def,
       get_module_code_def, pop_global_mods_def]
QED

Theorem pop_global_source_lookup_cases:
  lookup_callable_function F fn pop_global_tops = SOME (mut,nr,args,dflts,ret,bdy) <=>
    fn = "replace" /\ mut = Nonpayable /\ nr = F /\ args = [] /\ dflts = [] /\
    ret = BaseT (UintT 256) /\ bdy = pop_global_body
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``pop_global_body``]) >>
  Cases_on `fn = "replace"` >> simp[] >> metis_tac[]
QED

Theorem pop_global_source_functions_call_free:
  functions_follow_call_graph edges pop_global_cx
Proof
  simp[functions_follow_call_graph_def, pop_global_source_module_cases] >>
  rpt strip_tac >>
  gvs[pop_global_cx_def, empty_evaluation_context_def,
      pop_global_source_lookup_cases] >>
  EVAL_TAC
QED

Theorem pop_global_source_call_graph:
  irreflexive (TC (call_edge_rel [((NONE,"probe"),(NONE,"replace"))]))
Proof
  simp[relationTheory.irreflexive_def] >> gen_tac >> strip_tac >>
  drule relationTheory.TC_CASES1_E >>
  simp[call_edge_rel_def] >> strip_tac >>
  last_x_assum kall_tac >> gvs[] >> strip_tac >>
  drule relationTheory.TC_CASES1_E >> simp[call_edge_rel_def]
QED

Theorem pop_global_source_call_safe:
  call_evaluation_safe pop_global_cx [(NONE,"replace")]
Proof
  simp[call_evaluation_safe_def, pop_global_cx_def] >>
  qexists_tac `[((NONE,"probe"),(NONE,"replace"))]` >>
  simp[call_stack_follows_def, pop_global_source_call_graph,
       GSYM pop_global_cx_def, pop_global_source_functions_call_free,
       calls_follow_call_graph_def, call_edge_rel_def]
QED
