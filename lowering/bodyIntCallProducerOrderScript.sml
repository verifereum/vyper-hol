(* Fixed finite call-graph witnesses for recursive reachable simulation. *)
Theory bodyIntCallProducerOrder
Ancestors
  vyperTypeCallStackSoundness vyperTypeCallGraphSoundness vyperTypeCallGraph
  vyperInterpreter vyperContext vyperState relation pred_set list pair

Theorem finite_call_descendants:
  FINITE {y | TC (call_edge_rel edges) x y}
Proof
  irule SUBSET_FINITE >> qexists_tac `set (MAP SND edges)` >> simp[] >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  rename1 `TC (call_edge_rel edges) x target` >>
  `?z. call_edge_rel edges z target` by metis_tac[TC_CASES2] >>
  fs[call_edge_rel_def, MEM_MAP] >> metis_tac[SND]
QED

Theorem call_descendants_decrease:
  irreflexive (TC (call_edge_rel edges)) /\ call_edge_rel edges x y ==>
  CARD {z | TC (call_edge_rel edges) y z} <
  CARD {z | TC (call_edge_rel edges) x z}
Proof
  strip_tac >> irule CARD_PSUBSET >>
  simp[finite_call_descendants, PSUBSET_MEMBER, SUBSET_DEF] >>
  fs[irreflexive_def] >> metis_tac[TC_RULES]
QED

Theorem callable_graph_descent:
  cx.stk = owner::ancestors /\
  call_stack_follows (call_edge_rel edges) cx.stk /\
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cx /\
  calls_follow_call_graph edges owner calls /\ MEM (src,fn) calls /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  call_stack_follows (call_edge_rel edges)
    (cx with stk updated_by CONS (src,fn)).stk /\
  functions_follow_call_graph edges (cx with stk updated_by CONS (src,fn)) /\
  calls_follow_call_graph edges (src,fn) (function_int_calls dflts body) /\
  CARD {z | TC (call_edge_rel edges) (src,fn) z} <
  CARD {z | TC (call_edge_rel edges) owner z}
Proof
  strip_tac >>
  `call_edge_rel edges owner (src,fn)` by
    fs[calls_follow_call_graph_def, EVERY_MEM] >>
  conj_tac
  >- (simp[] >> qpat_x_assum `cx.stk = _` SUBST_ALL_TAC >>
      irule call_stack_follows_push >> simp[]) >>
  simp[functions_follow_call_graph_stk] >> conj_tac
  >- (fs[functions_follow_call_graph_def, calls_follow_call_graph_def] >>
      first_x_assum drule_all >> simp[function_int_calls_def, EVERY_APPEND]) >>
  irule call_descendants_decrease >> simp[]
QED
