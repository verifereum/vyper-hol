(* Seam 2 joint induction, a family leaf of the call step: nested internal calls, under the call-graph descent premise. *)
Theory bodyIntCallFamCallInt
Ancestors
  bodyIntCallJointContract bodyIntCallProducerOrder bodyIntCallJointCallCore

(* The packaging theorem quantifies over every frame at the selected owner;
   the graph induction premise supplies all of them at once. *)
Theorem intcall_nested_graph_producers:
  intcall_frame_ok fp /\
  (!fp' ss.
     fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner calls /\
  MEM (src,name) calls /\
  get_module_code fp.jc_cx src = SOME tops /\
  lookup_callable_function fp.jc_cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) ==>
  call_stack_follows (call_edge_rel fp.jc_edges)
    ((src,name)::fp.jc_cx.stk) /\
  functions_follow_call_graph fp.jc_edges
    (fp.jc_cx with stk updated_by CONS (src,name)) /\
  calls_follow_call_graph fp.jc_edges (src,name)
    (function_int_calls dflts ss) /\
  (!fp'. fp'.jc_edges = fp.jc_edges /\ fp'.jc_owner = (src,name) ==>
     intcall_stmts_producer fp' ss)
Proof
  strip_tac >>
  `fp.jc_cx.stk = fp.jc_owner::fp.jc_ancestors /\
   call_stack_follows (call_edge_rel fp.jc_edges) fp.jc_cx.stk /\
   irreflexive (TC (call_edge_rel fp.jc_edges)) /\
   functions_follow_call_graph fp.jc_edges fp.jc_cx` by
    fs[intcall_frame_ok_def] >>
  drule_all callable_graph_descent >> simp[] >> strip_tac >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem intcall_intcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (!fp' ss.
     fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss) /\
  (?a nsid args dflt. e = Call a (IntCall nsid) args dflt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> reverse conj_tac
  >- (irule intcall_effect_map_producer >> metis_tac[]) >>
  cheat
QED
