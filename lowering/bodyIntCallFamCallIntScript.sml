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

(* Located annotations describe the semantic layout, not necessarily the
   expression annotation used as the staging destination. *)
Theorem intcall_located_layout:
  vv_holds ce cx ty r (LocatedValue ann p) es s ==>
  ann = ty \/ (is_bytestring_type ty /\ is_bytestring_type ann)
Proof
  simp[loweringPostsTheory.vv_holds_def] >> metis_tac[]
QED

(* A genuine aggregate widening is not a bytestring-compatible store.
   This tests the type boundary only, not reachability of a complete run. *)
Theorem intcall_aggregate_layout_probe:
  ce.ce_func_return_type (nsid_to_string fid) =
    ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2) ==>
  post_value_type ce
    (Call (ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 2))
      (IntCall fid) args drv) =
    ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2) /\
  type_widens_to tenv
    (ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2))
    (ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 2)) /\
  ~(ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 2) =
      ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2) \/
    (is_bytestring_type (ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 2)) /\
     is_bytestring_type (ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2))))
Proof
  simp[loweringPostsTheory.post_value_type_def,
       exprLoweringTheory.lowered_value_type_def,
       compileEnvTheory.is_word_type_def,
       compileEnvTheory.is_bytestring_type_def,
       vyperTypeSystemTheory.type_widens_to_def,
       vyperTypeSystemTheory.arg_type_fits_def,
       vyperTypeSystemTheory.well_formed_type_def,
       vyperValueTheory.evaluate_type_def,
       wordsTheory.dimword_def, EVAL ``dimindex(:256)``] >> EVAL_TAC
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
