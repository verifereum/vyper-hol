(* Seam 2 joint induction, a family leaf of the call step: nested internal calls, under the call-graph descent premise. *)
Theory bodyIntCallFamCallInt
Ancestors
  bodyIntCallJointContract bodyIntCallSeamDefs bodyIntCallJointPackage
  bodyIntCallJointCallCore bodyIntCallProducerOrder bodyIntCallSource
  bodyIntCallFamCallIntEntry bodyIntCallFamCallIntReturn

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

(* The callee's package env takes its module-level fields from the root
   env, which agrees with every frame's env outside the locals. *)
Theorem intcall_res_module_pins:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s ==>
  cenv_module_pins fp.jc_tops ce
Proof
  strip_tac >>
  fs[intcall_frame_ok_def, intcall_expr_res_def, bodySimTheory.same_frame_def] >>
  qpat_x_assum `cenv_module_pins _ _` mp_tac >>
  qpat_x_assum `_ = fp.jc_root_ce` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[cenv_module_pins_def]
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
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  rename1 `Call ann (IntCall nsid) cargs dflt` >>
  rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  PairCases_on `nsid` >>
  drule_all body_intcall_source_selection >> strip_tac >>
  qpat_x_assum `nsid0 = NONE` SUBST_ALL_TAC >>
  rename1 `IntCall (NONE,name)` >>
  `cenv_module_pins fp.jc_tops ce` by metis_tac[intcall_res_module_pins] >>
  `MEM (NONE,name) (int_calls_expr (Call ann (IntCall (NONE,name)) cargs dflt))`
    by simp[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all_then strip_assume_tac intcall_nested_graph_producers >>
  qspecl_then [`fp`,`ce`,`env`,`ann`,`name`,`cargs`,`dflt`,`ty`,`sa`,`sb`,
               `vv`,`s`,`es`,`mut`,`args`,`ret`,`ss`,`rr`]
    mp_tac intcall_nested_entry >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  `?rcn rbs pvs. ce.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs)`
    by metis_tac[pairTheory.ABS_PAIR_THM] >>
  qspecl_then [`fp`,`ce`,`env`,`ann`,`name`,`cargs`,`dflt`,`ty`,`sa`,`sb`,
               `vv`,`s`,`es`,`mut`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,
               `es1`,`t`,`rcn`,`rbs`,`pvs`] mp_tac intcall_nested_return >>
  impl_tac >- (
    simp[] >> rpt strip_tac >>
    qspecl_then [`fp.jc_edges`,`fp.jc_tops`,`fp.jc_ctx`,`fp.jc_func`,`ce`,
                 `fp.jc_cx`,`env`,`name`,`cargs`,`sa`,`sb`,`vv`,`s`,`es`,`mut`,
                 `args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,`t`,`callee`,
                 `entered`,`rcn`,`rbs`,`pvs`] mp_tac intcall_callee_packaging >>
    impl_tac >- fs[intcall_frame_ok_def] >>
    disch_then irule >> metis_tac[]) >>
  simp[]
QED
