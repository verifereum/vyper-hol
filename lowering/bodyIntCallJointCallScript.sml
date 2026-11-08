(* Seam 2 joint induction step: calls and pops. *)
Theory bodyIntCallJointCall
Ancestors
  bodyIntCallJointContract supportedExprs bodyIntCallSemanticEntry

Theorem internal_prologue_module_pins:
  compile_internal_prologue ce params has_rb ret sa = ((ce',pc),sb) /\
  cenv_module_pins tops ce ==>
  cenv_module_pins tops ce'
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compileEnvTheory.compile_env_component_equality] >> strip_tac >>
  gvs[cenv_module_pins_def]
QED

(* Resource transport is independent of a value's representation.  The
   spatial and exact-operand frames are supplied by the call operation,
   rather than inferred from the ordinary value relation. *)
Theorem intcall_joint_res_frame:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  allocas_above fp.jc_lo u /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
     lookup_var x u = SOME w) /\
  (!n p k. local_region ce ee.scopes u n p k ==>
     local_region ce es.scopes s n p k) /\
  ee.immutables = es.immutables ==>
  intcall_joint_res fp ce env ee sb u
Proof
  strip_tac >>
  qpat_x_assum `intcall_joint_res _ _ _ _ _ _` mp_tac >>
  simp[intcall_joint_res_def] >> strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok ce sb u` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  `fp.jc_reserved fp.jc_rpc` by
    (fs[intcall_frame_ok_def]) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (rpt strip_tac >> metis_tac[])
  >- metis_tac[]
  >> gvs[]
QED

(* Separate the resource certificate from the ordinary value post. *)
Theorem intcall_expr_cont_vv_post:
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee tv vv u /\
  intcall_joint_res fp ce env ee sb u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  s.vs_alloca_next <= u.vs_alloca_next ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[intcall_expr_cont_def, loweringPostsTheory.vv_post_def] >> metis_tac[]
QED

(* Calls and pops are values, never mapping places. *)
Theorem intcall_effect_map_producer:
  ((?a tgt args dflt. e = Call a tgt args dflt) \/
   (?a tgt. e = Pop a tgt)) ==>
  intcall_map_producer fp e
Proof
  strip_tac >> gvs[intcall_map_producer_def,
    supported_pure_expr_def]
QED

Theorem intcall_supported_call_forms:
  supported_expr tops (Call ty target args dflt) ==>
  dflt = NONE /\
  ((?id. target = IntCall id) \/
   (?static skip sig opts. target = ExtCall static skip sig opts) \/
   (?flag. target = Send flag))
Proof
  Cases_on `dflt`
  >- (Cases_on `target` >>
      simp[supported_expr_def, supported_effect_expr_def,
           supported_pure_expr_def]) >>
  simp[supported_call_default_rejected]
QED

Theorem intcall_supported_pop_form:
  supported_expr tops (Pop ty target) ==>
  ?id. target = TopLevelNameTarget id /\
       supported_storage_dynamic_array tops id
Proof
  Cases_on `target` >>
  simp[supported_expr_def, supported_effect_expr_def,
       supported_pure_expr_def]
QED

(* Diagnostic boundary: after a later argument changes a local, the captured
   place reads the new value; an immediate result remains a snapshot. *)
Theorem intcall_deferred_read_probe[local]:
  read_results cx
    [PlaceR (MemoryPlace "x" []); Value (BoolV T)]
    (es with scopes := [FEMPTY |+ ("x",
      <| assignable := T; type := BaseTV BoolT;
         value := BoolV F; popped := [] |>)]) =
  (INL [BoolV F; BoolV T],
    es with scopes := [FEMPTY |+ ("x",
      <| assignable := T; type := BaseTV BoolT;
         value := BoolV F; popped := [] |>)])
Proof
  simp[vyperStateTheory.read_results_def, vyperStateTheory.read_result_def,
       vyperStateTheory.read_place_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.lookup_scopes_def, vyperStateTheory.read_memory_path_def,
       vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_sum_def,
       vyperStateTheory.evaluate_subscripts_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* L-call (C1.3.15): calls (internal, external, send) and pops, given the
   smaller expressions' producers and, by call-graph descent
   (callable_graph_descent), the statement producer of every frame whose
   owner has fewer call descendants under the same edges. *)
Theorem intcall_effect_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (!fp' ss.
     fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss) /\
  ((?a tgt args dflt. e = Call a tgt args dflt) \/ (?a tgt. e = Pop a tgt)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
