(* Seam 2 joint induction step: calls and pops. *)
Theory bodyIntCallJointCall
Ancestors
  bodyIntCallJointContract supportedExprs bodyIntCallSemanticEntry
  bodySimAugPlaceScopes stmtSimAugAssignPlaceStorage bodyIntCallJointCallSource
  exprSimExtCallCase

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

(* A genuine evaluation boundary: the first argument captures the array,
   while the second pops it.  Reading happens after both evaluations. *)
Theorem intcall_deferred_pop_probe[local]:
  FST (bind
    (eval_expr_results cx
      [Name (ArrayT (BaseT BoolT) (Dynamic 2)) "x";
       Pop (BaseT BoolT) (NameTarget "x")])
    (read_results cx)
    (es with scopes := [FEMPTY |+ ("x",
      <| assignable := T; type := ArrayTV (BaseTV BoolT) (Dynamic 2);
         value := ArrayV (DynArrayV [BoolV T; BoolV F]);
         popped := [] |>)])) =
  INL [ArrayV (DynArrayV [BoolV T]); BoolV F]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem intcall_pure_results_storage:
  !args tops cx es r ee tr.
    supported_pure_exprs tops args /\
    eval_expr_results cx args es = (r,ee) ==>
    get_storage cx ee tr = get_storage cx es tr
Proof
  Induct >> rpt gen_tac
  >- simp[vyperInterpreterTheory.evaluate_def,
          vyperStateTheory.return_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def,
       supported_pure_expr_def, vyperStateTheory.bind_def] >>
  Cases_on `eval_expr cx h es` >>
  rename1 `eval_expr cx h es = (head,mid)` >>
  Cases_on `head` >> simp[] >> strip_tac >>
  drule_all aug_place_pure_eval_storage >> strip_tac >>
  gvs[AllCaseEqs(), vyperStateTheory.return_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem intcall_memory_read_scopes:
  ee.scopes = es.scopes ==>
  FST (read_result cx (PlaceR (MemoryPlace name path)) ee) =
  FST (read_result cx (PlaceR (MemoryPlace name path)) es)
Proof
  strip_tac >>
  Cases_on `lookup_scopes name es.scopes` >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.read_place_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.bind_def,
       vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_sum_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rename1 `read_memory_path entry path` >>
  Cases_on `vyperState$read_memory_path entry path` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem intcall_pure_results_memory_read:
  supported_pure_exprs tops args /\
  eval_expr_results cx args es = (r,ee) ==>
  FST (read_result cx (PlaceR (MemoryPlace name path)) ee) =
  FST (read_result cx (PlaceR (MemoryPlace name path)) es)
Proof
  strip_tac >> irule intcall_memory_read_scopes >>
  drule_all aug_place_pure_results_scopes >> simp[]
QED

(* A pure child may write its fresh allocations, but not an earlier window. *)
Theorem intcall_pure_below_frontier_memory:
  vv_post ctx func ce cx e es sa sb s0 ee tv vv u /\
  ~expr_has_effect e /\ off + len <= s0.vs_alloca_next /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     sa.cs_next_id <= inst.inst_id /\
     FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
     s0.vs_alloca_next <= b) ==>
  mem_bytes_at off len u.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac >> drule_all vv_post_pure_memory_frame >> strip_tac >>
  first_x_assum irule >> rpt strip_tac >>
  simp[compileEnvTheory.regions_disjoint_def] >>
  first_x_assum drule_all >> decide_tac
QED

(* An earlier located result is framed by its actual allocation or local
   witness; reused allocation sites in the child need no frontier bound. *)
Theorem intcall_pure_child_located_memory:
  vv_at ce cx ty a b es r (LocatedValue vt p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  b.cs_next_id <= c.cs_next_id /\
  intcall_expr_cont fp ce env es c s ee d u /\
  vv_post fp.jc_ctx fp.jc_func ce cx child es c d s ee child_r child_vv u /\
  ~expr_has_effect child /\ cx = fp.jc_cx ==>
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.vv_at_def] >>
  strip_tac >> gvs[]
  >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (off,sz)` >>
      `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory` by
        (fs[intcall_expr_cont_def] >> first_x_assum irule >>
         goal_assum (drule_at Any) >> simp[] >>
         qexists `aid` >> simp[] >> decide_tac) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> sym_tac >> first_x_assum irule >> simp[])
  >- (drule_all vv_post_pure_memory_frame >> strip_tac >>
      rename1 `local_region ce es.scopes s n off sz` >>
      `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory` by
        (qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` irule >>
         goal_assum (drule_at Any)) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> sym_tac >> first_x_assum irule >> simp[]) >>
  simp[valueEncodingTheory.mem_bytes_at_def]
QED

(* Deferred reads depend only on the source places, not on gas observations. *)
Theorem intcall_read_result_source_frame:
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr. get_storage cx ee tr = get_storage cx es tr) ==>
  FST (read_result cx r ee) = FST (read_result cx r es)
Proof
  strip_tac >>
  Cases_on `?tr slot tv. r = PlaceR (StoragePlace tr slot tv)`
  >- (gvs[vyperStateTheory.read_result_def, vyperStateTheory.read_place_def,
          vyperStorageBackendTheory.read_storage_slot_eq] >>
      Cases_on `decode_value (get_storage cx es tr) (w2n slot) tv` >> simp[]) >>
  irule exprSimSubscriptArraySourceTheory.read_result_nonstorage_frame >>
  simp[] >> metis_tac[]
QED

Theorem intcall_pure_child_read_result:
  supported_pure_expr tops child /\
  eval_expr cx child es = (res,ee) /\
  read_result cx r es = (INL v,es) ==>
  read_result cx r ee = (INL v,ee)
Proof
  strip_tac >>
  `ee.scopes = es.scopes` by
    (drule_all aug_place_pure_expr_scopes >> simp[]) >>
  `ee.immutables = es.immutables` by
    (drule_all intcall_pure_expr_immutables >> simp[]) >>
  `!tr. get_storage cx ee tr = get_storage cx es tr` by
    (gen_tac >> drule_all aug_place_pure_eval_storage >> simp[]) >>
  drule_all intcall_read_result_source_frame >>
  disch_then (qspec_then `r` mp_tac) >>
  Cases_on `read_result cx r ee` >>
  drule vyperStateTheory.read_result_state >> simp[]
QED

(* The endpoint's immutable separation, not an old allocation-frontier
   bound, protects an initialized constructor immutable from a pure child. *)
Theorem intcall_pure_child_immutable_memory:
  vv_post ctx func ce cx child es sa sb s ee r vv u /\
  ~expr_has_effect child /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
             NONE => FEMPTY
           | SOME imms => get_source_immutables ce.ce_module imms) name =
    SOME (tv,v) ==>
  mem_bytes_at off (type_memory_size tv) u.vs_memory =
  mem_bytes_at off (type_memory_size tv) s.vs_memory
Proof
  strip_tac >> drule_all vv_post_pure_memory_frame >> strip_tac >>
  qpat_x_assum `!off len. _` irule >>
  `stmt_state_rel ctx func ce cx ee u` by
    fs[loweringPostsTheory.vv_post_def] >>
  pop_assum mp_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def] >>
  strip_tac >> rpt strip_tac >> first_x_assum drule_all >>
  simp[] >> metis_tac[]
QED

(* Captured-read equality allows arbitrary source result forms and the
   annotation on a located value need not equal its semantic type. *)
Theorem intcall_vv_at_frame:
  vv_at ce cx ty a b es r vv s /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!aid q. FLOOKUP s.vs_allocas aid = SOME q ==>
           FLOOKUP u.vs_allocas aid = SOME q) /\
  (!n off sz. local_region ce ee.scopes u n off sz <=>
              local_region ce es.scopes s n off sz) /\
  b.cs_next_id <= d.cs_next_id ==>
  vv_at ce cx ty a d ee r vv u
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_at_def, contextTheory.vv_operand_def,
       loweringPostsTheory.expr_val_at_def] >>
  strip_tac >> rpt strip_tac >> first_x_assum drule_all >>
  strip_tac >> simp[]
  >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (off,sz)` >>
      disj1_tac >> qexistsl [`aid`, `off`, `sz`] >> gvs[] >>
      first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[])
  >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (off,sz)` >>
      disj1_tac >> qexistsl [`aid`, `off`, `sz`] >> gvs[] >>
      first_assum ACCEPT_TAC)
  >> disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem intcall_vv_own_frame:
  vv_own ce cx ty a b es r vv s /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!aid q. FLOOKUP s.vs_allocas aid = SOME q ==>
           FLOOKUP u.vs_allocas aid = SOME q) /\
  (!n off sz. local_region ce ee.scopes u n off sz ==>
              local_region ce es.scopes s n off sz) /\
  b.cs_next_id <= d.cs_next_id ==>
  vv_own ce cx ty a d ee r vv u
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_own_def, contextTheory.vv_operand_def,
       loweringPostsTheory.expr_val_own_def] >>
  strip_tac >> rpt strip_tac >> first_x_assum drule_all >>
  strip_tac >> simp[] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (off,sz)` >>
  disj1_tac >> qexistsl [`aid`, `off`, `sz`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[] >> metis_tac[]
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
