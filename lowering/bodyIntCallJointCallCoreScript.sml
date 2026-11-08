(* Helpers for the seam 2 joint induction call step and its family leaves. *)
Theory bodyIntCallJointCallCore
Ancestors
  bodyIntCallJointContract supportedExprs bodyIntCallSemanticEntry
  bodySimAugPlaceScopes stmtSimAugAssignPlaceStorage bodyIntCallJointCallSource
  exprSimExtCallCase stmtSimAugAssignPlaceMemory abiStaticAggregateProps
  gasSummary gasSummaryCompose gasExemptCert vyperState

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

(* Recover the ordinary value post from the producer's normal certificate. *)
Theorem intcall_vv_post_intro:
  vv_holds ce fp.jc_cx (post_value_type ce e) tv vv ee u /\
  vv_at ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u /\
  (post_value_type ce e <> expr_type e ==>
   vv_own ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u) /\
  (~expr_has_effect e ==> vv_storage_live fp.jc_cx vv ee u) /\
  intcall_expr_cont fp ce env es sa s ee sb u ==>
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee tv vv u
Proof
  simp[loweringPostsTheory.vv_post_def, intcall_expr_cont_def,
       intcall_joint_res_def] >> metis_tac[]
QED

Theorem intcall_expr_cont_frame:
  intcall_expr_cont fp ce env es sa s ee sb u ==>
  wb_frame ce es sa s u
Proof
  simp[intcall_expr_cont_def, loweringPostsTheory.wb_frame_def] >>
  metis_tac[]
QED

Theorem intcall_expr_cont_trans:
  intcall_joint_res fp ce env es a s /\
  intcall_expr_cont fp ce env es a s em b t /\
  intcall_expr_cont fp ce env em b t ee d u /\
  a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM em.scopes ==>
  intcall_expr_cont fp ce env es a s ee d u
Proof
  strip_tac >>
  `wb_frame ce es a s t` by metis_tac[intcall_expr_cont_frame] >>
  `wb_frame ce em b t u` by metis_tac[intcall_expr_cont_frame] >>
  `wb_frame ce es a s u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     conj_tac >- fs[intcall_joint_res_def] >>
     conj_tac >- (qexistsl [`em`, `b`, `t`] >> simp[]) >>
     qexistsl [`fp.jc_ctx`, `fp.jc_cx`, `fp.jc_func`] >>
     fs[intcall_joint_res_def]) >>
  fs[intcall_expr_cont_def, loweringPostsTheory.wb_frame_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
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

Theorem intcall_storage_holds_frame:
  storage_holds cx tr ty r w es s /\
  get_storage cx ee tr = get_storage cx es tr /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    storage_range_agree (get_storage cx ee tr)
      (if tr then contract_transient u else contract_storage u) w tv) ==>
  storage_holds cx tr ty r w ee u
Proof
  simp[loweringPostsTheory.storage_holds_def,
       vyperStorageBackendTheory.read_storage_slot_eq] >>
  rpt strip_tac >> goal_assum (drule_at Any) >> gvs[AllCaseEqs()]
QED

Theorem intcall_vv_storage_live_frame:
  vv_storage_live cx vv es s /\
  (!tr. get_storage cx ee tr = get_storage cx es tr) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s ==>
  vv_storage_live cx vv ee u
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_storage_live_def,
       contextTheory.vv_operand_def] >> metis_tac[]
QED

Theorem intcall_storage_holds_live_frame:
  storage_holds cx tr ty r w es s /\
  get_storage cx ee tr = get_storage cx es tr /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        storage_read_live cx tr (get_storage cx es tr) w tv) /\
  stmt_state_rel ctx func ce cx ee u ==>
  storage_holds cx tr ty r w ee u
Proof
  strip_tac >> irule intcall_storage_holds_frame >>
  reverse conj_tac >- (qexistsl [`es`, `s`] >> simp[]) >>
  rpt strip_tac >>
  irule accountsRelPropsTheory.storage_range_agree_of_live >>
  conj_tac
  >- fs[loweringPostsTheory.storage_holds_def,
        accountsRelPropsTheory.storage_range_agree_def] >>
  qexistsl [`cx`, `tr`] >> reverse conj_tac >- metis_tac[] >>
  Cases_on `tr` >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def,
     compileEnvTheory.state_rel_def, compileEnvTheory.storage_rel_def,
     compileEnvTheory.transient_rel_def, vyperStorageBackendTheory.get_storage_def] >>
  gvs[vfmStateTheory.lookup_account_def]
QED

Theorem intcall_storage_vv_holds_frame:
  vv_holds ce cx ty r (LocatedValue ann p) es s /\
  vv_storage_live cx (LocatedValue ann p) es s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  (!tr. get_storage cx ee tr = get_storage cx es tr) /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
  stmt_state_rel ctx func ce cx ee u ==>
  vv_holds ce cx ty r (LocatedValue ann p) ee u
Proof
  strip_tac >>
  fs[loweringPostsTheory.vv_holds_def,
     loweringPostsTheory.vv_storage_live_def] >>
  irule intcall_storage_holds_live_frame >> metis_tac[]
QED

Theorem intcall_immutable_holds_frame:
  immutable_holds ce cx ty r w es s /\
  ee.immutables = es.immutables /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  (ce.ce_is_ctor ==>
   !name off itv iv.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
              | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     mem_bytes_at off (type_memory_size itv) s.vs_memory =
     mem_bytes_at off (type_memory_size itv) u.vs_memory) ==>
  immutable_holds ce cx ty r w ee u
Proof
  simp[loweringPostsTheory.immutable_holds_def] >> strip_tac >>
  qexistsl [`name`, `off`, `itv`, `iv`, `k`, `tvt`, `v`] >> simp[] >>
  disj2_tac >> simp[] >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  qexistsl [`type_memory_size tvt`, `s.vs_memory`] >> simp[] >>
  `mem_bytes_at off (type_memory_size itv) s.vs_memory =
   mem_bytes_at off (type_memory_size itv) u.vs_memory` by metis_tac[] >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
  strip_tac >> sym_tac >> first_x_assum irule >> simp[]
QED

Theorem intcall_pure_child_immutable_holds:
  immutable_holds ce cx ty r w es s /\
  supported_pure_expr fp.jc_tops child /\
  eval_expr cx child es = (INL child_r,ee) /\
  vv_post ctx func ce cx child es a b s ee child_r child_vv u ==>
  immutable_holds ce cx ty r w ee u
Proof
  strip_tac >>
  `ee.immutables = es.immutables` by
    (drule_all intcall_pure_expr_immutables >> simp[]) >>
  irule intcall_immutable_holds_frame >>
  qexistsl [`es`, `s`] >> simp[] >> conj_tac
  >- (drule exprSimAttributeTheory.immutable_holds_read >> strip_tac >>
      drule_all intcall_pure_child_read_result >> strip_tac >> simp[]) >>
  rpt strip_tac >>
  `~expr_has_effect child` by
    metis_tac[supportedExprTraverseTheory.supported_pure_expr_effect_free] >>
  metis_tac[intcall_pure_child_immutable_memory]
QED

(* Representation transport uses the semantic type independently of the
   located annotation.  The extra typed-word equation is framed explicitly. *)
Theorem intcall_memory_vv_holds_frame:
  vv_holds ce cx ty r (LocatedValue ann p) es s /\
  p.ptr_location = LocMemory /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
  (!v tv w. read_result cx r es = (INL v,es) /\
     evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand p.ptr_operand s = SOME w ==>
     val_wf tv v /\
     mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory =
     mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory) /\
  (is_word_type ty ==> !tv w.
     evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand p.ptr_operand s = SOME w ==>
     mem_word_at (w2n w) u.vs_memory = mem_word_at (w2n w) s.vs_memory) ==>
  vv_holds ce cx ty r (LocatedValue ann p) ee u
Proof
  strip_tac >> fs[loweringPostsTheory.vv_holds_def] >> rpt strip_tac
  >>~- ([`val_in_memory _ _ _ _`],
        irule exprSimPropsTheory.val_in_memory_footprint_agree >> metis_tac[]) >>
  metis_tac[]
QED

Theorem intcall_stack_vv_holds_frame:
  vv_holds ce cx ty r (StackValue ann op) es s /\
  (!v. read_result cx r ee = (INL v,ee) <=>
       read_result cx r es = (INL v,es)) /\
  eval_operand op u = eval_operand op s /\
  (~is_word_type ty ==> !v tv w.
     read_result cx r es = (INL v,es) /\
     evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand op s = SOME w ==>
     val_wf tv v /\
     mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory =
     mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory) ==>
  vv_holds ce cx ty r (StackValue ann op) ee u
Proof
  simp[loweringPostsTheory.vv_holds_def,
       loweringPostsTheory.expr_val_rel_def] >> strip_tac >>
  qexists `v` >> simp[] >>
  Cases_on `is_word_type ty` >- fs[] >> fs[] >> rpt strip_tac >>
  irule exprSimPropsTheory.val_in_memory_footprint_agree >> metis_tac[]
QED

(* A successful value operand is retained by the child's actual normal path,
   including Label operands; no compiler-shape exclusion is needed. *)
Theorem intcall_vv_operand_normal_frame:
  vv_holds ce fp.jc_cx ty r vv es s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c x) /\
  intcall_expr_cont fp ce env es c s ee d u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) ==>
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s
Proof
  strip_tac >>
  `?w. eval_operand (vv_operand vv) s = SOME w` by
    (Cases_on `vv` >>
     fs[loweringPostsTheory.vv_holds_def,
        loweringPostsTheory.expr_val_rel_def, contextTheory.vv_operand_def] >>
     metis_tac[]) >>
  `eval_operand (vv_operand vv) u = SOME w` by
    (irule aug_place_saved_operand >>
     qexists `c` >>
     qexistsl [`fp.jc_ctx`, `fp.jc_func`, `F`, `n`, `s`] >>
     fs[intcall_expr_cont_def]) >> simp[]
QED

Theorem intcall_pure_child_stack_memory:
  vv_at ce fp.jc_cx ty a b es r (StackValue ann op) s /\
  ~is_word_type ty /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  eval_operand op s = SOME w /\
  b.cs_next_id <= c.cs_next_id /\
  intcall_expr_cont fp ce env es c s ee d u /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child es c d s ee child_r child_vv u /\
  ~expr_has_effect child ==>
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  `vv_at ce fp.jc_cx ty a b es r
     (LocatedValue ann (mk_ptr op LocMemory)) s` by
    (fs[loweringPostsTheory.vv_at_def,
        loweringPostsTheory.expr_val_at_def, contextTheory.mk_ptr_def] >>
     metis_tac[]) >>
  irule intcall_pure_child_located_memory >>
  goal_assum (drule_at Any) >> simp[contextTheory.mk_ptr_def] >>
  metis_tac[]
QED

Theorem intcall_pure_child_memory_word:
  vv_at ce fp.jc_cx ty a b es r (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ is_word_type ty /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  b.cs_next_id <= c.cs_next_id /\
  intcall_expr_cont fp ce env es c s ee d u /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child es c d s ee child_r child_vv u /\
  ~expr_has_effect child ==>
  mem_word_at (w2n w) u.vs_memory = mem_word_at (w2n w) s.vs_memory
Proof
  strip_tac >>
  `val_footprint tv v = 32` by
    (drule_all exprSimPropsTheory.word_tv_memory_size >> strip_tac >>
     `~is_bytestring_type ty` by
       metis_tac[exprSimConvertTheory.is_word_type_not_bytestring] >>
     metis_tac[exprSimAggregateChildrenTheory.evaluated_nonbytes_footprint]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
    (irule intcall_pure_child_located_memory >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[mem_word_at_bytes]
QED

Theorem intcall_pure_child_read_agreement:
  supported_pure_expr tops child /\
  eval_expr cx child es = (res,ee) ==>
  !v. read_result cx r ee = (INL v,ee) <=>
      read_result cx r es = (INL v,es)
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
  Cases_on `read_result cx r ee` >> Cases_on `read_result cx r es` >>
  imp_res_tac vyperStateTheory.read_result_state >> simp[]
QED

Theorem intcall_pure_child_vv_holds:
  vv_holds ce fp.jc_cx ty r vv es s /\
  vv_at ce fp.jc_cx ty a b es r vv s /\
  vv_storage_live fp.jc_cx vv es s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c x) /\
  b.cs_next_id <= c.cs_next_id /\
  supported_pure_expr fp.jc_tops child /\
  eval_expr fp.jc_cx child es = (INL child_r,ee) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child es c d s ee child_r child_vv u /\
  intcall_expr_cont fp ce env es c s ee d u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) ==>
  vv_holds ce fp.jc_cx ty r vv ee u
Proof
  strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (irule intcall_vv_operand_normal_frame >> metis_tac[]) >>
  `!v. read_result fp.jc_cx r ee = (INL v,ee) <=>
       read_result fp.jc_cx r es = (INL v,es)` by
    (irule intcall_pure_child_read_agreement >> metis_tac[]) >>
  `~expr_has_effect child` by
    metis_tac[supportedExprTraverseTheory.supported_pure_expr_effect_free] >>
  `!tr. get_storage fp.jc_cx ee tr = get_storage fp.jc_cx es tr` by
    (gen_tac >> drule_all aug_place_pure_eval_storage >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u` by
    fs[loweringPostsTheory.vv_post_def] >>
  Cases_on `vv`
  >- (rename1 `StackValue ann op` >>
      irule intcall_stack_vv_holds_frame >>
      qexistsl [`es`, `s`] >> fs[contextTheory.vv_operand_def] >>
      disch_tac >> rpt gen_tac >> strip_tac >> conj_tac
      >- (fs[loweringPostsTheory.vv_at_def,
             loweringPostsTheory.expr_val_at_def] >> metis_tac[]) >>
      sym_tac >> irule intcall_pure_child_stack_memory >> metis_tac[]) >>
  rename1 `LocatedValue ann p` >>
  Cases_on `p.ptr_location`
  >- (irule intcall_memory_vv_holds_frame >> simp[] >>
      qexistsl [`es`, `s`] >> fs[contextTheory.vv_operand_def] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> conj_tac
          >- (fs[loweringPostsTheory.vv_at_def] >> metis_tac[]) >>
          sym_tac >> irule intcall_pure_child_located_memory >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> irule intcall_pure_child_memory_word >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[loweringPostsTheory.vv_holds_def] >> metis_tac[])
  >- (irule intcall_storage_vv_holds_frame >>
      fs[contextTheory.vv_operand_def] >> metis_tac[]) 
  >- (irule intcall_storage_vv_holds_frame >>
      fs[contextTheory.vv_operand_def] >> metis_tac[]) 
  >- (fs[loweringPostsTheory.vv_holds_def, contextTheory.vv_operand_def] >>
      irule intcall_pure_child_immutable_holds >> metis_tac[]) >>
  fs[loweringPostsTheory.vv_holds_def]
QED

(* The exact value certificate is independent of the child's own result.
   In particular the W capacity witnesses are retained, not reframed. *)
Theorem intcall_pure_child_value_certificate:
  vv_holds ce fp.jc_cx ty r vv es s /\
  vv_at ce fp.jc_cx ty a b es r vv s /\
  (ty <> origin_ty ==> vv_own ce fp.jc_cx ty a b es r vv s) /\
  vv_storage_live fp.jc_cx vv es s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
   (case vv of StackValue _ _ => T
             | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   !tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
     ?w off len. eval_operand (vv_operand vv) s = SOME w /\
       off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
       off + len < dimword (:256) /\
       (fp.jc_lo <= off \/
        ?base size. fp.jc_staged base size /\ base <= off /\
                    off + len <= base + size)) /\
  b.cs_next_id <= c.cs_next_id /\ b.cs_next_var <= c.cs_next_var /\
  c.cs_next_id <= d.cs_next_id /\ c.cs_next_var <= d.cs_next_var /\
  supported_pure_expr fp.jc_tops child /\
  eval_expr fp.jc_cx child es = (INL child_r,ee) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child es c d s ee child_r child_vv u /\
  intcall_joint_res fp ce env es c s /\
  intcall_expr_cont fp ce env es c s ee d u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) ==>
  vv_holds ce fp.jc_cx ty r vv ee u /\
  vv_at ce fp.jc_cx ty a d ee r vv u /\
  (ty <> origin_ty ==> vv_own ce fp.jc_cx ty a d ee r vv u) /\
  vv_storage_live fp.jc_cx vv ee u /\
  (!x. vv_operand vv = Var x ==> not_fresh_at d x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
   (case vv of StackValue _ _ => T
             | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   !tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
     ?w off len. eval_operand (vv_operand vv) u = SOME w /\
       off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
       off + len < dimword (:256) /\
       (fp.jc_lo <= off \/
        ?base size. fp.jc_staged base size /\ base <= off /\
                    off + len <= base + size))
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at c x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (irule intcall_vv_operand_normal_frame >> metis_tac[]) >>
  `!v. read_result fp.jc_cx r ee = (INL v,ee) <=>
       read_result fp.jc_cx r es = (INL v,es)` by
    (irule intcall_pure_child_read_agreement >> metis_tac[]) >>
  `ee.scopes = es.scopes` by
    (drule_all aug_place_pure_expr_scopes >> simp[]) >>
  `!name off len. local_region ce ee.scopes u name off len <=>
                 local_region ce es.scopes s name off len` by
    (rpt gen_tac >> irule stmtSimLogArgsTheory.log_frame_local_region >>
     fs[intcall_joint_res_def, intcall_expr_cont_def,
        loweringPostsTheory.wb_frame_def] >>
     conj_tac >-
       (qexists `c` >> simp[] >> rpt conj_tac >> rpt gen_tac >>
        strip_tac >> first_x_assum irule >> simp[] >>
        conj_tac >- (first_assum ACCEPT_TAC) >> qexists `aid` >> simp[]) >>
     qexistsl [`fp.jc_ctx`, `fp.jc_cx`, `fp.jc_func`] >> simp[]) >>
  conj_tac
  >- (irule intcall_pure_child_vv_holds >> metis_tac[]) >>
  conj_tac
  >- (irule intcall_vv_at_frame >> qexistsl [`b`, `es`, `s`] >>
      fs[intcall_expr_cont_def] >> metis_tac[]) >>
  conj_tac
  >- (strip_tac >> irule intcall_vv_own_frame >>
      qexistsl [`b`, `es`, `s`] >> fs[intcall_expr_cont_def] >> metis_tac[]) >>
  conj_tac
  >- (irule intcall_vv_storage_live_frame >> qexistsl [`es`, `s`] >>
      simp[] >> gen_tac >> drule_all aug_place_pure_eval_storage >> simp[]) >>
  conj_tac
  >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  gvs[]
QED

(* All typing and support clauses of expr_body_pre are state independent. *)
Theorem expr_body_pre_state_transport:
  expr_body_pre ce cx env e es /\ expr_sim_inv ce cx env ee ==>
  expr_body_pre ce cx env e ee
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def]
QED

Theorem intcall_gas_outcome_map_results:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result list evaluation_result) (es,s)
    (\res ee t. ?rs. res = INL rs /\ Q (INL (f rs)) ee t)
    (\res ee r. ?ex. res = INR ex /\ X ex ee r) ==>
  gas_outcome memory tops (ctx,func) (bind a (\rs. return (f rs))) (es,s)
    Q (\res ee r. ?ex. res = INR ex /\ X ex ee r)
Proof
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` strip_assume_tac)))
      >- (gvs[] >> qexists `marks` >> disj1_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl [`INL (f rs)`, `mid`, `OK t`] >>
          fs[gas_marked_exec_def, bind_def, return_def]) >>
      gvs[] >> qexists `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR ex`, `mid`, `r`] >>
      fs[gas_marked_exec_def, bind_def]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ef) (callee,tf)` >>
  qexists `marks` >> disj2_tac >> qexistsl [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_results >> simp[]
QED

Theorem intcall_gas_outcome_return:
  ~s.vs_halted /\ Q (INL v) (es with gas_obs := []) s ==>
  gas_outcome memory tops (ctx,func) (return v) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists `[]` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL v`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, return_def] >>
  irule fragGasModeTheory.gas_marked_path_from_mem >>
  simp[fragGasPathMemTheory.gas_path_mem_rules]
QED

Theorem intcall_compile_multi_vvs_prefix:
  !todo doneE doneV doneR es c s vvs d.
  (!de dv dr ee b u. P de dv dr ee b u ==>
     ~u.vs_halted /\ P de dv dr (ee with gas_obs := []) b u) /\
  (!e de dv dr ee b u vv b'.
     MEM e todo /\ P de dv dr ee b u /\
     cfn ce (expr_type e) e b = (vv,b') ==>
     gas_outcome memory tops (ctx,func) (eval_expr cx e) (ee,u)
       (\res ef t. ?r. res = INL r /\
         P (de ++ [e]) (dv ++ [vv]) (dr ++ [r]) ef b' t)
       (\res ef r. ?ex. res = INR ex /\ X ex ef r)) /\
  P doneE doneV doneR es c s /\
  compile_multi_vvs cfn ce todo c = (vvs,d) ==>
  gas_outcome memory tops (ctx,func) (eval_expr_results cx todo) (es,s)
    (\res ee u. ?rs. res = INL rs /\
       P (doneE ++ todo) (doneV ++ vvs) (doneR ++ rs) ee d u)
    (\res ee r. ?ex. res = INR ex /\ X ex ee r)
Proof
  Induct_on `todo`
  >- (rpt strip_tac >>
      gvs[exprLoweringTheory.compile_multi_vvs_def,
          compileEnvTheory.comp_return_def] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      irule intcall_gas_outcome_return >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[exprLoweringTheory.compile_multi_vvs_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
      AllCaseEqs()] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `cfn ce (expr_type h) h c = (hv,b)` >>
  rename1 `compile_multi_vvs cfn ce todo b = (tvs,d)` >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  irule exprSimSubscriptMapTheory.gas_outcome_bind_result_exec >>
  qexistsl [`\res ee r. ?ex. res = INR ex /\ X ex ee r`,
    `\res ee u. ?r. res = INL r /\
       P (doneE ++ [h]) (doneV ++ [hv]) (doneR ++ [r]) ee b u`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      irule intcall_gas_outcome_map_results >>
      simp[] >>
      qpat_x_assum `!doneE' doneV' doneR' es' c' s'' vvs' d'. _`
        (qspecl_then [`doneE ++ [h]`, `doneV ++ [hv]`, `doneR ++ [v]`]
          (irule o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC,
             listTheory.APPEND])) >>
      simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> simp[]) >>
  first_x_assum irule >> simp[] >> qexists `c` >> simp[]
QED

(* Unlike the membership-only interface, this boundary exposes the actual
   remaining compilation at every step, so its consumer can split code. *)
Theorem intcall_compile_multi_vvs_suffix:
  !todo doneE doneV doneR es c s vvs d.
  (!de dv dr rest ee b u. P de dv dr rest ee b u ==>
     ~u.vs_halted /\ P de dv dr rest (ee with gas_obs := []) b u) /\
  (!de dv dr e tail ee b u vv b' vs.
     whole = de ++ (e::tail) /\ P de dv dr (e::tail) ee b u /\
     cfn ce (expr_type e) e b = (vv,b') /\
     compile_multi_vvs cfn ce tail b' = (vs,d) ==>
     gas_outcome memory tops (ctx,func) (eval_expr cx e) (ee,u)
       (\res ef t. ?r. res = INL r /\
         P (de ++ [e]) (dv ++ [vv]) (dr ++ [r]) tail ef b' t)
       (\res ef r. ?ex. res = INR ex /\ X ex ef r)) /\
  whole = doneE ++ todo /\ P doneE doneV doneR todo es c s /\
  compile_multi_vvs cfn ce todo c = (vvs,d) ==>
  gas_outcome memory tops (ctx,func) (eval_expr_results cx todo) (es,s)
    (\res ee u. ?rs. res = INL rs /\
       P (doneE ++ todo) (doneV ++ vvs) (doneR ++ rs) [] ee d u)
    (\res ee r. ?ex. res = INR ex /\ X ex ee r)
Proof
  Induct_on `todo`
  >- (rpt strip_tac >>
      gvs[exprLoweringTheory.compile_multi_vvs_def,
          compileEnvTheory.comp_return_def] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      irule intcall_gas_outcome_return >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[exprLoweringTheory.compile_multi_vvs_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
      AllCaseEqs()] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `cfn ce (expr_type h) h c = (hv,b)` >>
  rename1 `compile_multi_vvs cfn ce todo b = (tvs,d)` >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  irule exprSimSubscriptMapTheory.gas_outcome_bind_result_exec >>
  qexistsl [`\res ee r. ?ex. res = INR ex /\ X ex ee r`,
    `\res ee u. ?r. res = INL r /\
       P (doneE ++ [h]) (doneV ++ [hv]) (doneR ++ [r]) todo ee b u`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      irule intcall_gas_outcome_map_results >> simp[] >>
      qpat_x_assum `!doneV' doneR' es' c' s'' vvs' d'. _`
        (qspecl_then [`doneV ++ [hv]`, `doneR ++ [v]`]
          (irule o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC,
             listTheory.APPEND])) >>
      simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qexists `c` >> simp[]
QED
