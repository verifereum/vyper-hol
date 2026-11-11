(* Live-scope resource transport for the actual internal entry. *)
Theory bodyIntCallActualEntryResource
Ancestors
  bodyIntCallEntryTransport bodyIntCallPrologueResource bodyIntCallBodyTrace
  intCallCallee context compileEnv venomState finite_map list
Libs
  monadsyntax

Theorem local_region_update_not_scope_ptr:
  not_scope_ptr ce scopes x ==>
  (local_region ce scopes (update_var x w s) n b sz <=>
   local_region ce scopes s n b sz)
Proof
  simp[not_scope_ptr_def, local_region_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem mat_inv_fresh_assignment:
  mat_inv fn ce env st s lo mr /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  st.cs_next_id <= st'.cs_next_id ==>
  mat_inv fn ce env st'
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) lo mr
Proof
  strip_tac >>
  `not_scope_ptr ce [env] (STRING #"%" (toString st.cs_next_var))` by
    (irule localPtrsPropsTheory.local_ptrs_rel_fresh_not_scope_ptr >>
     qexistsl_tac [`fn`, `s`, `st`] >> fs[mat_inv_def]) >>
  `fresh_vars_wrt st'
    (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule emitHelperPropsTheory.fresh_vars_wrt_advance >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> fs[mat_inv_def]) >>
  `local_ptrs_rel fn ce [env]
    (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule localPtrsPropsTheory.local_ptrs_rel_update_var >> fs[mat_inv_def]) >>
  `alloca_inv (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
     fs[mat_inv_def, update_var_def]) >>
  fs[mat_inv_def] >>
  simp[local_region_update_not_scope_ptr, update_var_def] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem mat_fixed_region_assignment:
  compile_fixed_region_with_id nbytes st = ((id,buf),st') /\
  mat_inv fn ce env st s lo mr /\
  mat_pending ce env st s lo mr caps ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand buf.buf_operand s' = SOME 0w /\
    mat_inv fn ce env st' s' lo mr /\
    mat_pending ce env st' s' lo mr caps /\
    mat_frame st s s'
Proof
  strip_tac >>
  drule immutableWordExecutionTheory.compile_fixed_region_execution >> strip_tac >>
  drule compile_fixed_region_with_id_result >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) 0w s` >>
  simp[] >> conj_tac
  >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (irule mat_inv_fresh_assignment >> simp[]) >>
  conj_tac
  >- (irule mat_pending_stage_transport >>
      qexistsl_tac [`s`, `st`] >> simp[update_var_def] >> rpt strip_tac
      >- (fs[not_fresh_at_def] >>
          metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
      fs[lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def]) >>
  simp[mat_frame_fresh_update]
QED

Theorem internal_entry_prefix_stages:
  compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) ==>
  ?rb stb next stp.
    (if has_rb then
       do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st0 = (rb,stb) /\
    compile_internal_param_decls params (if has_rb then 1 else 0) stb =
      ((caps,next),stp) /\
    emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc,sc) /\
    stage_ce = ce with
      <|ce_return_buf := (case (rb,ce.ce_return_buf) of
           (SOME p,SOME (MemLoc off sz)) => SOME (PtrVar p sz)
         | _ => ce.ce_return_buf);
        ce_return_pc := SOME (PtrVar rpc 0)|>
Proof
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem internal_entry_prefix_shapes:
  compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) ==>
  stage_ce.ce_vars = ce.ce_vars /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  MAP FST caps = MAP FST params /\
  st0.cs_next_var <= sc.cs_next_var /\
  sc.cs_blocks = st0.cs_blocks /\
  sc.cs_current_bb = st0.cs_current_bb /\
  isPREFIX st0.cs_current_insts sc.cs_current_insts
Proof
  strip_tac >> drule internal_entry_prefix_stages >> strip_tac >>
  drule internal_param_decls_projection >> strip_tac >>
  qpat_x_assum `emit_op RETPC_PARAM _ _ = _` mp_tac >>
  Cases_on `has_rb` >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >> gvs[] >>
  simp[listTheory.APPEND_ASSOC]
QED

Theorem internal_fixed_region_shape:
  compile_fixed_region_with_id n st = ((id,buf),st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  st'.cs_next_id = st.cs_next_id + 1 /\
  isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  simp[compile_fixed_region_with_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem internal_ctor_entry_stage_shapes:
  compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) /\
  compile_fixed_region_with_id n sc = ((id,buf),sr) /\
  materialize_internal_params stage_ce caps sr = (ce2,sm) /\
  (case rt of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) sm = ((),st1) ==>
  stage_ce.ce_vars = ce.ce_vars /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  MAP FST caps = MAP FST params /\
  st0.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_var <= sr.cs_next_var /\
  sr.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_var <= st1.cs_next_var /\
  sr.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= st1.cs_next_id /\
  isPREFIX st0.cs_current_insts sc.cs_current_insts /\
  isPREFIX sc.cs_current_insts sr.cs_current_insts /\
  isPREFIX sr.cs_current_insts sm.cs_current_insts /\
  isPREFIX sm.cs_current_insts st1.cs_current_insts
Proof
  strip_tac >>
  drule internal_entry_prefix_shapes >> strip_tac >>
  drule internal_fixed_region_shape >> strip_tac >>
  drule materialize_internal_params_shape >> strip_tac >>
  drule internal_scratch_shape >> strip_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem internal_entry_prefix_resources:
  compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory ==>
  ?t mr.
    run_inst_seq (emitted_insts st0 sc) s0 = OK t /\
    mat_inv func stage_ce env sc t caller.vs_alloca_next mr /\
    mat_pending stage_ce env sc t caller.vs_alloca_next mr caps /\
    mat_frame st0 s0 t /\
    t.vs_alloca_next = caller.vs_alloca_next /\
    (!n1 n2 b1 sz1 b2 sz2.
      n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
      regions_disjoint b1 sz1 b2 sz2) /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) args))
Proof
  strip_tac >> drule internal_entry_prefix_shapes >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule_all internal_capture_materialization_entry >> strip_tac >>
  qexistsl_tac [`t`, `mr`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `t = s0 with vs_vars := _` SUBST1_TAC >>
      drule setup_callee_frontier >> simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem run_entry_segments:
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  isPREFIX sb.cs_current_insts sc.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  run_inst_seq (emitted_insts sb sc) t = OK u ==>
  run_inst_seq (emitted_insts sa sc) s = OK u
Proof
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    simp[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc` by
    metis_tac[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all exprLoweringPropsTheory.emitted_insts_append >>
  strip_tac >> metis_tac[exprLoweringPropsTheory.run_inst_seq_append]
QED

Theorem internal_entry_resource_run:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) ==>
  ?t mr.
    run_inst_seq (emitted_insts st0 st1) s0 = OK t /\
    mat_inv func ce2 env st1 t caller.vs_alloca_next mr /\
    mat_frame st0 s0 t /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) args))
Proof
  strip_tac >> Cases_on `ctor /\ imm_len > 0`
  >- suspend "constructor" >>
  drule compile_internal_function_entry_no_reservation >>
  disch_then (fn th => fs[th, comp_bind_def, comp_return_def]) >>
  pairarg_tac >> gvs[] >> PairCases_on `pr` >> gvs[] >>
  drule_all internal_prologue_resource_run >> simp[]
QED

Resume internal_entry_resource_run[constructor]:
  gvs[] >> `0 < imm_len` by decide_tac >>
  drule_all compile_internal_function_entry_ctor_stages >> strip_tac >>
  PairCases_on `ar` >>
  rename1 `compile_internal_entry_prefix _ _ _ _ = ((stage_ce,caps,rpc),sc)` >>
  rename1 `compile_fixed_region_with_id _ sc = ((rid,buf),sr)` >>
  rename1 `materialize_internal_params stage_ce caps sr = (ce2,sm)` >>
  `(case rt of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
     | NONE => return ()) sm = ((),st1)` by
    (Cases_on `rt` >> Cases_on `ce.ce_returns_count > 0` >> fs[comp_return_def]) >>
  drule_all internal_ctor_entry_stage_shapes >> strip_tac >>
  `internal_stack_size stage_ce params = internal_stack_size ce params` by
    (irule internal_stack_size_vars >> simp[]) >>
  drule_all internal_entry_prefix_resources >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 sc) s0 = OK captured` >>
  drule_all mat_fixed_region_assignment >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sc sr) captured = OK reserved` >>
  `ALL_DISTINCT (MAP FST caps)` by fs[internal_args_rel_def] >>
  drule_all internal_prologue_segment_members >>
  disch_then (qspec_then `sr` strip_assume_tac) >>
  `reserved.vs_alloca_next = caller.vs_alloca_next` by
    (drule immutableWordExecutionTheory.compile_fixed_region_execution >>
     disch_then (qspec_then `captured` mp_tac) >>
     simp[] >> strip_tac >> gvs[update_var_def]) >>
  `reserved.vs_alloca_next +
    internal_stack_size stage_ce (MAP (\c. (FST c,FST (SND c))) caps)
    < dimword (:256)` by simp[] >>
  `!i. MEM i (DROP (LENGTH sr.cs_current_insts) sm.cs_current_insts) ==>
    MEM i (fn_insts func)` by fs[exprLoweringPropsTheory.emitted_insts_def] >>
  drule_all materialize_run_compact >> strip_tac >>
  rename1 `mat_inv func ce2 env sm materialized _ _` >>
  `run_inst_seq (emitted_insts sr sm) reserved = OK materialized` by
    fs[exprLoweringPropsTheory.emitted_insts_def] >>
  drule_all internal_scratch_materialization_inv >> strip_tac >>
  rename1 `mat_inv func ce2 env st1 landing _ _` >>
  qexistsl_tac [`landing`, `mr`] >> simp[] >> conj_tac
  >- suspend "sequence" >> suspend "frame"
QED

Resume internal_entry_resource_run[sequence]:
  `isPREFIX st0.cs_current_insts sr.cs_current_insts` by
    (irule rich_listTheory.IS_PREFIX_TRANS >>
     qexists_tac `sc.cs_current_insts` >> simp[]) >>
  `isPREFIX st0.cs_current_insts sm.cs_current_insts` by
    (irule rich_listTheory.IS_PREFIX_TRANS >>
     qexists_tac `sr.cs_current_insts` >> simp[]) >>
  irule run_entry_segments >> qexistsl_tac [`sm`, `materialized`] >> simp[] >>
  irule run_entry_segments >> qexistsl_tac [`sr`, `reserved`] >> simp[] >>
  irule run_entry_segments >> qexistsl_tac [`sc`, `captured`] >> simp[]
QED

Resume internal_entry_resource_run[frame]:
  irule mat_frame_trans >> qexistsl_tac [`sc`, `captured`] >> simp[] >>
  conj_tac >- (fs[not_fresh_at_def] >> decide_tac) >>
  irule mat_frame_trans >> qexistsl_tac [`sr`, `reserved`] >> simp[] >>
  conj_tac >- (fs[not_fresh_at_def] >> decide_tac) >>
  irule mat_frame_trans >> qexistsl_tac [`sm`, `materialized`] >>
  simp[] >> fs[not_fresh_at_def] >> decide_tac
QED

Finalise internal_entry_resource_run

(* Resource attachment uses determinism of a fixed successful instruction run. *)
Theorem internal_entry_landing_resources:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK t ==>
  ?mr. mat_inv func ce2 env st1 t caller.vs_alloca_next mr /\
    mat_frame st0 s0 t /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) args))
Proof
  strip_tac >> drule_all internal_entry_resource_run >>
  strip_tac >> gvs[] >> qexists_tac `mr` >> simp[]
QED

Theorem internal_entry_protected_landing:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK t /\
  (!a k. P a k ==> a + k <= caller.vs_alloca_next) /\
  (!a k. P a k ==>
    mem_bytes_at a k s0.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b z. staged b z /\
      b <= w2n (EL ((if has_rb then 1 else 0) + i) args) /\
      w2n (EL ((if has_rb then 1 else 0) + i) args) + sz <= b + z) ==>
  mat_frame st0 s0 t /\
  (!a k. P a k ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!n p k. local_region ce2 [env] t n p k ==>
    caller.vs_alloca_next <= p \/
    ?b z. staged b z /\ b <= p /\ p + k <= b + z)
Proof
  strip_tac >> drule_all internal_entry_landing_resources >> strip_tac >>
  simp[] >> conj_tac
  >- (drule setup_callee_frontier >> strip_tac >>
      qpat_x_assum `mat_frame st0 s0 t` mp_tac >>
      simp[mat_frame_def] >> metis_tac[]) >>
  fs[mat_inv_def] >>
  qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
  qpat_x_assum `!i off sz. _ ==> ?b z. staged _ _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >- simp[] >>
  disj2_tac >> gvs[] >> metis_tac[]
QED
