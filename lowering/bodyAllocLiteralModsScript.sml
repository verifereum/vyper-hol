(* Linked nonword literals: the writer, physical frame and ghost posts
   describe the same deterministic buffer execution. *)
Theory bodyAllocLiteralMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyInvSplit bodyFullShadowBodyInv bodyPtrDefs
  loweringStateRelDefs ptrDiscipline compileEnv context exprLowering
  exprSimHypsDefs exprSimLiteralBuffer gasShadowState loweringPosts
  bodyFullLiteralNonword bodyFullLiteralBuffer
  bodyFullLiteralEndpoint bodyFullLiteralGhost exprBodyPreProps
  exprSimPtrLiteralPayload exprSimPtrLiteralBuffer exprSimPtrLiteralOps
  instSeqPtrLo gasShadowCompileStmtHelpers gasOutcomeFullMods
  exprSimUnwrapProps exprLoweringProps loweringSlice
  vyperStorageFootprint bodyPtrMakeArrayAllocBuffer fragGasOriginPtr fragGasSeqPtr
  gasSummary gasStorage gasContext gasOutcomeFull exprSimDefs exprSimProps exprSimMemDefs
  vfmConstants bodySimFull exprPtrCleanBufferPost allocLimits
  valueEncoding vyperTypeCallGraph vyperValueOperation exprSimSource
  gasShadow exprBodyPreTypingProps immutableRegionFrameProps
  valueEncodingProofs valueEncodingDefs vyperTypeSystem vyperTyping
  vyperInterpreter vyperState vyperAST vyperValue venomState venomInst
  venomExecSemantics finite_map pred_set words list

Theorem literal_ghost_zero[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at D 0 d cenv cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem literal_ghost_linked[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  ghost_inv_at D 0 d cenv cx es G' tn' t /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
                             FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
  tn'.t_mem SUBSET tn.t_mem /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory ==>
  ghost_inv_at_mods D lo d cenv cx (es with gas_obs := []) G' tn' t
Proof
  rw[ghost_inv_at_mods_def, ghost_inv_at_def] >>
  gvs[SUBSET_DEF, op_taint_def, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem literal_alloca_growth[local]:
  step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) ==>
     FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b)
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> simp[]
QED

Theorem literal_alloca_prefix[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
     FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b)
Proof
  strip_tac >> drule literal_ptr_bytelike_shape >> strip_tac >>
  drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  drule_then strip_assume_tac literal_alloca_growth >>
  drule_then strip_assume_tac literal_alloca_static_frame >>
  `run_inst_seq (mk_inst sm.cs_next_id MSTORE
     [Var p; Lit (n2w (LENGTH bs))] [] :: emitted_insts sh sb) u = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     pure_asm_rewrite_tac [APPEND] >>
     once_rewrite_tac [run_inst_seq_def] >>
     gvs[mk_inst_def, is_terminator_def] >>
     simp[run_inst_seq_def, is_terminator_def]) >>
  `lookup_var p u = SOME (n2w (w2n w))` by
    gvs[eval_operand_def, wordsTheory.n2w_w2n] >>
  `w2n w+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = u` mp_tac >>
  simp[Once venom_state_component_equality] >> strip_tac >> simp[]
QED

Theorem literal_immutable_frame[local]:
  immutable_frame_mods func cenv cx es s /\
  t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b len. FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
     FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  (!src tops id off tv v. cenv.ce_is_ctor /\
     ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) id = SOME (tv,v) ==>
     mem_bytes_at off (type_memory_size tv) t.vs_memory =
       mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
  immutable_frame_mods func cenv cx (es with gas_obs := [])
    (t with vs_inst_idx := i)
Proof
  rw[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def]
  >- (simp[loweringStateRelDefsTheory.immutables_rel_def] >>
      `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
         (t with vs_inst_idx := i)` suffices_by
        (simp[loweringStateRelDefsTheory.immutables_rel_def]) >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >> metis_tac[]) >>
  irule immutable_alloca_sep_frame >> qexistsl_tac [`s`,`es`] >> simp[] >>
  rpt gen_tac >> strip_tac >> disj1_tac >> qexists_tac `id` >>
  fs[local_region_def, local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

(* At zero the two ghost predicates agree on the facts required by the
   existing literal runner. Lift only its pointer check to the linked lo. *)
Theorem literal_inst_seq_linked[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  inst_seq_ptr D 0 ctx func PG G tn insts s G' tn' ==>
  inst_seq_ptr D lo ctx func PG G tn insts s G' tn'
Proof
  strip_tac >> irule inst_seq_ptr_zero_to_lo >>
  fs[ghost_inv_at_mods_def] >> qexists_tac `D` >> simp[]
QED

Theorem literal_linked_region_bytes[local]:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  dead_lo_ok_mods (H : (bool # bytes32 # type_value) list # num list) D lo cenv cx /\ lo <= b /\
  (!a len. a+len <= b \/ b+n <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  !src tops id off tv v. cenv.ce_is_ctor /\
     ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) id = SOME (tv,v) ==>
     mem_bytes_at off (type_memory_size tv) t.vs_memory =
       mem_bytes_at off (type_memory_size tv) s.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[FLOOKUP_EMPTY] >>
  drule_all immutable_region_value_layout_mods >> strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem literal_buffer_full_run_mods[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?u t b p sh G' tn'.
    buf.buf_operand = Var p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size (LENGTH bs)) /\
    lo <= b /\
    (!name a len. local_region cenv es.scopes u name a len ==>
       regions_disjoint b (32+32*word_size (LENGTH bs)) a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
    (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    FLOOKUP G' p = SOME (b,32+32*word_size (LENGTH bs)) /\
    lookup_var p t = SOME (n2w b) /\ op_taint tn' (Var p) = {} /\
    b+32+32*word_size (LENGTH bs) < dimword (:256) /\
    mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
       FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      stmt_state_rel H ctx func cenv cx es u
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) 0 d cenv cx es G tn s` by
      (rpt gen_tac >> strip_tac >> first_assum drule >> strip_tac >>
       simp[] >> drule literal_ghost_zero >> simp[]) >>
  drule_all (Q.INST [`lo` |-> `0`] (SPEC_ALL literal_bytelike_full_run)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all literal_bytelike_full_run_allocas_from >> strip_tac >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size (LENGTH bs))` by
    (qpat_assum `(t with <|vs_vars := _; vs_memory := _|>) = u`
       (mp_tac o Q.AP_TERM `\v. v.vs_allocas`) >> simp[]) >>
  `lo <= b` by (fs[allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`u`,`t`,`b`,`p`,`sh`,`G'`,`tn'`] >>
  asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (drule_then strip_assume_tac) >>
  drule_all literal_inst_seq_linked >> simp[]
QED

Theorem literal_memory_ptr_post[local]:
  evaluate_type (get_tenv cx) ann = SOME tv /\ b < dimword (:256) /\
  lookup_var p t = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,sz) /\ val_store_size tv v <= sz /\
  val_wf tv v /\ val_footprint tv v <= sz /\ val_in_memory tv v b t.vs_memory /\
  (!i. b <= i /\ i < b+sz ==> i NOTIN tn.t_mem) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz ==>
  ptr_mem_ok cx ann v (Var p) G tn (t with vs_inst_idx := j) /\
  ptr_buf_ok cenv e (Var p) G (t with vs_inst_idx := j)
Proof
  strip_tac >>
  fs[ptr_mem_ok_def, ptr_buf_ok_def, eval_operand_def, lookup_var_def, w2n_n2w] >>
  rpt strip_tac >> irule val_in_memory_footprint_agree >> simp[] >>
  qexists_tac `t.vs_memory` >> simp[] >>
  irule exprPtrCleanBufferPostTheory.clean_window_memory_agree >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  `i < b+sz` by decide_tac >> metis_tac[]
QED

(* A source-pure literal leaves the storage trace unchanged. On a bad
   input trace the zero-length focus suffices; otherwise use the run. *)
Theorem literal_pure_outcome_mods[local]:
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  ~s.vs_halted /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   ?t G' tn'. !H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
     Q H res (es with gas_obs := []) G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R
Proof
  strip_tac >> PURE_REWRITE_TAC[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (disj1_tac >> conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
      qexistsl_tac [`ARB`,`func`,`PG`,`G`,`tn`,`s`] >> simp[gas_origin_ptr_focus_nil]) >>
  first_x_assum (drule_then strip_assume_tac) >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`es`,`OK t`,`G'`,`tn'`] >> simp[gas_explicit_def]
QED

Theorem literal_vv_post_linked[local]:
  vv_post H ctx func cenv cx e es sa sb s es (Value v) (LocatedValue ann (base_ptr buf)) t /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) t ==>
  vv_post_mods H ctx func cenv cx e es sa sb s (es with gas_obs := [])
    (Value v) (LocatedValue ann (base_ptr buf)) t
Proof
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
     (irule storage_well_formed_on_backends >> simp[]) >>
  `locals_kept cenv es (es with gas_obs := []) s t <=> locals_kept cenv es es s t` by
    simp[locals_kept_def, popped_kept_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def, vv_post_mods_def, vv_holds_mods_def, vv_place_ptr_mods_def,
       base_ptr_def, vv_holds_def, vv_at_def, vv_own_def, read_result_def,
       return_def, stmt_state_rel_start_gas_obs] >> strip_tac >> simp[]
QED

(* The shared run endpoint supplies the memory virtual value. The plain
   value reads that same location without emitting a further instruction. *)
Theorem literal_buffer_endpoint_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  post_value_type cenv (Literal ann l) = ann /\ ~is_word_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ val_wf tv v /\
  val_footprint tv v <= 32+32*word_size (LENGTH bs) /\
  val_store_size tv v <= 32+32*word_size (LENGTH bs) /\
  type_memory_bytes cenv (lowered_value_type cenv (Literal ann l)) <=
    32+32*word_size (LENGTH bs) /\
  (!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv (Literal ann l)) = SOME rt ==>
     type_memory_size rt <= 32+32*word_size (LENGTH bs)) /\
  (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
     mem_bytes_at (a+32) (LENGTH bs) mem = bs ==> val_in_memory tv v a mem) /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?t G' tn'. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn') /\
    vv_post_mods H ctx func cenv cx (Literal ann l) es sa sb s (es with gas_obs := [])
      (Value v) (LocatedValue ann (base_ptr buf)) t /\
    vv_store_bound cx ann (lowered_value_type cenv (Literal ann l)) (es with gas_obs := [])
      (Value v) (LocatedValue ann (base_ptr buf)) t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G' tn' t /\
    ptr_val_ok cx ann v buf.buf_operand G' tn' t /\
    ptr_buf_ok cenv (Literal ann l) buf.buf_operand G' t /\
    ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s` by
    (rpt gen_tac >> strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all literal_buffer_full_run_mods >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
     inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (rpt gen_tac >> strip_tac >> rpt (first_x_assum (drule_then strip_assume_tac)) >> simp[]) >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
                 literal_bytelike_full_endpoint) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  gen_tac >> strip_tac >>
  rpt (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
         (drule_then strip_assume_tac)) >>
  suspend "post"
QED

Resume literal_buffer_endpoint_mods[post]:
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by metis_tac[] >>
  `!a len. a+len <= b \/ b+(32+32*word_size (LENGTH bs)) <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _`
       (qspecl_then [`a`,`len`] mp_tac) >>
     simp[]) >>
  `tn'.t_mem SUBSET tn.t_mem` by simp[DIFF_SUBSET] >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by simp[] >>
  `immutable_frame_mods func cenv cx (es with gas_obs := [])
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by suspend "immutable" >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G' tn'
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept_at lo cenv es sa G tn s G' tn'` by suspend "ghost" >>
  `ptr_val_ok cx ann v buf.buf_operand G' tn' (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ptr_buf_ok cenv (Literal ann l) buf.buf_operand G' (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    suspend "pointer" >>
  simp[allocas_below_fmp_def] >>
  conj_tac >- (drule_all literal_vv_post_linked >> simp[]) >>
  gvs[vv_store_bound_def, read_result_def, return_def]
QED

Resume literal_buffer_endpoint_mods[immutable]:
  drule_all literal_alloca_prefix >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by metis_tac[] >>
  irule literal_immutable_frame >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  fs[] >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  mp_tac (Q.INST [`D` |-> `DF H`, `n` |-> `32+32*word_size (LENGTH (bs:word8 list))`]
    literal_linked_region_bytes) >> simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC
QED

Resume literal_buffer_endpoint_mods[ghost]:
  drule literal_ghost_zero >> strip_tac >>
  drule_all literal_bytelike_full_static_frame >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
     lookup_var x t = lookup_var x u /\ FLOOKUP G' x = FLOOKUP G x /\
     FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x` by metis_tac[] >>
  mp_tac (Q.INST [`lo` |-> `0`, `D` |-> `DF H`]
    (INST_TYPE [alpha |-> ``:256``] literal_bytelike_full_ghost_post)) >>
  (impl_tac >- (fs[allocas_from_def] >> conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  reverse conj_tac >- (fs[ghost_kept_at_def] >> metis_tac[]) >>
  irule literal_ghost_linked >> fs[allocas_from_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`] >> simp[DIFF_SUBSET] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

Resume literal_buffer_endpoint_mods[pointer]:
  `b < dimword (:256)` by decide_tac >>
  `val_in_memory tv v b t.vs_memory` by metis_tac[] >>
  `!i. b <= i /\ i < b+(32+32*word_size (LENGTH bs)) ==> i NOTIN tn'.t_mem` by
    (simp[] >> decide_tac) >>
  drule_all literal_memory_ptr_post >>
  disch_then (qspec_then `LENGTH sb.cs_current_insts` strip_assume_tac) >>
  fs[ptr_val_ok_def, ptr_buf_ok_def, eval_operand_def, lookup_var_def]
QED

Finalise literal_buffer_endpoint_mods[local]

Theorem literal_value_post_mods[local]:
  vv_post_mods H ctx func cenv cx e es sa sb s ee (Value v)
    (LocatedValue ann (base_ptr buf)) t /\ ~is_word_type ann ==>
  expr_post_mods H ctx func cenv cx e es sa sb s ee v buf.buf_operand t
Proof
  simp[vv_post_mods_def, expr_post_mods_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, base_ptr_def] >> strip_tac >> simp[] >>
  `vv_post H ctx func cenv cx e es sa sb s ee (Value v)
     (LocatedValue ann (base_ptr buf)) t` by (simp[vv_post_def, base_ptr_def] >> first_assum ACCEPT_TAC) >>
  drule expr_post_of_vv_post_memory >> simp[base_ptr_def]
QED

Theorem literal_buffer_value_vv_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  ~is_word_type ann /\ is_bytestring_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ val_wf tv v /\
  val_footprint tv v <= 32+32*word_size (LENGTH bs) /\
  val_store_size tv v <= 32+32*word_size (LENGTH bs) /\
  type_memory_bytes cenv (lowered_value_type cenv (Literal ann l)) <=
    32+32*word_size (LENGTH bs) /\
  (!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv (Literal ann l)) = SOME rt ==>
     type_memory_size rt <= 32+32*word_size (LENGTH bs)) /\
  (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
     mem_bytes_at (a+32) (LENGTH bs) mem = bs ==> val_in_memory tv v a mem) /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  (!sa. ?buf sb. compile_expr cenv ty (Literal ann l) sa =
       (LocatedValue ann (base_ptr buf),sb) /\
     compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb)) /\
  (!st. eval_expr cx (Literal ann l) st = (INL (Value v),st)) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Literal ann l) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Literal ann l) es
Proof
  strip_tac >> conj_tac >> rw[expr_sim_full_mods_def, expr_vv_sim_full_mods_def] >>
  qpat_x_assum `!sa. ?buf sb. compile_expr _ _ _ sa = _ /\ _`
    (qspec_then `sa` strip_assume_tac) >>
  `post_value_type cenv (Literal ann l) = ann` by simp[post_value_type_def, expr_type_def]
  >- suspend "value"
  >> suspend "vv"
QED

Resume literal_buffer_value_vv_mods[value]:
  `op = buf.buf_operand /\ sb = sb'` by
    (drule lower_value_nonword_memory >> simp[base_ptr_def]) >>
  gvs[] >> irule literal_pure_outcome_mods >> (conj_tac >- simp[]) >> qexists_tac `INL v` >>
  simp[bind_def, read_result_def, return_def] >> disch_tac >>
  suspend "value_endpoint"
QED

Resume literal_buffer_value_vv_mods[vv]:
  gvs[] >> irule literal_pure_outcome_mods >> (conj_tac >- simp[]) >> qexists_tac `INL (Value v)` >>
  simp[] >> disch_tac >> suspend "vv_endpoint"
QED

Resume literal_buffer_value_vv_mods[value_endpoint]:
  mp_tac (Q.INST [`s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`]
    literal_buffer_endpoint_mods) >>
  (impl_tac >- (simp[post_value_type_def, expr_type_def] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (gen_tac >> strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[])))) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[] >> conj_tac
  >- (drule literal_value_post_mods >> simp[]) >>
  fs[expr_store_bound_def, vv_store_bound_def, base_ptr_def,
     read_result_def, return_def, PULL_EXISTS]
QED

Resume literal_buffer_value_vv_mods[vv_endpoint]:
  mp_tac (Q.INST [`s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`]
    literal_buffer_endpoint_mods) >>
  (impl_tac >- (simp[post_value_type_def, expr_type_def] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (gen_tac >> strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[])))) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  fs[ptr_vv_ok_def, ptr_val_ok_def, contextTheory.vv_location_def, base_ptr_def,
     read_result_def, return_def, vv_operand_def]
QED

Finalise literal_buffer_value_vv_mods[local]

Theorem linked_nonword_literal_shape[local]:
  well_typed_expr env (Literal ann l) /\ ~is_word_type ann ==>
  (?bs n. (l = BytesL bs \/ l = HexBytesL bs) /\ ann = BaseT (BytesT (Dynamic n))) \/
  (?str n. l = StringL str /\ ann = BaseT (StringT n))
Proof
  strip_tac >> gvs[well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def, is_word_type_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[well_typed_literal_def, is_word_type_def, well_formed_type_def,
      vyperValueTheory.evaluate_type_def]
QED

Theorem alloc_literal_full_ok_mods:
  !mods exps cx ann l. ~is_word_type ann ==>
    body_expr_full_ok_mods mods exps cx (Literal ann l)
Proof
  simp[body_expr_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Literal ann l) /\ alloc_limits_expr cenv (Literal ann l)` by
    fs[expr_body_pre_mods_def] >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule_all linked_nonword_literal_shape >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`bs`,`n`] (CONJUNCTS_THEN2 assume_tac SUBST_ALL_TAC))
    strip_assume_tac)
  >- suspend "bytes"
  >> gvs[] >> suspend "string"
QED

Resume alloc_literal_full_ok_mods[bytes]:
  qpat_x_assum `l = BytesL bs \/ l = HexBytesL bs` STRIP_ASSUME_TAC >> (
    gvs[well_typed_expr_def, well_typed_literal_def,
        alloc_limits_expr_def, literal_alloc_ok_def, compatible_bound_def,
        well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
    irule literal_buffer_value_vv_mods >>
    simp[is_word_type_def, is_bytestring_type_def] >>
    (reverse conj_tac >- (qexistsl_tac [`env`,`exps`,`mods`] >> simp[])) >>
    qexistsl_tac [`bs`, `BaseTV (BytesT (Dynamic n))`, `BytesV bs`] >>
    simp[post_value_type_def, expr_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, val_wf_def, val_footprint_def,
         val_store_size_def, literal_bytes_buffer_size,
         lowered_value_type_def, type_memory_size_def, type_memory_bytes_def] >>
    rpt conj_tac
    >- (gen_tac >>
        simp[compile_expr_def, compile_literal_vv_def, expr_type_def, is_word_type_def,
             comp_bind_def, comp_return_def] >>
        Cases_on `compile_bytelike_literal bs (LENGTH bs) sa` >> simp[])
    >- simp[Once evaluate_def, return_def, evaluate_literal_def]
    >- (simp[val_in_memory_def] >> metis_tac[])
    >> gvs[vfmConstantsTheory.word_size_def] >> simp[wordsTheory.dimword_def] >>
    mp_tac (Q.SPEC `n` le_word_size_mul) >>
    mp_tac (Q.SPEC `LENGTH (bs:word8 list)` le_word_size_mul) >>
    simp[vfmConstantsTheory.word_size_def] >> decide_tac)
QED

Resume alloc_literal_full_ok_mods[string]:
  gvs[well_typed_expr_def, well_typed_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def, compatible_bound_def,
      well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  irule literal_buffer_value_vv_mods >>
  simp[is_word_type_def, is_bytestring_type_def] >>
  (reverse conj_tac >- (qexistsl_tac [`env`,`exps`,`mods`] >> simp[])) >>
  qexistsl_tac [`MAP (n2w o ORD) str`, `BaseTV (StringT n)`, `StringV str`] >>
  simp[post_value_type_def, expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, val_wf_def, val_footprint_def,
       val_store_size_def, literal_string_buffer_size, LET_THM,
       lowered_value_type_def, type_memory_size_def] >>
  rpt conj_tac
  >- (gen_tac >>
      simp[compile_expr_def, compile_literal_vv_def, expr_type_def, is_word_type_def,
           comp_bind_def, comp_return_def] >>
      Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) (LENGTH str) sa` >> simp[])
  >- simp[Once evaluate_def, return_def, evaluate_literal_def]
  >- (simp[val_in_memory_def] >> metis_tac[])
  >> gvs[vfmConstantsTheory.word_size_def] >> simp[wordsTheory.dimword_def] >>
  mp_tac (Q.SPEC `n` le_word_size_mul) >>
  mp_tac (Q.SPEC `LENGTH (str:string)` le_word_size_mul) >>
  simp[vfmConstantsTheory.word_size_def] >> decide_tac
QED

Finalise alloc_literal_full_ok_mods
