(* Head evaluation and zero-mark physical-layout store for tuple loops. *)
Theory exprSimAggregateBodyHead
Ancestors
  exprSimAggregateBodyCounted exprSimAggregateBodySource stmtSimAssignAttr
  exprSimAggregateChildren exprSimSource exprSimHyps exprSimHypsDefs
  exprSimAggregateSource exprLoweringProps loweringPosts compileEnv loweringStateRelDefs
  gasSummary gasSummaryCompose gasOutcome fragGasPath fragGasMode fragExec
  vyperInterpreter vyperState venomState emitHelper exprOperandVar freshWrites
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom
  exprBopSimProps exprSimProps tupleMemoryFrame valueEncodingProps
  exprSimAggregateLoops exprSimUnwrap exprSimUnwrapProps exprSimMemoryRead
  exprSimMemoryForce placeTypedCopyRecursivePath placeMemoryPrimitiveForward
  localMemoryStorePath vyperAST vyperTypeCallGraph aggregateStoreSizePath
Libs
  monadsyntax

Theorem aggregate_store_body_rebased_slice_fields[local]:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel H ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  expr_post H ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP q.vs_allocas aid = SOME a) /\
    (!a len. a + len <= w2n w \/ w2n w + type_memory_size tv <= a ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule compile_store_memory_post_type >>
  disch_then (qspecl_then [`ce`, `op`, `Var x`] assume_tac) >>
  gvs[] >>
  `lookup_var x s = SOME w` by metis_tac[expr_post_rebased_lookup] >>
  `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
  `stmt_state_rel H ctx func ce cx es' s /\
   FLOOKUP s.vs_allocas did = SOME (b,k)` by fs[expr_post_def] >>
  `!name a len. local_region ce es'.scopes s name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r name a len` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >> simp[] >>
        metis_tac[expr_post_rebased_lookup]) >>
     first_x_assum drule >> simp[arithmeticTheory.ADD_COMM]) >>
  Cases_on `post_value_type ce e = expr_type e \/
    tuple_memory_layout_eq (expr_type e) (post_value_type ce e)`
  >- suspend "same_layout" >>
  pop_assum (strip_assume_tac o SRULE [DE_MORGAN_THM]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    (qpat_x_assum `_ ==> acyclic_struct_metadata _` irule >>
     conj_tac
     >- (Cases_on `e` >>
         fs[post_value_type_def, expr_type_def] >>
         rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
         fs[post_value_type_def, expr_type_def] >>
         simp[Once int_calls_expr_def]) >>
     metis_tac[post_value_type_lowered]) >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (`expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
     drule_all post_value_type_widens >>
     fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size tv <= w2n sw)` by
    (`expr_val_at ce cx (post_value_type ce e)
       (sa with cs_next_var := sm.cs_next_var) su es' v op s` by
       fs[expr_post_def] >>
     irule aggregate_physical_source_slot_bounds >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `type_widens_to _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel H _ _ _ _ _ s`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (b,k)`)) >>
     simp[arithmeticTheory.ADD_COMM] >>
     first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])) >>
  `compile_store_memory_typed ce (Var x) (expr_type e) op
     (post_value_type ce e) su = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  drule aggregate_body_copy_metadata >> strip_tac >>
  drule compile_store_memory_typed_forward_run >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (expr_type e) = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)) >>
  disch_then (qspecl_then [`ctx`, `func`, `w`] mp_tac) >>
  (impl_tac
   >- (simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >>
       first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  drule aggregate_store_rebased_control_frame >>
  disch_then (qspecl_then [`t`, `type_memory_size tv`, `w2n w`] mp_tac) >>
  (impl_tac
   >- (gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
           typedMemoryCopyTheory.typed_copy_frame_def] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def,
      arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
    vs_current_bb := _; vs_inst_idx := _|> = s`
    (mp_tac o Q.AP_TERM `\z. (z.vs_allocas, z.vs_accounts, z.vs_transient,
                              z.vs_requests, z.vs_call_ctx)`) >> simp[] >>
  strip_tac >> simp[] >> rpt conj_tac >>
  first_assum (MATCH_ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED

Resume aggregate_store_body_rebased_slice_fields[same_layout]:
  (* Equal types, or tuples with equal member layouts: both store by a
     same-type bulk copy. *)
  `compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
   expr_val_rel cx (expr_type e) v op s` by
    (qpat_x_assum `post_value_type ce e = expr_type e \/ _` strip_assume_tac
     >- gvs[expr_post_def] >>
     conj_tac
     >- (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
         simp[contextTheory.compile_store_memory_def]) >>
     drule_all aggregate_child_tuple_layout_val_rel >> simp[]) >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (Cases_on `is_word_type (expr_type e)`
     >- (drule_all word_tv_memory_size >> simp[wordsTheory.dimword_def]) >>
     drule_all expr_body_pre_copy_ok >> simp[wordsTheory.dimword_def]) >>
  `?sw. eval_operand op s = SOME sw /\
    (if is_word_type (expr_type e) then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  drule compile_store_memory_same_type_size_forward >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME tv`)) >>
  disch_then (drule_at (Pat `eval_operand op s = SOME sw`)) >>
  disch_then (qspecl_then [`v`, `func`, `w`, `ctx`] mp_tac) >>
  (impl_tac >- simp[venomStateTheory.eval_operand_def]) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
       (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  drule aggregate_store_rebased_control_frame >>
  disch_then (qspecl_then [`t`, `type_memory_size tv`, `w2n w`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
          (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := s.vs_prev_bb;
            vs_current_bb := s.vs_current_bb|>`) >> simp[]) >>
    rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM]))) >>
  strip_tac >> gvs[] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def,
      arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >>
  first_assum (MATCH_ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED

Finalise aggregate_store_body_rebased_slice_fields

(* stmt_state_rel_fields_transport at 256-bit horizons, with an explicit
   binder order for irule. *)
Theorem stmt_state_rel_fields_transport_256[local]:
  !(H0:(bool # bytes32 # type_value) list # num list)
   (H:(bool # bytes32 # type_value) list # num list)
   ctx func cenv cx es u s.
  stmt_state_rel H0 ctx func cenv cx es u /\
  stmt_state_rel H ctx func cenv cx es s /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx ==>
  stmt_state_rel H ctx func cenv cx es u
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    exprLoweringPropsTheory.stmt_state_rel_fields_transport) >>
  metis_tac[]
QED


Theorem aggregate_body_tuple_head_path:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e)
    su = ((),st) /\
  expr_body_pre ce cx env e es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) mid (OK r) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     vv_post H ctx func ce cx e es sa sm s0 (mid with gas_obs := []) tvv vv r) /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  fn_has_code sa st func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  inst.inst_id < sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  off + type_memory_size tv <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0) /\
  (?H. valid_horizon cx st0 H mid.storage_trace) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v q.
    read_result cx tvv (mid with gas_obs := []) =
      (INL v,mid with gas_obs := []) /\
    expr_sim_inv ce cx env (mid with gas_obs := []) /\
    gas_marked_path F ctx func r 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = st.cs_current_bb /\
    q.vs_inst_idx = LENGTH st.cs_current_insts /\
    val_in_memory tv v (b+off) q.vs_memory /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func ce cx (mid with gas_obs := []) q) /\
    (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
      aid < sa.cs_next_id /\
      (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
        p+n <= lo \/ lo+sz <= p) /\
      (p+n <= b+off \/ b+off+type_memory_size tv <= p) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    (!p n. b <= p /\ p+n <= b+asz /\
      (p+n <= b+off \/ b+off+type_memory_size tv <= p) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    locals_kept ce es (mid with gas_obs := []) s0 q /\
    (~expr_has_effect e ==>
      (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
        mem_bytes_at lo sz q.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
      (!p n. (p+n <= b \/ b+asz <= p) /\
        (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
          sa.cs_next_id <= i.inst_id /\
          FLOOKUP q.vs_allocas i.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
        mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory))
Proof
  strip_tac >>
  `vv_post H ctx func ce cx e es sa sm s0 (mid with gas_obs := []) tvv vv r /\
   stmt_state_rel H ctx func ce cx es s0` by metis_tac[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ es s0` kall_tac >>
  `?v. read_result cx tvv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := [])` by metis_tac[vv_post_materialises] >>
  `expr_body_pre ce cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
   (do res <- eval_expr cx e; read_result cx res od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v,mid with gas_obs := [])` by
    metis_tac[aggregate_body_marked_read_replay] >>
  `expr_sim_inv ce cx env (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_eval] >>
  `value_has_type tv v /\ val_wf tv v` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     metis_tac[aggregate_materialised_child_typed, aggregate_materialised_child_wf,
               expr_body_pre_gas_obs]) >>
  suspend "store"
QED
Resume aggregate_body_tuple_head_path[store]:
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su st` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn st func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `lookup_var x r = SOME (n2w b)` by fs[vv_post_def] >>
  `eval_operand (Var x) r = SOME (n2w b)` by simp[eval_operand_def] >>
  qspec_then `\H. valid_horizon cx st0 H mid.storage_trace`
    (drule_all o SRULE [])
    (Q.GEN `P` (SPEC_ALL buffer_emit_add_vv_marked_path_horizons)) >>
  strip_tac >>
  `?y. dst = Var y /\ not_fresh_at sn y` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_inst_def, emit_def, comp_return_def,
          not_fresh_at_def] >> strip_tac >>
     gvs[ASCIInumbersTheory.toString_11]) >>
  gvs[] >>
  `local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved, ci_mono_def, arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    metis_tac[cj 1 compiler_compile_var, not_fresh_at_mono, ci_mono_def] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    (drule_at (Pos hd) compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def] >> metis_tac[]) >>
  `sa.cs_next_id <= sn.cs_next_id /\ sn.cs_next_var <= su.cs_next_var /\
    cs_extends sn su /\ cs_extends su st` by
    fs[ci_mono_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `stmt_state_rel H ctx func ce cx (mid with gas_obs := []) q /\
   FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz)` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ sn _ _ _ _ q`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac std_ss [vv_post_def] >> strip_tac >> fs[]) >>
  `lookup_var y q = SOME (n2w (b+off))` by
    fs[eval_operand_def, wordsTheory.word_add_n2w] >>
  `stmt_state_rel H ctx func ce cx mid q /\ not_local_ptr ce mid.scopes x` by
    (conj_tac
     >- (fs[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >>
         metis_tac[]) >>
     metis_tac[]) >>
  `!name lo sz. local_region ce mid.scopes q name lo sz ==>
    lo+sz <= b+off \/ b+off+type_memory_size tv <= lo` by
    (rpt strip_tac >> irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
       exprSimAggregateLoopsTheory.aggregate_alloca_slice_excludes_local) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `immutable_metadata_frame es mid` by
    (drule_all aggregate_body_marked_replay >> strip_tac >>
     drule eval_expr_immutable_metadata_frame >>
     simp[immutable_metadata_frame_def] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)` by
    (rpt strip_tac >>
     fs[immutable_metadata_frame_def] >>
     qpat_x_assum `!addr. IS_SOME _ <=> IS_SOME _`
       (qspec_then `cx.txn.target` mp_tac) >>
     Cases_on `ALOOKUP es.immutables cx.txn.target` >>
     Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[] >>
     rename1 `ALOOKUP es.immutables cx.txn.target = SOME oldimms` >>
     qpat_x_assum `!addr imms imms' src id. _`
       (drule_all_then (qspecl_then [`ce.ce_module`, `name`] mp_tac)) >>
     Cases_on `FLOOKUP (get_source_immutables ce.ce_module oldimms) name` >>
     simp[] >> rename1 `SOME pair` >> Cases_on `pair` >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `w2n (n2w (b+off):256 word) = b+off` by
    (simp[wordsTheory.w2n_n2w] >>
     `b+off < dimword (:256)` by decide_tac >> simp[]) >>
  `fn_has_code sn su func /\ fn_has_code su st func` by
    metis_tac[fn_has_code_split] >>
  drule_all unwrap_value_body_rebased_path_horizons >> strip_tac >>
  `expr_post H ctx func ce cx e (mid with gas_obs := [])
     (sa with cs_next_var := sn.cs_next_var) su q (mid with gas_obs := [])
     v op u` by metis_tac[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ sn _ _ _ _ q`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_at (Pat `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (Q.INST [`sa` |-> `sa`, `sm` |-> `sn`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] aggregate_store_body_rebased_slice_fields))) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`tv`, `asz`,
    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
    `env`, `inst.inst_id`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[arithmeticTheory.ADD_ASSOC])) >>
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule_all aggregate_body_marked_replay >>
     disch_then assume_tac >> drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!name lo sz. local_region ce mid.scopes q name lo sz ==>
      local_region ce es.scopes s0 name lo sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `mid.scopes`, `q`] >> simp[] >>
     fs[vv_post_def]) >>
  qexists_tac `q'` >> simp[] >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_marked_path_then))) >>
      qexists_tac `q` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_marked_path_then))) >>
      qexists_tac `u` >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (`stmt_state_rel H ctx func ce cx (mid with gas_obs := []) q'` by
        (fs[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >>
         metis_tac[]) >>
      qx_gen_tac `H2` >> strip_tac >>
      `stmt_state_rel H2 ctx func ce cx (mid with gas_obs := []) u` by
        (qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
           (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_def]))) >>
      `stmt_state_rel H2 ctx func ce cx (mid with gas_obs := []) q'`
        suffices_by simp[] >>
      match_mp_tac (Q.SPECL [`H`, `H2`, `ctx`, `func`, `ce`, `cx`,
        `mid with gas_obs := []`, `q'`, `u`] stmt_state_rel_fields_transport_256) >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >>
         fs[ci_mono_def] >> decide_tac) >>
      metis_tac[vv_post_def]) >>
  conj_tac >- metis_tac[vv_post_def] >>
  conj_tac
  >- (rpt strip_tac >> (
      `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (qpat_x_assum `vv_post H _ _ _ _ _ _ _ sn _ _ _ _ q`
           (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
         qpat_x_assum `!aid off sz. _` irule >>
         conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
         qexists_tac `aid` >> simp[]) >>
      `mem_bytes_at p n q'.vs_memory = mem_bytes_at p n q.vs_memory` suffices_by simp[] >>
      qpat_x_assum `!aid off' sz a len. _` irule >>
      conj_tac
      >- (qexistsl_tac [`aid`, `p`, `n`] >> simp[] >>
          conj_tac
          >- (rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
          metis_tac[vv_post_def])
      >- (pure_asm_rewrite_tac[] >> decide_tac))) >>
  conj_tac
  >- (`!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          lo+sz <= b \/ b+asz <= lo` by
        (rpt strip_tac >>
         drule_at (Pat `local_region _ _ _ _ _ _`)
           (Q.INST [`off` |-> `0`, `n` |-> `asz`]
             (SPEC_ALL (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] exprSimAggregateLoopsTheory.aggregate_alloca_slice_excludes_local))) >>
         simp[] >> disch_then irule >> simp[] >>
         metis_tac[expr_body_pre_def]) >>
      `mem_bytes_at b asz q.vs_memory = mem_bytes_at b asz s0.vs_memory` by
        (qpat_x_assum `vv_post H _ _ _ _ _ _ _ sn _ _ _ _ q`
           (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
         qpat_x_assum `!aid off sz. _` irule >>
         conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
         qexists_tac `inst.inst_id` >> simp[]) >>
      rpt strip_tac >> (
      `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (drule mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`p-b`, `n`] mp_tac) >>
         `b+(p-b) = p /\ p-b+n <= asz` by decide_tac >> simp[]) >>
      `mem_bytes_at p n q'.vs_memory = mem_bytes_at p n q.vs_memory` suffices_by simp[] >>
      qpat_x_assum `!aid off' sz a len. _` irule >>
      conj_tac
      >- (qexistsl_tac [`inst.inst_id`, `b`, `asz`] >> simp[] >>
          rpt strip_tac >>
          metis_tac[arithmeticTheory.ADD_COMM]) 
      >- (pure_asm_rewrite_tac[] >> decide_tac))) >>
  conj_tac
  >- (irule locals_kept_trans >>
      qexistsl_tac [`mid with gas_obs := []`, `sa`, `q`] >>
      simp[] >> metis_tac[vv_post_def]) >>
  suspend "pure_frame"
QED
Resume aggregate_body_tuple_head_path[pure_frame]:
  strip_tac >>
  rpt (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac) >>
  `pure_frame ce func es sa s0 q` by fs[vv_post_def] >>
  `pure_frame ce func (mid with gas_obs := [])
     (sa with cs_next_var := sn.cs_next_var) q u` by
    (drule exprSimWordArgsTheory.expr_post_pure_frame >> simp[]) >>
  `!aid a. FLOOKUP q.vs_allocas aid = SOME a ==>
      FLOOKUP u.vs_allocas aid = SOME a` by fs[expr_post_def] >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
      lookup_var z q = SOME w` by fs[vv_post_def] >>
  `pure_frame ce func es sa s0 u` by
    (match_mp_tac pure_frame_trans >>
     qexistsl_tac [`mid with gas_obs := []`,
       `sa with cs_next_var := sn.cs_next_var`, `q`] >>
     simp[]) >>
  match_mp_tac (SRULE [arithmeticTheory.ADD_COMM] aggregate_pure_frame_store) >>
  qexistsl_tac [`u`, `b+off`, `type_memory_size tv`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_local_ptr ce es.scopes x` by fs[expr_body_pre_def] >>
      fs[stmt_state_rel_def, state_rel_def] >>
      drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
      simp[regions_disjoint_def]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Finalise aggregate_body_tuple_head_path
