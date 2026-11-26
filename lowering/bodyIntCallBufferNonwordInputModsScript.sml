(* The allocated formal buffer and the unwrapped source are distinct cuts. *)
Theory bodyIntCallBufferNonwordInputMods
Ancestors
  bodyIfExpArmUnwrapMods bodyAnnNonwordReadTypesMods bodyAssignNameLinkedSetup
  bodySimStmtFacts vyperInterpreter vyperState vyperTypeExprSoundness
  bodyWriteSubscriptSourceMods
  bodyStructFieldCutsMods abiEncodeValuesPhases gasOriginPtrLabels
  reasonEndpointResourcesPtr reasonCopySourcePtr exprReasonOperand
  exprSimIfExpCompat typedMemoryCopy wordArgsPtr stateRelProj
  valueCopyBytes exprSimHypsDefs exprBodyPreProps exprBodyPreTypingProps
  vyperTypeArgFits vyperTypeEvalCaseProofs vyperTypeSystem vfmConstants
  context exprSimSource exprSimSend vyperTyping exprSimProps venomMemDefs arithmetic
  valueEncoding valueTypingMemoryProps loweringPosts bodyFullPostsMods bodyFullShadowBodyInv
  exprLoweringProps freshWrites bodyPtrDefs fragGasOriginPtr vyperStorageFootprint
  words venomState finite_map vyperContext vyperAST compileEnv annassignRelayoutSource
Libs monadsyntax

val _ = Parse.hide "base";

Theorem intcall_nonword_tag_options[local]:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce ty e si = (vv,ci) ==>
  vv_type vv = expr_type e \/ vv_type vv = lowered_value_type ce e
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  qhdtm_x_assum `expr_sim_inv_mods`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
  drule_all compile_expr_reason_uniform >>
  simp[reason_uniform_shape_def] >>
  disch_then (qspec_then `ty` (qx_choosel_then [`loc`,`tag`]
    (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac
       (drule_then assume_tac))))) >>
  qpat_assum `reason_result_shape _ _ vv` mp_tac >>
  qpat_assum `tag = expr_type e \/ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `vv` >> simp[reason_result_shape_def,vv_type_def] >> metis_tac[]
QED

Theorem intcall_nonword_aggregate_tag[local]:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce ty e si = (vv,ci) /\
  ~is_bytestring_type (expr_type e) ==>
  vv_type vv = lowered_value_type ce e
Proof
  strip_tac >> drule_all_then assume_tac intcall_nonword_tag_options >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (qhdtm_assum `expr_sim_inv_mods`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
     ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all ifexp_lowered_type_classify >>
  disch_then strip_assume_tac >>
  TRY (qpat_assum `is_bytestring_type (expr_type e)` (fn th =>
         qpat_assum `~is_bytestring_type (expr_type e)` (fn neg =>
           CONTR_TAC (MP neg th))) >> NO_TAC) >>
  TRY (qpat_assum `lowered_value_type ce e = expr_type e` (fn th =>
         qpat_assum `vv_type vv = _ \/ _` mp_tac >> simp[NoAsms,th]) >> NO_TAC) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_call] >> strip_tac >> drule reason_compile_call >>
  Cases_on `vv` >> simp[reason_result_shape_def,vv_type_def]
QED

Theorem intcall_annotation_value[local]:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL v,mid) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)` by
    simp[bind_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  fs[value_runtime_typed_def]
QED

Theorem intcall_bytes_length[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME rt /\ value_has_type rt v ==>
  ?len. (?bs. v = BytesV bs /\ len = LENGTH bs) \/
        (?str. v = StringV str /\ len = LENGTH str)
Proof
  strip_tac >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem intcall_bytes_rounded[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME rt /\ value_has_type rt v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) ==>
  32 * word_size len + 32 <= type_memory_size rt
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def,type_memory_size_def] >>
  irule word_size_monotone >> simp[]
QED

Theorem intcall_aggregate_disjoint[local]:
  alloca_inv a /\ FLOOKUP a.vs_allocas did = SOME (base,cap) /\
  dn <= cap /\
  ((?aid b n. FLOOKUP a.vs_allocas aid = SOME (b,n) /\ aid <> did /\
      b <= src /\ src + sn <= b + n) \/
   (?nm b n. local_region ce ee.scopes a nm b n /\
      b <= src /\ src + sn <= b + n)) /\
  (!nm b n. local_region ce ee.scopes a nm b n ==> base+cap <= b \/ b+n <= base) ==>
  src + sn <= base \/ base + dn <= src
Proof
  strip_tac
  >- (`b + n <= base \/ base + cap <= b` by
        (fs[alloca_inv_def,allocas_non_overlapping_def] >>
         first_x_assum (qspecl_then [`aid`,`did`,`b`,`n`,`base`,`cap`] mp_tac) >> simp[]) >>
      decide_tac) >>
  qpat_assum `!nm b n. local_region _ _ _ nm b n ==> _`
    (drule_then strip_assume_tac) >> decide_tac
QED

(* The live source was in an older registered allocation or a local before
   the destination ALLOCA; neither can be the new row. *)
Theorem intcall_retained_source_apart[local]:
  vv_at ce cx sty si ci ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  0 < val_footprint stv v /\
  ((?tag. vv = StackValue tag (vv_operand vv)) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)) /\
  eval_operand (vv_operand vv) s = SOME w /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP a.vs_allocas aid = SOME row) /\
  (!nm b n. local_region ce ee.scopes s nm b n ==> local_region ce ee.scopes a nm b n) /\
  alloca_inv a /\ FLOOKUP a.vs_allocas ci.cs_next_id = SOME (base,cap) /\ dn <= cap /\
  (!nm b n. local_region ce ee.scopes a nm b n ==> base+cap <= b \/ b+n <= base) ==>
  w2n w + val_footprint stv v <= base \/ base + dn <= w2n w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(?aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < ci.cs_next_id /\
      b <= w2n w /\ w2n w + val_footprint stv v <= b+n) \/
   (?nm b n. local_region ce ee.scopes s nm b n /\
      b <= w2n w /\ w2n w + val_footprint stv v <= b+n)` by
    (irule vv_at_memory_region_prefix >>
     qpat_assum `vv_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     asm_rewrite_tac[LESS_EQ_REFL] >>
     Cases_on `vv` >> gvs[vv_operand_def] >> metis_tac[]) >>
  irule intcall_aggregate_disjoint >>
  qpat_assum `FLOOKUP a.vs_allocas _ = _` (irule_at Any) >>
  qexistsl [`ee`,`ce`] >> asm_rewrite_tac[]
  >- (disj1_tac >> qexistsl [`aid`,`b`,`n`] >> simp[] >> decide_tac) >>
  disj2_tac >> qexistsl [`nm`,`b`,`n`] >> simp[]
QED

val unwrap_entry = ``
  compile_expr ce ty e si = (vv,ci) /\
  unwrap_value ce vv ca = (op,cu) /\
  ci.cs_next_var <= ca.cs_next_var /\ ci.cs_next_id <= ca.cs_next_id /\
  fn_has_code ca cu func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce si /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si ca s0 mid raw vv a /\
    ghost_inv_at_mods (DF H) lo d ce cx mid Ga ta a) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) mid raw vv a /\
  ptr_vv_ok cx (post_value_type ce e) raw vv mid Ga ta a /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x Ga a) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga a) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) a = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es si G0 t0 s0 Ga ta /\
  ~a.vs_halted /\ a.vs_current_bb = ca.cs_current_bb /\
  a.vs_inst_idx = LENGTH ca.cs_current_insts /\ alloca_history func a``;

val allocated_dst = ``
  ci.cs_next_id < ca.cs_next_id /\
  not_fresh_at ca dst /\ lookup_var dst a = SOME (n2w base) /\
  ptr_covers Ga ta dst a (MAX 32 (type_memory_bytes ce dty)) /\
  FLOOKUP a.vs_allocas ci.cs_next_id = SOME (base,MAX 32 (type_memory_bytes ce dty)) /\
  base + MAX 32 (type_memory_bytes ce dty) < dimword (:256) /\
  base + MAX 32 (type_memory_bytes ce dty) <= a.vs_alloca_next /\
  (!nm b n. local_region ce mid.scopes a nm b n ==>
    base + MAX 32 (type_memory_bytes ce dty) <= b \/ b+n <= base)``;

val retained_source = ``
  vv_at ce cx (post_value_type ce e) si ci mid raw vv s /\
  (!w. eval_operand (vv_operand vv) a = SOME w ==> eval_operand (vv_operand vv) s = SOME w) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP a.vs_allocas aid = SOME row) /\
  (!nm b n. local_region ce mid.scopes s nm b n ==> local_region ce mid.scopes a nm b n)``;

val bytes_input = ``
  ?src len n stv.
    op = Var src /\ is_bytestring_type (vv_type vv) /\
    evaluate_type (get_tenv cx) (vv_type vv) = SOME stv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory stv v (w2n w) m) /\
    n = 32 + 32 * word_size len /\ n < dimword (:256) /\
    n <= type_memory_size stv /\ n <= type_memory_size dtv /\
    not_fresh_at cu src /\ lookup_var src z = SOME w /\
    ptr_covers Gf tf src z n /\ ptr_covers Gf tf dst z n /\
    w2n w + n <= z.vs_alloca_next /\ base + n <= z.vs_alloca_next``;

Theorem intcall_buffer_nonword_input_mods:
  ^unwrap_entry /\ ^allocated_dst /\ ^retained_source /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\
  ~is_word_type dty /\ evaluate_type (get_tenv cx) dty = SOME dtv ==>
  ?v z Gf tf w.
    read_result cx raw mid = (INL v,mid) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post_mods H ctx func ce cx e es si cu s0 mid v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx mid Gf tf z) /\
    ghost_kept_at lo ce es si G0 t0 s0 Gf tf /\
    wb_frame ce mid mid ca a z /\ ghost_kept_at lo ce mid ca Ga ta a Gf tf /\
    ~z.vs_halted /\ z.vs_current_bb = cu.cs_current_bb /\
    z.vs_inst_idx = LENGTH cu.cs_current_insts /\ alloca_history func z /\
    alloca_inv z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    a.vs_alloca_next <= z.vs_alloca_next /\
    ca.cs_next_id <= cu.cs_next_id /\ ca.cs_next_var <= cu.cs_next_var /\
    z.vs_labels = a.vs_labels /\
    (!nm b n. local_region ce mid.scopes a nm b n <=> local_region ce mid.scopes z nm b n) /\
    (!x. not_fresh_at ca x ==> lookup_var x z = lookup_var x a /\
      FLOOKUP Gf x = FLOOKUP Ga x /\ op_taint tf (Var x) = op_taint ta (Var x)) /\
    (!aid row. FLOOKUP a.vs_allocas aid = SOME row ==> FLOOKUP z.vs_allocas aid = SOME row) /\
    (!aid b n. aid < ca.cs_next_id /\ FLOOKUP a.vs_allocas aid = SOME (b,n) /\
      (!nm p k. local_region ce mid.scopes a nm p k ==> b+n <= p \/ p+k <= b) ==>
      mem_bytes_at b n z.vs_memory = mem_bytes_at b n a.vs_memory /\
      (!i. b <= i /\ i < b+n /\ i IN tf.t_mem ==> i IN ta.t_mem)) /\
    not_fresh_at cu dst /\ lookup_var dst z = SOME (n2w base) /\
    ptr_covers Gf tf dst z (MAX 32 (type_memory_bytes ce dty)) /\
    FLOOKUP z.vs_allocas ci.cs_next_id = SOME (base,MAX 32 (type_memory_bytes ce dty)) /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    eval_operand op z = SOME w /\
    (if is_bytestring_type dty then ^bytes_input
     else ?stv. struct_operand_mods (ce,get_tenv cx,vv_type vv,dty,stv,dtv)
                 (op,v) (dst,base) (cu,Gf,tf,z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  drule_all ifexp_arm_nonword_unwrap_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`v`,`z`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "finish"
QED

Resume intcall_buffer_nonword_input_mods[finish]:
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H ctx func ce cx e es si ca s0 mid raw vv a /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H ctx func ce cx e es si cu s0 mid v op z /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid a` by
    fs[vv_post_mods_def] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid z` by
    fs[expr_post_mods_def,expr_post_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `ca.cs_next_id <= cu.cs_next_id /\ ca.cs_next_var <= cu.cs_next_var` by
    (qpat_assum `unwrap_value ce vv ca = _` mp_tac >>
     qsuff_tac `ci_mono ca (SND (unwrap_value ce vv ca))` >- simp[ci_mono_def] >>
     simp[ci_mono_unwrap_value]) >>
  `z.vs_labels = a.vs_labels` by
    (irule gas_origin_ptr_path_preserves_labels >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] _`
       (qspec_then `DF (storage_trace_horizon mid.storage_trace)` (irule_at Any))) >>
  `local_ptrs_reserved ce ca` by
    (drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
     irule local_ptrs_reserved_next_var >> qexists `si` >> simp[] >> decide_tac) >>
  `!nm b n. local_region ce mid.scopes a nm b n <=> local_region ce mid.scopes z nm b n` by
    (drule_all (SIMP_RULE bool_ss [REFL_CLAUSE]
        (Q.INST [`es1` |-> `es`] wb_frame_local_regions)) >> simp[]) >>
  `not_fresh_at cu dst /\ lookup_var dst z = SOME (n2w base) /\
   ptr_covers Gf tf dst z (MAX 32 (type_memory_bytes ce dty)) /\
   FLOOKUP z.vs_allocas ci.cs_next_id = SOME (base,MAX 32 (type_memory_bytes ce dty))` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists `ca` >> simp[]) >>
     qpat_assum `!x. not_fresh_at ca x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x cap. not_fresh_at ca x /\ ptr_covers Ga ta x a cap ==> _`
       (drule_all_then assume_tac) >>
     qpat_assum `!aid row. FLOOKUP a.vs_allocas aid = SOME row ==> _`
       (drule_then assume_tac) >> simp[]) >>
  `type_memory_bytes ce dty = type_memory_size dtv` by
    (irule assign_name_memory_bytes_mods >>
     qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv` (irule_at Any) >>
     drule_then assume_tac expr_body_pre_mods_inv >> qexistsl [`mods`,`es`,`env`] >> simp[]) >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`w`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "protected" >>
  Cases_on `is_bytestring_type dty` >> simp[]
  >- suspend "bytes" >>
  suspend "aggregate"
QED

Resume intcall_buffer_nonword_input_mods[protected]:
  map_every qx_gen_tac [`aid`,`b`,`n`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!nm p k. local_region ce mid.scopes a nm p k ==> b+n <= p \/ p+k <= b` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!nm p k. local_region ce mid.scopes a nm p k <=> _`
       (qspecl_then [`nm`,`p`,`k`] mp_tac) >>
     qpat_assum `!nm p k. local_region ce mid.scopes z nm p k ==> _`
       (qspecl_then [`nm`,`p`,`k`] mp_tac) >> simp[]) >>
  `b <= b /\ b+n <= b+n` by simp[] >>
  drule_all (Q.INST [`q` |-> `b`,`len` |-> `n`]
    abi_encode_values_unwrap_window) >> simp[]
QED

Resume intcall_buffer_nonword_input_mods[bytes]:
  `is_bytestring_type (lowered_value_type ce e)` by
    (irule typed_copy_bytestring_source >> qexistsl [`dty`,`get_tenv cx`] >> simp[]) >>
  `is_bytestring_type (expr_type e)` by
    (irule typed_copy_bytestring_source >> qexistsl [`dty`,`get_tenv cx`] >> simp[]) >>
  `value_has_type dtv v` by
    (qpat_assum `type_widens_to _ (lowered_value_type ce e) dty`
       (mp_then Any mp_tac type_widens_to_value_has_type) >> simp[]) >>
  drule_all_then assume_tac intcall_nonword_tag_options >>
  `?stv. is_bytestring_type (vv_type vv) /\
         evaluate_type (get_tenv cx) (vv_type vv) = SOME stv /\ value_has_type stv v` by
    (qpat_assum `vv_type vv = _ \/ _` strip_assume_tac
     >- (drule_all intcall_annotation_value >> simp[]) >> metis_tac[]) >>
  `?len. (?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)` by
    (irule intcall_bytes_length >> qexistsl [`rt`,`get_tenv cx`,`lowered_value_type ce e`] >> simp[]) >>
  `32 * word_size len + 32 <= type_memory_size rt` by
    (irule intcall_bytes_rounded >> conj_tac
     >- (qexistsl [`get_tenv cx`,`lowered_value_type ce e`] >> simp[]) >> qexists `v` >> simp[]) >>
  `32 * word_size len + 32 <= type_memory_size stv` by
    (irule intcall_bytes_rounded >> conj_tac
     >- (qexistsl [`get_tenv cx`,`vv_type vv`] >> simp[]) >> qexists `v` >> simp[]) >>
  `32 * word_size len + 32 <= type_memory_size dtv` by
    (irule intcall_bytes_rounded >> conj_tac
     >- (qexistsl [`get_tenv cx`,`dty`] >> simp[]) >> qexists `v` >> simp[]) >>
  qabbrev_tac `n = 32 * word_size len + 32` >>
  `0 < n` by simp[Abbr `n`] >>
  `0 < type_memory_size rt` by decide_tac >>
  qpat_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
  `!m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory stv v (w2n w) m` by
    (rpt strip_tac >>
     `val_in_memory rt v (w2n w) m` by simp[] >>
     drule_all (Q.SPECL [`get_tenv cx`,`lowered_value_type ce e`,`vv_type vv`]
       bytestring_val_in_memory_transfer) >> simp[]) >>
  `n <= MAX 32 (type_memory_bytes ce dty)` by
    (simp[MAX_DEF] >> decide_tac) >>
  `n < dimword (:256) /\ w2n w + n <= z.vs_alloca_next /\
    base + n <= z.vs_alloca_next` by decide_tac >>
  `ptr_covers Gf tf r z n` by
    (irule ptr_covers_mono >> qexists `type_memory_size rt` >> simp[]) >>
  `ptr_covers Gf tf dst z n` by
    (irule ptr_covers_mono >> qexists `MAX 32 (type_memory_bytes ce dty)` >> simp[]) >>
  `lookup_var r z = SOME w` by
    (qpat_x_assum `eval_operand op z = SOME w` mp_tac >> asm_rewrite_tac[eval_operand_def]) >>
  unabbrev_all_tac >>
  qexistsl [`r`,`len`,`stv`] >> asm_rewrite_tac[] >> simp[NoAsms]
QED

Resume intcall_buffer_nonword_input_mods[aggregate]:
  `~is_bytestring_type (expr_type e)` by
    (strip_tac >> drule_all type_widens_from_bytestring >> simp[]) >>
  `~is_bytestring_type (lowered_value_type ce e)` by
    (strip_tac >> drule_all type_widens_from_bytestring >> simp[]) >>
  drule_all_then assume_tac intcall_nonword_aggregate_tag >>
  `post_value_type ce e = lowered_value_type ce e` by
    (qpat_x_assum `post_value_type ce e = _ \/ _` mp_tac >> simp[]) >>
  `value_has_type dtv v` by
    (qpat_assum `type_widens_to _ (lowered_value_type ce e) dty`
       (mp_then Any mp_tac type_widens_to_value_has_type) >> simp[]) >>
  drule_then assume_tac value_has_type_memory_wf >>
  `val_wf dtv v` by simp[value_has_type_memory_wf] >>
  `type_memory_size dtv <= MAX 32 (type_memory_bytes ce dty)` by simp[MAX_DEF] >>
  `base + type_memory_size dtv < dimword (:256) /\
   base + type_memory_size dtv <= z.vs_alloca_next` by decide_tac >>
  `ptr_covers Gf tf dst z (type_memory_size dtv)` by
    (irule ptr_covers_mono >> qexists `MAX 32 (type_memory_bytes ce dty)` >> simp[]) >>
  qexists `rt` >> asm_rewrite_tac[struct_operand_mods_def] >>
  qexists `w` >> asm_rewrite_tac[] >> strip_tac >>
  `w2n w + type_memory_size rt <= z.vs_alloca_next` by decide_tac >>
  `val_footprint rt v = type_memory_size rt` by
    (irule nonbytes_evaluated_val_footprint >>
     qexistsl [`get_tenv cx`,`lowered_value_type ce e`] >> simp[]) >>
  asm_rewrite_tac[] >>
  suspend "apart"
QED

(* Outside the retained locations, the compiler must emit an allocation. *)
Theorem intcall_nonword_located_unwrap_growth[local]:
  unwrap_value ce (LocatedValue tag p) ca = (op,cu) /\
  fn_has_code ca cu func /\ ~is_word_type tag /\
  p.ptr_location <> LocMemory /\ p.ptr_location <> LocCalldata ==>
  ca.cs_next_id < cu.cs_next_id
Proof
  strip_tac >>
  `?n buf cut. compile_alloc_buffer n ca = (buf,cut) /\
               cut.cs_next_id <= cu.cs_next_id` suffices_by
    (strip_tac >> drule_then strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts >>
     decide_tac) >>
  Cases_on `p.ptr_location = LocCode`
  >- (`?buf cut. compile_alloc_buffer (type_memory_bytes ce tag) ca = (buf,cut) /\
        compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
          buf.buf_operand ((type_memory_bytes ce tag + 31) DIV 32) 0 cut = ((),cu)` by
       (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
        simp[exprLoweringTheory.unwrap_value_def,compile_ensure_in_memory_def,
             comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
        pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
      `ci_mono cut cu` by metis_tac[ci_mono_compile_imm_copy_to_memory,pairTheory.SND] >>
      qexistsl [`type_memory_bytes ce tag`,`buf`,`cut`] >> fs[ci_mono_def]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` suffices_by
    (disch_tac >> drule_all_then strip_assume_tac exprSimMemUnwrapTheory.storage_unwrap_layout_facts >>
     qexistsl [`type_memory_bytes ce tag`,`buf`,`mid`] >> simp[]) >>
  Cases_on `p.ptr_location` >> gvs[]
QED

Resume intcall_buffer_nonword_input_mods[apart]:
  conj_tac >-
    (qpat_assum `0 < type_memory_size rt ==> _` (drule_then assume_tac) >> metis_tac[]) >>
  qpat_x_assum `cu = ca /\ _ \/ ca.cs_next_id < cu.cs_next_id /\ _`
    (DISJ_CASES_THEN strip_assume_tac)
  >- (`(?tag. vv = StackValue tag (vv_operand vv)) \/
       (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)` suffices_by
        (disch_tac >>
         qpat_x_assum `z = a` SUBST_ALL_TAC >>
         qpat_x_assum `op = vv_operand vv` SUBST_ALL_TAC >>
         qpat_assum `!w. eval_operand (vv_operand vv) a = SOME w ==> _`
           (drule_then assume_tac) >>
         `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt` by
           (qpat_assum `post_value_type ce e = lowered_value_type ce e`
              (fn th => pure_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
         `0 < val_footprint rt v` by
           (qpat_assum `val_footprint rt v = type_memory_size rt`
              (fn th => pure_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
         qpat_assum `val_footprint rt v = type_memory_size rt`
           (fn th => pure_rewrite_tac [GSYM th]) >>
         irule intcall_retained_source_apart >> asm_rewrite_tac[] >>
         qpat_assum `vv_at ce cx _ si ci mid raw vv s` (irule_at Any) >>
         qpat_assum `FLOOKUP a.vs_allocas ci.cs_next_id = SOME (base,_)`
           (irule_at Any) >> asm_rewrite_tac[]) >>
      Cases_on `vv` >> simp[vv_operand_def] >>
      rename1 `unwrap_value ce (LocatedValue tag p) ca = (op,cu)` >>
      CCONTR_TAC >>
      `~is_word_type tag` by
        (qpat_assum `vv_type (LocatedValue tag p) = lowered_value_type ce e`
           (SUBST1_TAC o REWRITE_RULE [vv_type_def]) >> first_assum ACCEPT_TAC) >>
      `p.ptr_location <> LocCalldata` by
        (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ ca _ _ _ (LocatedValue tag p) a`
           (strip_assume_tac o PURE_REWRITE_RULE [vv_post_mods_def]) >>
         qpat_x_assum `vv_holds_mods _ _ _ _ (LocatedValue tag p) _ a` mp_tac >>
         Cases_on `p.ptr_location` >> simp[vv_holds_mods_def,vv_holds_def]) >>
      drule_all_then mp_tac intcall_nonword_located_unwrap_growth >>
      qpat_assum `cu = ca` SUBST1_TAC >> simp[]) >>
  qpat_assum `!aid b len. aid < ca.cs_next_id /\
                FLOOKUP a.vs_allocas aid = SOME (b,len) ==> _`
    (drule_all_then mp_tac) >>
  qpat_assum `type_memory_size dtv <= MAX 32 (type_memory_bytes ce dty)` mp_tac >>
  pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise intcall_buffer_nonword_input_mods
