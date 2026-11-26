(* Restore a saved slot at the post-setup cursor, not by replaying its child. *)
Theory bodyAbiEncodeSavedSlotMods
Ancestors
  bodyAbiEncodePackedPostMods bodyCopySlotRhsEndpointMods bodyCopyMaterializedRhsPostMods
  bodyFullPostsMods bodyFullShadowBodyInv exprOperandVar exprLoweringProps
  exprSimProps freshWrites localPtrsProps stateRelProj bodyMemoryDefs
  bodyFullHashKeccakFixed
  bodyPtrDefs loweringPosts loweringStateRelDefs exprSimStorageCopy ptrDiscipline
  valueEncodingProps vyperStorageFootprint vyperState vyperInterpreter
  fragGasOriginPtr fragExec exprLowering compileEnv context venomInst venomState
  words finite_map pred_set arithmetic

(* The slot carries a read of v. Its copy does not use the original raw
   result's place identity: use Value v when viewing this same state as a
   zero-width linked post. In the slot clauses ptr_vv_ok is raw-independent. *)
Theorem saved_slot_cut_post[local]:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  post_value_type ce e = expr_type e /\
  vv_holds_mods ce cx (expr_type e) raw (LocatedValue (expr_type e) p) ee s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn s /\
  vv_storage_live H cx (LocatedValue (expr_type e) p) ee s /\
  stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
  storage_well_formed_on cx ee (FST H) ==>
  vv_post_mods H ctx func ce cx e ee ready ready s ee (Value v)
    (LocatedValue (expr_type e) p) s /\
  ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[vv_post_mods_def, vv_at_def, vv_place_ptr_mods_def, vv_place_ptr_def] >>
  qpat_x_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
  fs[vv_holds_mods_def, vv_holds_def, ptr_vv_ok_def, storage_holds_def,
     read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

Theorem saved_slot_region_kept[local]:
  regions_disjoint dst nb b len /\
  (!off n. off+n <= dst \/ dst+nb <= off ==>
    mem_bytes_at off n z.vs_memory = mem_bytes_at off n s.vs_memory) /\
  (!j. j < dst \/ dst+nb <= j ==> j IN tf.t_mem ==> j IN tn.t_mem) ==>
  mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
  (!j. b <= j /\ j < b+len /\ j IN tf.t_mem ==> j IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[regions_disjoint_def]
QED

(* Keep the allocation step and copy frame for the very same restore exit. *)
Theorem abi_encode_saved_slot_restore_packet_mods:
  saved = LocatedValue (lowered_value_type ce e) p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  unwrap_value ce saved ready = (src,sc) /\ fn_has_code ready sc func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ return_buf_frame d ce ready s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?z Gz tz w root.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    src = Var root /\ not_fresh_at sc root /\ eval_operand src z = SOME w /\
    op_taint tz src = {} /\ ptr_covers Gz tz root z (type_memory_size rt) /\
    val_wf rt v /\ lo <= w2n w /\ w2n w + type_memory_size rt < dimword (:256) /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    expr_val_rel cx (lowered_value_type ce e) v src z /\
    expr_val_at ce cx (lowered_value_type ce e) ready sc ee v src z /\
    ptr_val_ok cx (lowered_value_type ce e) v src Gz tz z /\
    ptr_buf_ok ce e src Gz z /\ expr_store_bound cx (lowered_value_type ce e) v src z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    return_buf_frame d ce sc z /\ pure_frame ce func ee ready s z /\
    wb_frame ce ee ee ready s z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    ready.cs_next_id < sc.cs_next_id /\ ready.cs_next_var < sc.cs_next_var /\
    FLOOKUP z.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!aid b len. aid < ready.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size rt) b len /\
      mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!j. b <= j /\ j < b+len /\ j IN tz.t_mem ==> j IN tn.t_mem)) /\
    mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!j. j < lo /\ j IN tz.t_mem ==> j IN tn.t_mem) /\
    MEM (mk_inst ready.cs_next_id ALLOCA
      [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
    (?u. exec_alloca (mk_inst ready.cs_next_id ALLOCA
            [Lit (n2w (type_memory_size rt))] [root]) s
            (n2w (type_memory_size rt) : bytes32) = OK u /\
         FLOOKUP u.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
         copy_static z = copy_static u) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size rt <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. i < w2n w \/ w2n w + type_memory_size rt <= i ==>
      i IN tz.t_mem ==> i IN tn.t_mem) /\
    z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
    z.vs_data_section = s.vs_data_section /\
    tz.t_stor = tn.t_stor /\ tz.t_trans = tn.t_trans /\ tz.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_row_mods_def]) >>
  `~is_word_type (lowered_value_type ce e) /\ lowered_value_type ce e = expr_type e /\ saved = vv` by
    (qpat_x_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
     qpat_x_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
     qpat_x_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[]) >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  `si.cs_next_var <= ready.cs_next_var` by
    (drule (cj 1 compile_expr_grows) >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce ready` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at ready x` by
    metis_tac[not_fresh_at_mono] >>
  `!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at ready x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at ready x` by
    (qpat_x_assum `saved = vv` SUBST_ALL_TAC >>
     qpat_x_assum `_ = LocatedValue _ _` SUBST_ALL_TAC >>
     drule (cj 1 compiler_compile_var) >> simp[vv_operand_def] >>
     disch_tac >> gen_tac >> disch_tac >>
     irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def, vyperStateTheory.return_def] >>
  suspend "copy"
QED

Resume abi_encode_saved_slot_restore_packet_mods[copy]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e ee ready ready s ee (Value v)
      (LocatedValue (expr_type e) p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     qpat_x_assum `?raw. read_result cx raw ee = (INL v,ee) /\ _`
       (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
     qpat_x_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
     qpat_assum `lowered_value_type ce e = expr_type e`
       (fn th => rule_assum_tac (PURE_REWRITE_RULE[th])) >>
     drule_all saved_slot_cut_post >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e ee ready ready s ee (Value v)
      (LocatedValue (expr_type e) p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by simp[] >>
  `ptr_vv_ok cx (post_value_type ce e) (Value v) (LocatedValue (expr_type e) p) ee G tn s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ ptr_vv_ok _ _ _ _ _ _ _ _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`t` |-> `expr_type e`, `op` |-> `src`, `sm` |-> `ready`,
                  `sa` |-> `ready`, `es` |-> `ee`, `entry` |-> `s`, `tv` |-> `Value v`]
    copy_slot_rhs_endpoint_mods) >>
  (impl_tac >- (gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`w`,`mid`,`buf`,`u`,`z`,`Gz`,`tz`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "post"
QED

Resume abi_encode_saved_slot_restore_packet_mods[post]:
  qpat_x_assum `src = Var root` SUBST_ALL_TAC >>
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `~is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt` by
    (qpat_assum `lowered_value_type ce e = expr_type e`
       (fn th => pure_rewrite_tac[GSYM th]) >> asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e ee ready sc s ee v (Var root) z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\
    ptr_val_ok cx (post_value_type ce e) v (Var root) Gz tz z /\
    ptr_buf_ok ce e (Var root) Gz z /\ expr_store_bound cx (post_value_type ce e) v (Var root) z /\
    FLOOKUP z.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    not_fresh_at sc root /\ wb_frame ce ee ee ready s z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     mp_tac (Q.INST [`sm` |-> `ready`, `sa` |-> `ready`, `sb` |-> `sc`,
                     `es` |-> `ee`, `s0` |-> `s`, `Gi` |-> `G`, `ti` |-> `tn`,
                     `nb` |-> `type_memory_size rt`, `D` |-> `DF H`, `Gf` |-> `Gz`, `tf` |-> `tz`,
                     `vv` |-> `LocatedValue (expr_type e) p`, `tv` |-> `Value v`]
       (INST_TYPE [alpha |-> ``:256``] copy_materialized_rhs_post_mods)) >>
     (impl_tac >- asm_rewrite_tac[LESS_EQ_REFL, wordArgsPtrTheory.ghost_kept_at_refl]) >>
     simp[]) >>
  suspend "frame"
QED

Resume abi_encode_saved_slot_restore_packet_mods[frame]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[expr_post_mods_def, expr_post_def]) >>
  `stmt_state_rel H0 ctx func ce cx ee z` by simp[] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `expr_val_rel cx (post_value_type ce e) v (Var root) z /\
    expr_val_at ce cx (post_value_type ce e) ready sc ee v (Var root) z` by
    fs[expr_post_mods_def, expr_post_def] >>
  `op_taint tz (Var root) = {}` by fs[ptr_covers_def] >>
  `return_buf_frame d ce sc z` by
    (drule bodyMemoryDefsTheory.return_buf_frame_frame >>
     disch_then (qspecl_then [`ce`,`sc`,`z`] mp_tac) >> simp[] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at ready x ==> _ /\ _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `pure_frame ce func ee ready s z` by
    (irule pure_frame_buffer_tail >>
     qexistsl [`w2n w`,`type_memory_size rt`,
               `mk_inst ready.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]`,`s`] >>
     asm_rewrite_tac[mk_inst_def, pure_frame_refl, LESS_EQ_REFL] >>
     pure_rewrite_tac[regions_disjoint_def] >> conj_tac
     >- (qpat_assum `!n b len. local_region ce ee.scopes s n b len ==> _` mp_tac >>
         simp[DISJ_COMM]) >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` mp_tac >>
     simp[DISJ_COMM]) >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qpat_x_assum `post_value_type ce e = expr_type e`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE[th])) >>
  qpat_x_assum `lowered_value_type ce e = expr_type e` (fn th => pure_rewrite_tac[th]) >>
  qexistsl [`z`,`Gz`,`tz`,`w`,`root`] >> asm_rewrite_tac[] >>
  suspend "older"
QED

Resume abi_encode_saved_slot_restore_packet_mods[older]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `regions_disjoint (w2n w) (type_memory_size rt) b len` by
        (qpat_assum `!aid b len. aid < ready.cs_next_id /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >>
      simp[] >> irule saved_slot_region_kept >>
      qexistsl [`w2n w`, `type_memory_size rt`] >> asm_rewrite_tac[]) >>
  conj_tac
  >- (qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i. _ ==> i IN tz.t_mem ==> _` (qspec_then `j` mp_tac) >> simp[] >> decide_tac) >>
  asm_rewrite_tac[] >> qexists `u` >> asm_rewrite_tac[]
QED

Finalise abi_encode_saved_slot_restore_packet_mods

Theorem abi_encode_saved_slot_restore_mods:
  saved = LocatedValue (lowered_value_type ce e) p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  unwrap_value ce saved ready = (src,sc) /\ fn_has_code ready sc func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ return_buf_frame d ce ready s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?z Gz tz w root.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
    src = Var root /\ not_fresh_at sc root /\ eval_operand src z = SOME w /\
    op_taint tz src = {} /\ ptr_covers Gz tz root z (type_memory_size rt) /\
    val_wf rt v /\ lo <= w2n w /\ w2n w + type_memory_size rt < dimword (:256) /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    expr_val_rel cx (lowered_value_type ce e) v src z /\
    expr_val_at ce cx (lowered_value_type ce e) ready sc ee v src z /\
    ptr_val_ok cx (lowered_value_type ce e) v src Gz tz z /\
    ptr_buf_ok ce e src Gz z /\ expr_store_bound cx (lowered_value_type ce e) v src z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    return_buf_frame d ce sc z /\ pure_frame ce func ee ready s z /\
    wb_frame ce ee ee ready s z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    ready.cs_next_id < sc.cs_next_id /\ ready.cs_next_var < sc.cs_next_var /\
    FLOOKUP z.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!aid b len. aid < ready.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size rt) b len /\
      mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!j. b <= j /\ j < b+len /\ j IN tz.t_mem ==> j IN tn.t_mem)) /\
    mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!j. j < lo /\ j IN tz.t_mem ==> j IN tn.t_mem)
Proof
  disch_then (mp_tac o MATCH_MP abi_encode_saved_slot_restore_packet_mods) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`w`,`root`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`z`,`Gz`,`tz`,`w`,`root`] >> asm_rewrite_tac[]
QED
