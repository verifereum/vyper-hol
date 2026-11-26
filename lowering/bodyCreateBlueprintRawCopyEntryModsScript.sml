(* Linked allocation and qualified source unwrap at a raw blueprint copy entry. *)
Theory bodyCreateBlueprintRawCopyEntryMods
Ancestors
  bodyIfExpAllocMods bodyFullExtCallDefaultUnwrapMods
  abiCallerAllocation abiCallerLocalScratch bodyFullHashKeccakFixed
  exprSimIfExpWidenedAdapter fragGasOriginPtrLoop exprLoweringProps
  bodyFullPostsMods bodyFullAllocaFresh bodyMemoryDefs bodyPtrIfExpAllocCompiler
  bodyFullShadowBodyInv bodyPtrDefs fragGasOriginPtr exprSimWordArgs
  exprLowering compileEnv loweringPosts loweringStateRelDefs
  exprSimProps exprSimAlloc freshWrites stateRelProj
  vyperEvalExprPreservesScopesDom vyperStorageFootprint
  vyperInterpreter vyperState venomState finite_map words arithmetic
Libs pairLib

Theorem blueprint_raw_copy_entry_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_alloc_buffer (type_memory_bytes ce (vv_type vv)) sm = (buf,sn) /\
  unwrap_value ce vv sn = (op,sc) /\
  fn_has_code sm sn func /\ fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  type_memory_bytes ce (vv_type vv) < dimword (:256) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size ptv /\
  type_memory_size ptv < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
  0 < type_memory_size ltv /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  read_result cx tv ee = (INL (BytesV bs),ee) /\
  value_has_type ptv (BytesV bs) /\ value_has_type ltv (BytesV bs) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> 
      vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok ce e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sm s /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q dw z Gz tz x sw.
    buf.buf_operand = Var q /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       expr_post_mods H ctx func ce cx e es sa sc s0 ee (BytesV bs) op z /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (!v. not_fresh_at sm v ==> lookup_var v z = lookup_var v s /\
         FLOOKUP Gz v = FLOOKUP G v /\ op_taint tz (Var v) = op_taint tn (Var v)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = s.vs_labels /\ ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ return_buf_frame d ce sc z /\
    not_fresh_at sc q /\ lookup_var q z = SOME dw /\
    ptr_covers Gz tz q z (type_memory_bytes ce (vv_type vv)) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_bytes ce (vv_type vv)) /\
    FLOOKUP Gz q = SOME (w2n dw,type_memory_bytes ce (vv_type vv)) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (vv_type vv)))] [q]) (fn_insts func) /\
    lo <= w2n dw /\ w2n dw + type_memory_bytes ce (vv_type vv) <= z.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_bytes ce (vv_type vv)) b len) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n dw) (type_memory_bytes ce (vv_type vv)) b len) /\
    op = Var x /\ not_fresh_at sc x /\ lookup_var x z = SOME sw /\
    val_wf ltv (BytesV bs) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
       val_in_memory ltv (BytesV bs) (w2n sw) mem) /\
    ptr_covers Gz tz x z (type_memory_size ltv) /\
    w2n sw + type_memory_size ltv <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v rt. read_result cx tv ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt ==>
    value_has_type rt v` by simp[] >>
  mp_tac (Q.INST [`n` |-> `type_memory_bytes ce (vv_type vv)`, `k` |-> `sn`]
    ifexp_arm_result_alloc_mods) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then (qx_choosel_then [`p`,`dw0`,`u`,`Ga`,`ta`,`raw`]
    (map_every assume_tac o CONJUNCTS)) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `vv_post_mods (storage_trace_horizon ee.storage_trace)
      ctx func ce cx e es sa sm s0 ee tv vv s` by
    (qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[vv_post_mods_def] >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s` by
    suspend "alloc_record" >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  `ghost_kept_at lo ce es sa Gi ti s0 Ga ta` by suspend "alloc_ghost" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta u` by suspend "alloc_post" >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id < sn.cs_next_id /\
    s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
      value_has_type ptv v /\ value_has_type ltv v` by simp[] >>
  mp_tac (Q.INST [`n` |-> `type_memory_bytes ce (vv_type vv)`, `cenv` |-> `ce`,
                `q` |-> `p`, `dw` |-> `dw0`]
    extcall_default_unwrap_store_entry_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`v`,`z`,`Gz`,`tz`,`sw`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "join"
QED

Resume blueprint_raw_copy_entry_mods[alloc_record]:
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qx_choosel_then [`q'`,`dw'`,`u'`,`Ga'`,`ta'`,`raw'`]
    (map_every assume_tac o CONJUNCTS) o SPEC_ALL) >>
  `raw' = raw` by
    (qpat_x_assum `run_inst_seq _ s = OK raw'` mp_tac >>
     qpat_assum `run_inst_seq _ s = OK raw` (fn th => simp[th])) >>
  `u' = u` by
    (qpat_assum `u' = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_assum `u' with <| vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _ |> = s`
    (fn th => qpat_assum `u' = u` (fn eq => ACCEPT_TAC (REWRITE_RULE [eq] th)))
QED

Resume blueprint_raw_copy_entry_mods[alloc_ghost]:
  qpat_assum `stmt_state_rel H0 _ _ _ _ es s0`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
      b + len <= s.vs_alloca_next` by
    (rpt strip_tac >> irule LESS_EQ_TRANS >> qexists `s0.vs_alloca_next` >>
     simp[] >> irule abi_caller_allocation_end >> simp[] >>
     qexistsl [`len`,`aid`,`b`] >> simp[]) >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
      b + len <= s.vs_alloca_next` by
    (rpt strip_tac >> irule LESS_EQ_TRANS >> qexists `s0.vs_alloca_next` >>
     simp[] >> irule abi_caller_local_end >>
     qexistsl [`ce`,`func`,`name`,`es.scopes`] >> simp[]) >>
  irule alloc_buffer_ghost_kept_at >>
  qexistsl [`G`,`w2n dw0 + type_memory_bytes ce (vv_type vv)`,`s`,`tn`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> disch_tac >>
      `not_fresh_at sm x` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      simp[]) >>
  rpt strip_tac >>
  qpat_assum `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) ==> _`
    (drule_then assume_tac) >> decide_tac
QED

Resume blueprint_raw_copy_entry_mods[alloc_post]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_mods_def])) >>
  qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ sn _ _ _ _ u /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_mods_def])) >>
  asm_rewrite_tac[vv_post_mods_def] >> conj_tac
  >- (irule vv_at_alloc_mono_frame >> qexistsl [`s`,`sm`] >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  disch_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`s`,`sm`] >> simp[]
QED

Resume blueprint_raw_copy_entry_mods[join]:
  `v = BytesV bs` by
    (qpat_x_assum `read_result cx tv ee = (INL v,ee)` mp_tac >>
     qpat_assum `read_result cx tv ee = (INL (BytesV bs),ee)` (fn th => simp[th])) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `!v. not_fresh_at sm v ==> lookup_var v z = lookup_var v s /\
        FLOOKUP Gz v = FLOOKUP G v /\ op_taint tz (Var v) = op_taint tn (Var v)` by
    (qx_gen_tac `y` >> disch_tac >>
     `not_fresh_at sn y` by (irule not_fresh_at_mono >> qexists `sm` >> simp[]) >> simp[]) >>
  `?x. op = Var x /\ ptr_covers Gz tz x z (type_memory_size ltv)` by simp[] >>
  `s.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `return_buf_frame d ce sc z` by suspend "retbuf" >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (vv_type vv)))] [p])
     (fn_insts func)` by
    (drule_all_then strip_assume_tac compile_alloc_buffer_raw_step >> gvs[]) >>
  qexistsl [`p`,`dw0`,`z`,`Gz`,`tz`,`x`,`sw`] >>
  simp[eval_operand_def] >> rpt conj_tac
  >- suspend "path"
  >- suspend "old_allocas"
  >> fs[eval_operand_def]
QED

Resume blueprint_raw_copy_entry_mods[retbuf]:
  `sn.cs_next_var <= sc.cs_next_var` by
    (qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  irule return_buf_frame_frame >>
  qpat_assum `return_buf_frame d ce sm s` (irule_at Any) >> simp[] >> decide_tac
QED

Resume blueprint_raw_copy_entry_mods[path]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path (DF H,_,_,_,_,_) (u,Ga,ta) [] _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[] >>
  irule gas_origin_ptr_path_trans >> qexistsl [`Ga`,`u`,`ta`] >> simp[]
QED

Resume blueprint_raw_copy_entry_mods[old_allocas]:
  rpt strip_tac >>
  qpat_assum `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> _`
    (drule_then assume_tac) >>
  qpat_assum `wb_frame ce ee ee sn u z` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  simp[]
QED

Finalise blueprint_raw_copy_entry_mods
