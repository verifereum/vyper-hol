(* The private snapshot store runs in the original registered function.
   The pointer path and band certificate use the same sequence result. *)
Theory createCtorMaterializeStoreMods
Ancestors
  createCtorMaterializeStore createExprSizeExitDefsMods
  createCtorSegmentArrival createCtorStraightBand abiEncodeMaterializeExec abiEncodeMaterialize
  exprLoweringProps fragExecMem loweringPosts loweringStateRelDefs ptrDiscipline
  bodyFullMemoryFrames bodyCopyMemoryBase assignTuplePtrLocalFixedCopy
  logBytesSeqPtr instSeqPtrLo bodyPtrIfExpBytesCounted valueCopyBytes memSafeRun unitTransformDefs
  representationCleanPtr robustCopyTransportPtr bytesCopyCode stateRelProj
  assignTuplePtrCopyLen exprSimCopy exprSimProps exprSimStorageCopy
  exprSimWordArgs fragGasSeqPtr fragExec emitHelperProps bodyPtrDefs
  ghostObservationPtr venomMemDefs
  context compileEnv venomExecSemantics venomInst venomState valueEncodingDefs
  valueEncodingProps vfmConstants arithmetic relation rich_list list words finite_map

Theorem ctor_store_code_mods[local]:
  compile_store_memory ce src dst ty ty a = ((),b) /\ ~is_word_type ty ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
    i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> DALLOCA)
    (emitted_insts a b)
Proof
  simp[compile_store_memory_def] >> strip_tac >> Cases_on `is_bytestring_type ty`
  >- (fs[] >> drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
      `b.cs_next_id = a.cs_next_id + 6` by
        gvs[compile_store_bytestring_def,compile_bytestring_copy_len_def,
          emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
      simp[same_blocks_def,bytes_copy_insts_def,mk_inst_def,is_terminator_def] >>
      fs[same_blocks_def]) >>
  Cases_on `type_memory_bytes ce ty` >>
  gvs[compile_copy_memory_def,emitHelperTheory.emit_void_def,
      comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_id_def,emit_def,
      emitted_insts_def,DROP_APPEND1,DROP_LENGTH_NIL,mk_inst_def,is_terminator_def]
QED

Theorem ctor_materialize_store_arrival_mods:
  compile_store_memory ce src (Var p) (lowered_value_type ce e)
    (lowered_value_type ce e) su = ((),sb) /\
  ~is_word_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  n = (if is_bytestring_type (lowered_value_type ce e) then val_store_size tv v
       else type_memory_size tv) /\
  fn_has_code su sb func /\ ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at su x) /\ not_fresh_at su p /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (0 < n ==> w2n sw + n <= s.vs_alloca_next /\
             (?x. src = Var x /\ ptr_covers G tn x s n)) /\
  ptr_covers G tn p s (type_memory_size tv) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
  sa.cs_next_id <= inst.inst_id /\ sa.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce su /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
  HP H0 /\ (!H. HP H ==> stmt_state_rel H ctx func ce cx ee s /\
                         immutable_frame_mods func ce cx ee s /\
                        ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  wb_frame ce es ee sa s0 s /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 s) ==>
  ?t Gt tt.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
         su.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
         i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    lookup_var p t = SOME dw /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    ptr_val_ok cx (lowered_value_type ce e) v (Var p) Gt tt t /\
    ptr_buf_ok ce e (Var p) Gt t /\
    (!name b len. local_region ce ee.scopes t name b len ==>
       w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
    (!H. HP H ==> stmt_state_rel H ctx func ce cx ee t /\
                  immutable_frame_mods func ce cx ee t /\
                  ghost_inv_at_mods (DF H) lo d ce cx ee Gt tt t) /\
    wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gt tt /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ty = lowered_value_type ce e` >>
  `val_footprint tv v <= n /\ n <= type_memory_size tv` by
    (Cases_on `is_bytestring_type ty` >> fs[] >>
     metis_tac[val_footprint_le_store_size,val_store_size_le,val_footprint_le]) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `0 < n ==> w2n sw + n <= s.vs_alloca_next /\
    w2n dw + n <= s.vs_alloca_next /\
    (?x. src = Var x /\ ptr_covers G tn x s n) /\ ptr_covers G tn p s n` by
    (qpat_x_assum `n = _` kall_tac >> strip_tac >>
     qpat_assum `0 < n ==> _` (drule_then strip_assume_tac) >>
     simp[] >>
     qpat_assum `ptr_covers G tn p s (type_memory_size tv)`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def] >> qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac) >>
  `if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory` by simp[] >>
  drule_all materialize_store_owned_run >>
  disch_then (qx_choose_then `r` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  (`?Gr tr. run_inst_seq_mem_ok (emitted_insts su sb) s /\
   inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|> 0 ctx func PG G tn (emitted_insts su sb) s Gr tr /\
   tr.t_stor = tn.t_stor /\ tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
   (!x. not_fresh_at su x ==>
      FLOOKUP Gr x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x)) /\
   mem_bytes_at (w2n dw) n r.vs_memory = mem_bytes_at (w2n sw) n s.vs_memory /\
   (!i. i < n ==> (w2n dw + i IN tr.t_mem <=> w2n sw + i IN tn.t_mem)) /\
   (!i. ~(w2n dw <= i /\ i < w2n dw + n) ==>
      (i IN tr.t_mem <=> i IN tn.t_mem))` by
    (Cases_on `is_bytestring_type ty`
     >- (drule_all ctor_store_byte_header >> strip_tac >>
         `0 < n /\ len + 31 < dimword (:256)` by
           (`len + 31 < ((len + 31) DIV 32 + 1) * 32` by simp[GSYM DIV_LE_X] >>
            fs[word_size_def, Once MULT_COMM, RIGHT_ADD_DISTRIB] >> decide_tac) >>
         qpat_assum `0 < n ==> _` (drule_then strip_assume_tac) >> gvs[] >>
         `compile_store_bytestring (Var x) (Var p) su = ((),sb)` by
           fs[compile_store_memory_def] >>
         `run_inst_seq_mem_ok (emitted_insts su sb) s` by
           (drule compile_store_bytestring_body_mem_ok >>
            disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
            disch_then (qspec_then `len` mp_tac) >>
            simp[eval_operand_def] >> metis_tac[]) >>
         pop_assum $ mk_asm "mem_ok" >>
         drule logBytesSeqPtrTheory.compile_store_bytestring_seq_ptr >>
         disch_then (drule_at (Pat `mload _ _ = _`)) >>
         simp[GSYM word_size_def] >>
         disch_then (qspecl_then [`tn`,`func`,`ctx`,`PG`,`G`,`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >>
         (impl_tac >- fs[eval_operand_def]) >>
         strip_tac >> qexistsl_tac [`Gf`,`tnf`] >>
         conj_tac >- (asm "mem_ok" ACCEPT_TAC) >>
         simp[mcopy_mem_bytes_at_same] >>
         qpat_assum `!i. (~(w2n dw <= i) \/
           ~(i < w2n dw + (32 * word_size len + 32))) ==> _` ACCEPT_TAC)
     >> Cases_on `n = 0`
     >- (`sb = su` by fs[compile_store_memory_def,compile_copy_memory_def,comp_return_def] >>
         qexistsl_tac [`G`,`tn`] >>
         gvs[emitted_insts_def,rich_listTheory.DROP_LENGTH_NIL,run_inst_seq_def,
             inst_seq_ptr_def,run_inst_seq_mem_ok_def,mem_bytes_at_def])
     >> (`0 < n` by decide_tac >>
         qpat_assum `0 < n ==> _` (drule_then strip_assume_tac) >> gvs[eval_operand_def] >>
         `run_inst_seq_mem_ok (emitted_insts su sb) s` by
           (irule compile_copy_memory_body_mem_ok >>
            qexistsl_tac [`dw`,`Var p`,`type_memory_size tv`,`Var x`,`sw`] >>
            fs[compile_store_memory_def,eval_operand_def]) >>
         drule compile_fixed_copy_sequence_ptr >>
         disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
         disch_then (drule_at (Pat `lookup_var _ _ = SOME sw`)) >>
         simp[] >>
         disch_then (qspecl_then [`func`,`ctx`,`PG`,`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >> simp[] >> strip_tac >>
         qexistsl_tac [`G`,
           `step_taint (mk_inst su.cs_next_id MCOPY [Var p;Var x;Lit (n2w (type_memory_size tv))] [])
              s (mcopy (w2n dw) (w2n sw) (type_memory_size tv) s) tn`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         asm_rewrite_tac[] >>
         mp_tac (Q.SPECL [`tn`,`s`,`su.cs_next_id`,`Var p`,`Var x`,
           `Lit (n2w (type_memory_size tv))`] mcopy_operand_taint_frames_ptr) >>
         simp[eval_operand_def,op_taint_def,mcopy_mem_bytes_at_same] >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         first_assum ACCEPT_TAC)))
  >>
  rename1 `run_inst_seq (emitted_insts su sb) s = OK r` >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
         su.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
         i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s t /\
   (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gr,tr)) /\
   t.vs_current_bb = sb.cs_current_bb` by suspend "traversal" >>
  suspend "store_frame"
QED

Resume ctor_materialize_store_arrival_mods[traversal]:
  drule_all ctor_store_code_mods >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts su sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def,IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts su sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts su sb) /\
   EVERY (\i. su.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id)
     (emitted_insts su sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts su sb) = []` by
    (fs[EVERY_MEM,FILTER_EQ_NIL] >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==>
     !pre i post v. emitted_insts su sb = pre ++ i::post /\
       run_inst_seq pre s = OK v ==> dalloca_no_wrap i v)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_assum `EVERY (\ins. _ /\ _ /\ _ /\ _ /\ _ /\ ins.inst_opcode <> DALLOCA)
       (emitted_insts su sb)` (fn th =>
       qpat_assum `emitted_insts su sb = pre ++ i::post` (fn eq =>
         mp_tac (REWRITE_RULE[eq, EVERY_APPEND, EVERY_DEF] th))) >>
     simp[]) >>
  conj_tac >- (drule_all ctor_straight_band_run >> simp[Abbr `t`]) >>
  conj_tac
  >- (gen_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. HP H ==> _` (drule_then strip_assume_tac) >>
     fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts su sb) s Gr tr` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
   drule_all run_inst_seq_gas_origin_ptr_path >> simp[Abbr `t`]) >>
  simp[Abbr `t`] >> drule_all bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >> simp[]
QED

Resume ctor_materialize_store_arrival_mods[store_frame]:
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   t.vs_memory = r.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (simp[Abbr `t`] >>
     qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at su x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP Gr x = FLOOKUP G x /\
     op_taint tr (Var x) = op_taint tn (Var x)` by
    fs[Abbr `t`,lookup_var_def] >>
  `!name b len. local_region ce ee.scopes t name b len <=>
                local_region ce ee.scopes s name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tr.t_mem t.vs_memory mem ==>
         val_in_memory tv v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >> simp[] >>
     qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`n`,`w2n sw`,`tn.t_mem`,`tr.t_mem`] >>
     qpat_x_assum `n = _` kall_tac >> simp[] >> fs[]) >>
  `ptr_covers Gr tr p t (type_memory_size tv) /\ lookup_var p t = SOME dw` by
    (conj_asm2_tac >- (irule ptr_covers_lookup_frame >>
       qexistsl_tac [`G`,`s`,`tn`] >> fs[]) >> fs[]) >>
  qexistsl_tac [`t`,`Gr`,`tr`] >> simp[] >>
  conj_tac >- (fs[ptr_val_ok_def,ptr_mem_ok_def,eval_operand_def,ptr_covers_def] >>
               drule val_store_size_le >> decide_tac) >>
  conj_tac >- (fs[ptr_buf_ok_def,eval_operand_def,ptr_covers_def,Abbr `ty`] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[ADD_COMM]) >>
  conj_tac >- suspend "horizon" >>
  suspend "rest"
QED

Resume ctor_materialize_store_arrival_mods[horizon]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. HP H ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule copy_buffer_state_rel_frame >>
      qexistsl_tac [`w2n dw`,`inst`,`s`,`su`,`type_memory_size tv`] >> simp[] >>
      qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      fs[Abbr `t`,copy_static_def,venom_state_component_equality] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "immutables" >>
  suspend "ghost"
QED

Resume ctor_materialize_store_arrival_mods[immutables]:
  fs[bodyFullPostsModsTheory.immutable_frame_mods_def] >>
  conj_tac
  >- (fs[bodyInvSplitTheory.immutables_rel_mods_def] >>
      rpt gen_tac >> strip_tac >> irule loweringSliceTheory.immutables_rel_mem_agree >>
      qexists_tac `s` >> simp[] >>
      qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutables_rel _ _ _ _ _ _`
        (drule_then assume_tac) >>
      simp[] >> rpt strip_tac >>
      qpat_assum `immutable_alloca_sep_mods _ _ _ _ _`
        (mp_tac o REWRITE_RULE [bodyInvSplitTheory.immutable_alloca_sep_mods_def]) >>
      disch_then (drule_then mp_tac) >>
      simp[immutable_alloca_sep_def,PULL_EXISTS] >> strip_tac >>
      qpat_assum `!off len. _ ==> mem_bytes_at off len r.vs_memory = _` irule >>
      qpat_assum `!nm tvv vv off. _ ==> _ /\ _` (drule_all_then strip_assume_tac) >>
      qpat_assum `!ins b sz. _ ==> regions_disjoint _ _ _ _` (drule_all_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def,ADD_COMM]) >>
  fs[bodyInvSplitTheory.immutable_alloca_sep_mods_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then assume_tac) >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`ee`] >> simp[] >>
  simp[local_region_def] >> metis_tac[local_ptrs_reserved_def]
QED

Resume ctor_materialize_store_arrival_mods[ghost]:
  qabbrev_tac `writes = {i | w2n dw <= i /\ i < w2n dw + type_memory_size tv}` >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next /\ lo <= w2n dw` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     fs[allocas_from_def] >> metis_tac[]) >>
  `!i. i NOTIN writes ==> (i IN tr.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. ~(w2n dw <= i /\ i < w2n dw + n) ==> _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- (qpat_x_assum `n = _` kall_tac >> fs[Abbr `writes`] >> decide_tac)) >> simp[]) >>
  `!i. i NOTIN writes ==>
       mem_bytes_at i 1 r.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (gen_tac >> strip_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len r.vs_memory = _` irule >>
     fs[Abbr `writes`] >> decide_tac) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by simp[] >>
  `!i. i < lo /\ i IN tr.t_mem ==> i IN tn.t_mem` by
    (gen_tac >> strip_tac >>
     `i NOTIN writes` by (simp[Abbr `writes`] >> decide_tac) >>
     qpat_assum `!i. i NOTIN writes ==> (i IN tr.t_mem <=> _)` (drule_then mp_tac) >>
     simp[]) >>
  `!p sz. not_fresh_at su p /\ ptr_covers G tn p s sz ==>
    ptr_covers Gr tr p t sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  simp[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  conj_tac >- suspend "ghost_locals" >>
  conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- fs[stor_taint_ok_at_def] >>
  rpt strip_tac >>
  `not_fresh_at su x` by fs[local_ptrs_reserved_def] >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x t = _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[] >> metis_tac[]
QED

Resume ctor_materialize_store_arrival_mods[ghost_locals]:
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var px) sz)` >>
  `not_fresh_at su px` by
    (qpat_assum `local_ptrs_reserved ce su` (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     strip_tac >> qpat_assum `!n1 n2 p sz1 sz2. _ ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1 o SPEC_ALL))) >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x t = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers G tn p s sz /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var px s = SOME w` by fs[] >>
  `local_region ce ee.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (drule stmt_state_rel_local_ptrs_alloca >>
     disch_then (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     qpat_x_assum `!name entry p sz. _ ==> _` (drule_all_then strip_assume_tac) >>
     gvs[]) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
       i NOTIN writes` by
    (`val_footprint entry.type entry.value <= type_memory_size entry.type` by
       simp[val_footprint_le] >>
     qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
       (drule_then mp_tac) >>
     simp[Abbr `writes`] >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`s.vs_memory`,`r.vs_memory`,`tn.t_mem`,`tr.t_mem`,`writes`] >>
  simp[]
QED

Resume ctor_materialize_store_arrival_mods[rest]:
  qpat_assum `!H. HP H ==> _` (drule_then strip_assume_tac) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac
  >- (irule materialize_fresh_store_frame >>
      qexistsl_tac [`inst.inst_id`,`w2n dw`,`s`,`type_memory_size tv`] >>
      fs[alloca_inv_def] >> metis_tac[]) >>
  conj_tac >- suspend "kept" >>
  strip_tac >> irule pure_frame_buffer_tail >>
  qexistsl_tac [`w2n dw`,`type_memory_size tv`,`inst`,`s`] >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_materialize_store_arrival_mods[kept]:
  rewrite_tac [ghost_kept_at_def,GSYM ghost_kept_def] >>
  irule ghost_kept_exterior_frame >>
  qexistsl_tac [`G`,`{i | w2n dw <= i /\ i < w2n dw + type_memory_size tv}`,`tn`] >>
  `ghost_kept ce es sa G0 tn0 s0 G tn` by
    (PURE_REWRITE_TAC [ghost_kept_def,GSYM ghost_kept_at_def] >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `not_fresh_at su x` by
        (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at su x` (drule_then ACCEPT_TAC)) >>
      qpat_assum `!x. not_fresh_at su x ==> lookup_var x t = _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name b len. local_region ce es.scopes s0 name b len ==> _`
        (drule_then strip_assume_tac) >> simp[] >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by fs[wb_frame_def] >>
      `allocas_non_overlapping s` by fs[alloca_inv_def] >>
      `off + sz <= w2n dw \/ w2n dw + type_memory_size tv <= off` by
        (qpat_assum `allocas_non_overlapping s`
           (irule o REWRITE_RULE [allocas_non_overlapping_def]) >>
         qexistsl_tac [`aid`,`inst.inst_id`] >> simp[] >> decide_tac) >>
      simp[] >> decide_tac) >>
  gen_tac >> simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_assum `!i. ~(w2n dw <= i /\ i < w2n dw + n) ==> _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED

Finalise ctor_materialize_store_arrival_mods
