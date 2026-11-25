(* A raw blueprint snapshot copies the live bytes, not the source capacity. *)
Theory createBlueprintRawBytesStoreMods
Ancestors
  createBlueprintRawBytesStore createExprSizeExitDefsMods
  createCtorStraightBand createCtorMaterializeStoreMods abiEncodeMaterializeExec abiEncodeMaterialize
  logBytesSeqPtr bodyCopyMemoryBase bytesCopyCode bodyPtrIfExpBytesCounted
  bodyFullMemoryFrames bodyFullUnwrapRun bodyMemoryDefs instSeqPtrLo
  valueCopyBytes representationCleanPtr assignTuplePtrCopyLen reasonCopySourcePtr
  ghostObservationPtr fragGasSeqPtr memSafeRun unitTransformDefs freshWrites valueEncodingProps
  createCtorMaterializeStore robustCopyTransportPtr
  stateRelProj exprSimCopy exprSimProps exprSimStorageCopy fragExec fragExecMem exprLoweringProps loweringPosts
  bodyPtrDefs loweringStateRelDefs ptrDiscipline context compileEnv
  venomMemDefs venomExecSemantics venomInst venomState valueEncodingDefs
  vfmConstants arithmetic relation rich_list list words finite_map pred_set

Theorem create_blueprint_raw_bytes_store_arrival_mods:
  compile_store_memory ce (Var src) (Var p) ty ty su = ((),cs) /\
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv (BytesV bytes) /\ val_wf tv (BytesV bytes) /\
  N = type_memory_size tv /\ type_memory_bytes ce ty = N /\ N + 64 < dimword (:256) /\
  is_bytestring_type phys /\ evaluate_type (get_tenv cx) phys = SOME pv /\
  value_has_type pv (BytesV bytes) /\
  m = val_store_size pv (BytesV bytes) /\ m <= N /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
     val_in_memory pv (BytesV bytes) (w2n sw) mem) /\
  lookup_var src z = SOME sw /\ lookup_var p z = SOME dw /\
  not_fresh_at su src /\ not_fresh_at su p /\
  ptr_covers G tn src z m /\ w2n sw + m <= z.vs_alloca_next /\
  ptr_covers G tn p z N /\ w2n dw + N <= z.vs_alloca_next /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,N) /\
  sa.cs_next_id <= inst.inst_id /\ sa.cs_next_var <= su.cs_next_var /\
  (!name b len. local_region ce ee.scopes z name b len ==>
    w2n dw + N <= b \/ b + len <= w2n dw) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
    w2n dw + N <= b \/ b + len <= w2n dw) /\
  fn_has_code su cs func /\ fn_inst_ids_distinct func /\
  ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  local_ptrs_reserved ce su /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at su x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at su x) /\
  return_buf_frame d ce su z /\
  (!x. old = Var x ==> not_fresh_at su x) /\ eval_operand old z = SOME ow /\
  HP H0 /\ (!H. HP H ==> stmt_state_rel H ctx func ce cx ee z /\
                         immutable_frame_mods func ce cx ee z /\
                         ghost_inv_at_mods (DF H) lo d ce cx ee G tn z) /\
  wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?t Gt tt.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      su.cs_next_id <= i.inst_id /\ i.inst_id < cs.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) z t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gt,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = cs.cs_current_bb /\
    t.vs_inst_idx = LENGTH cs.cs_current_insts /\
    val_in_memory tv (BytesV bytes) (w2n dw) t.vs_memory /\
    lookup_var p t = SOME dw /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,N) /\
    ptr_covers Gt tt p t N /\ not_fresh_at cs p /\
    eval_operand old t = SOME ow /\ (!x. old = Var x ==> not_fresh_at cs x) /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    return_buf_frame d ce cs t /\
    (!H. HP H ==> stmt_state_rel H ctx func ce cx ee t /\
                  immutable_frame_mods func ce cx ee t /\
                  ghost_inv_at_mods (DF H) lo d ce cx ee Gt tt t) /\
    wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gt tt
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_bytestring (Var src) (Var p) su = ((),cs)` by
    fs[compile_store_memory_def,is_bytestring_word_type] >>
  `m = 32 + 32 * word_size (LENGTH bytes) /\
   mload (w2n sw) z = n2w (LENGTH bytes) /\
   (!i. w2n sw <= i /\ i < w2n sw + 32 ==> i NOTIN tn.t_mem)` by
    metis_tac[ctor_store_byte_header] >>
  qpat_x_assum `m = val_store_size _ _` kall_tac >>
  `m < dimword (:256) /\ LENGTH bytes + 31 < dimword (:256) /\
    w2n dw + m <= z.vs_alloca_next` by suspend "bounds" >>
  `ptr_covers G tn p z m` by metis_tac[ptr_covers_mono] >>
  `run_inst_seq_mem_ok (emitted_insts su cs) z` by suspend "mem_ok" >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                        d_imm := K {}; d_ret := K {}|>` >>
  drule logBytesSeqPtrTheory.compile_store_bytestring_seq_ptr >>
  disch_then (drule_at (Pat `mload _ _ = _`)) >>
  simp[GSYM word_size_def] >>
  disch_then (qspecl_then [`tn`,`func`,`ctx`,`PG`,`G`,`D0`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq _ _ = OK r` >>
  qpat_x_assum `r.vs_memory = (mcopy _ _ _ _).vs_memory` kall_tac >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + N) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     (impl_tac >- (fs[] >> decide_tac)) >> simp[]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `!H. HP H ==> _` (drule_then strip_assume_tac) >>
     fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH cs.cs_current_insts` >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
    su.cs_next_id <= i.inst_id /\ i.inst_id < cs.cs_next_id /\
    i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) z t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gf,tnf)) /\
    cs.cs_current_bb = su.cs_current_bb /\ su.cs_next_var <= cs.cs_next_var /\
    cs.cs_current_insts = su.cs_current_insts ++ emitted_insts su cs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts su cs)` by
    suspend "band" >>
  `val_in_memory tv (BytesV bytes) (w2n sw) z.vs_memory` by suspend "transfer" >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `eval_operand (Var src) z = SOME sw` by simp[eval_operand_def] >>
  `!x. Var src = Var x ==> not_fresh_at su x` by simp[] >>
  `if is_word_type ty then sw = typed_val_to_w256 tv (BytesV bytes)
   else val_in_memory tv (BytesV bytes) (w2n sw) z.vs_memory` by simp[] >>
  `FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
   type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256)` by fs[] >>
  drule_all materialize_store_owned_run >>
  disch_then (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  `raw = r` by metis_tac[exec_result_11] >>
  pop_assum SUBST_ALL_TAC >>
  suspend "frame"
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[bounds]:
  `LENGTH bytes + 31 < ((LENGTH bytes + 31) DIV 32 + 1) * 32` by simp[GSYM DIV_LE_X] >>
  fs[word_size_def,Once MULT_COMM,RIGHT_ADD_DISTRIB] >> decide_tac
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[mem_ok]:
  drule compile_store_bytestring_body_mem_ok >>
  disch_then (drule_at (Pat `mload _ _ = _`)) >> simp[eval_operand_def] >> metis_tac[]
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[band]:
  drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  `cs.cs_next_id = su.cs_next_id + 6` by
    gvs[compile_store_bytestring_def,compile_bytestring_copy_len_def,
      emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
      comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
  `EVERY (\i. su.cs_next_id <= i.inst_id /\ i.inst_id < cs.cs_next_id)
       (emitted_insts su cs)` by simp[bytes_copy_insts_def,mk_inst_def] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post v. emitted_insts su cs = pre ++ i::post /\
       run_inst_seq pre z = OK v ==> dalloca_no_wrap i v)` by
    (`EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts su cs)` by
       simp[bytes_copy_insts_def, mk_inst_def] >>
     rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     fs[EVERY_MEM] >> first_x_assum irule >>
     qpat_x_assum `emitted_insts su cs = pre ++ i::post` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `emitted_insts su cs = bytes_copy_insts _ _ _ _` kall_tac >>
  drule bodyPtrIfExpBytesCountedTheory.compile_store_bytestring_code >>
  simp[EVERY_MEM] >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts su cs) = []` by
    (simp[FILTER_EQ_NIL,EVERY_MEM] >> metis_tac[]) >>
  `cs.cs_current_bb = su.cs_current_bb` by fs[same_blocks_def] >>
  `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts su cs) (DROP z.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def,IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `z.vs_inst_idx + LENGTH (emitted_insts su cs) = LENGTH cs.cs_current_insts` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts su cs)` by (simp[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- (drule_all ctor_straight_band_run >> simp[Abbr `t`]) >>
  conj_tac
  >- (gen_tac >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts su cs) z Gf tnf` by
        (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D0` >> simp[Abbr `D0`]) >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[Abbr `t`]) >>
  simp[] >> metis_tac[]
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[transfer]:
  irule bytestring_val_in_memory_transfer >> simp[] >>
  qexistsl_tac [`phys`,`ty`,`get_tenv cx`,`pv`] >> simp[] >>
  qpat_assum `!mem. mem_agree_outside tn.t_mem _ mem ==> _` irule >>
  simp[mem_agree_outside_def]
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[frame]:
  `!off len. off + len <= w2n dw \/ w2n dw + N <= off ==>
    mem_bytes_at off len r.vs_memory = mem_bytes_at off len z.vs_memory` by
    (rpt strip_tac >> qpat_assum `!off len. _ ==> mem_bytes_at off len r.vs_memory = _` irule >>
     metis_tac[]) >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_inst_idx = LENGTH cs.cs_current_insts /\
   t.vs_current_bb = cs.cs_current_bb /\ t.vs_memory = r.vs_memory /\
   t.vs_labels = z.vs_labels /\ t.vs_call_ctx = z.vs_call_ctx /\ t.vs_accounts = z.vs_accounts /\
   t.vs_transient = z.vs_transient /\ t.vs_immutables = z.vs_immutables /\
   t.vs_data_section = z.vs_data_section /\ copy_static t = copy_static z /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (simp[Abbr `t`] >>
     qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = z` mp_tac >>
     fs[venom_state_component_equality,copy_static_def,allocas_below_fmp_def] >> metis_tac[]) >>
  `!x. not_fresh_at su x ==>
       lookup_var x t = lookup_var x z /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)` by fs[Abbr `t`,lookup_var_def] >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  suspend "finish"
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[finish]:
  `alloca_inv z` by
    (qpat_assum `!H. HP H ==> _` (drule_then strip_assume_tac) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!off len. off + len <= w2n dw \/ w2n dw + N <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len z.vs_memory` by
    (qpat_assum `t.vs_memory = r.vs_memory` (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at su x ==> not_fresh_at cs x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var p t = SOME dw /\ ptr_covers Gf tnf p t N` by
    (simp[] >> irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`z`,`tn`] >> gvs[]) >>
  `eval_operand old t = SOME ow` by
    (Cases_on `old` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `alloca_history func t` by
    (simp[Abbr `t`] >> drule_all emitted_alloca_history >> simp[]) >>
  `return_buf_frame d ce cs t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`z`,`su`] >> simp[]) >>
  `wb_frame ce es ee sa s0 t` by
    (irule materialize_fresh_store_frame >>
     qexistsl_tac [`inst.inst_id`,`w2n dw`,`z`,`N`] >>
     fs[alloca_inv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at cs p /\ (!x. old = Var x ==> not_fresh_at cs x)` by metis_tac[] >>
  `ptr_covers Gf tnf p t (type_memory_size tv)` by metis_tac[] >>
  asm_rewrite_tac[] >> conj_tac >- suspend "horizon" >>
  suspend "kept"
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[horizon]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. HP H ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule copy_buffer_state_rel_frame >>
      qexistsl_tac [`w2n dw`,`inst`,`z`,`su`,`N`] >> simp[] >>
      gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "immutables" >>
  suspend "ghost"
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[immutables]:
  fs[bodyFullPostsModsTheory.immutable_frame_mods_def] >>
  conj_tac
  >- (fs[bodyInvSplitTheory.immutables_rel_mods_def] >>
      rpt gen_tac >> strip_tac >> irule loweringSliceTheory.immutables_rel_mem_agree >>
      qexists_tac `z` >> simp[] >>
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
  irule immutable_alloca_sep_fields >> qexistsl_tac [`z`,`ee`] >> simp[] >>
  simp[local_region_def] >> metis_tac[local_ptrs_reserved_def]
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[ghost]:
  qabbrev_tac `writes = {i | w2n dw <= i /\ i < w2n dw + N}` >>
  `lo <= w2n dw /\ allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 z.vs_memory /\
           (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >>
         fs[Abbr `writes`] >> decide_tac) >>
     qpat_assum `!i. ~(w2n dw <= i /\ i < w2n dw + N) ==> _` irule >>
     fs[Abbr `writes`]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo z.vs_memory` by simp[] >>
  `!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> `i NOTIN writes` by (simp[Abbr `writes`] >> decide_tac) >>
     metis_tac[]) >>
  `!p sz. not_fresh_at su p /\ ptr_covers G tn p z sz ==>
    ptr_covers Gf tnf p t sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`z`,`tn`] >> simp[] >> metis_tac[]) >>
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

Resume create_blueprint_raw_bytes_store_arrival_mods[ghost_locals]:
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var px) sz)` >>
  `not_fresh_at su px` by
    (qpat_assum `local_ptrs_reserved ce su` (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     strip_tac >> qpat_assum `!n1 n2 p sz1 sz2. _ ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1 o SPEC_ALL))) >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x t = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers G tn p z sz /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var px z = SOME w` by fs[] >>
  `local_region ce ee.scopes z name (w2n w) sz` by
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
     qpat_assum `!name b len. local_region ce ee.scopes z name b len ==> _`
       (drule_then mp_tac) >>
     simp[Abbr `writes`] >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`z.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tnf.t_mem`,`writes`] >>
  simp[]
QED

Resume create_blueprint_raw_bytes_store_arrival_mods[kept]:
  rewrite_tac[ghost_kept_at_def,GSYM ghost_kept_def] >>
  irule ghost_kept_exterior_frame >>
  qexistsl_tac [`G`,`{i | w2n dw <= i /\ i < w2n dw + N}`,`tn`] >>
  `ghost_kept ce es sa G0 tn0 s0 G tn` by
    (PURE_REWRITE_TAC [ghost_kept_def,GSYM ghost_kept_at_def] >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name b len. local_region ce es.scopes s0 name b len ==> _`
        (drule_then strip_assume_tac) >> simp[] >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `FLOOKUP z.vs_allocas aid = SOME (off,sz)` by fs[wb_frame_def] >>
      `allocas_non_overlapping z` by fs[alloca_inv_def] >>
      `off + sz <= w2n dw \/ w2n dw + N <= off` by
        (qpat_assum `allocas_non_overlapping z`
           (irule o REWRITE_RULE [allocas_non_overlapping_def]) >>
         qexistsl_tac [`aid`,`inst.inst_id`] >> simp[] >> decide_tac) >>
      simp[] >> decide_tac) >>
  gen_tac >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
  qpat_assum `!i. ~(w2n dw <= i /\ i < w2n dw + N) ==> _`
    (qspec_then `i` mp_tac) >> simp_tac (srw_ss()) [] >> metis_tac[]
QED

Finalise create_blueprint_raw_bytes_store_arrival_mods
