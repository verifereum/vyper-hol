Theory extRetRawStagePtr
Ancestors
  normalizationAllocationPathPtr storageNormalizationOwnershipPtr
  logAllocFramePtr extRetNormalizeBytesChildPtr abiBuiltinAllocation
  valueTypingMemoryProps logDataStorePtr ghostPcTransportPtr
  exprSimAlloc exprLoweringProps bodyPtrDefs loweringPosts loweringHalt
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  venomState venomInst venomExecSemantics ptrDiscipline fragGasSeqPtr
  finite_map words arithmetic rich_list list fragExec fragGasPathPtr
  bodyPtrIfExpStoreContract bodyPtrBopTypedBytes valueEncoding
  valueEncodingProofs ptrCoverage annAssignPtrBytestring valueCopyBytes vyperTyping assignTuplePtrLocalCompat

Theorem raw_bytes_allocate_source_ptr[local]:
  compile_alloc_buffer cap sm = (buf,sn) /\ fn_has_code sm sn func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ cap < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm src /\
  expr_val_at ce cx vty se sm es (BytesV bs) (Var src) s /\
  evaluate_type (get_tenv cx) vty = SOME stv /\
  value_has_type stv (BytesV bs) /\
  ptr_val_ok cx vty (BytesV bs) (Var src) G tn s /\
  stor_taint_ok cx tn s ==>
  ?u dst b H tm.
    buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u) /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~u.vs_halted /\
    lookup_var dst u = SOME (n2w b) /\ ptr_covers H tm dst u cap /\
    b+cap < dimword(:256) /\ not_fresh_at sn dst /\ not_fresh_at sn src /\
    ptr_val_ok cx vty (BytesV bs) (Var src) H tm u /\
    lookup_var src u = lookup_var src s /\ stor_taint_ok cx tm u
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[] >>
  `src <> STRING #"%" (toString sm.cs_next_var)` by
    (strip_tac >> gvs[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `buf.buf_size < dimword(:256)` by decide_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst sm.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
      [STRING #"%" (toString sm.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all normalization_alloca_checked_endpoint >>
  disch_then (qspecl_then [`D`,`PG`,`G`,`tn`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm _` >>
  `ptr_val_ok cx vty (BytesV bs) (Var src) H tm t` by
    (unabbrev_all_tac >> irule logAllocFramePtrTheory.alloca_step_ptr_val_ok >>
     simp[] >> conj_tac >- metis_tac[value_has_type_memory_wf] >>
     qexistsl_tac [`ce`,`ctx`,`es`,`func`,`se`,`sm`] >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
          AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def]) >>
  `stor_taint_ok cx tm t` by
    (unabbrev_all_tac >>
     drule_all normalization_alloca_storage_observations >> strip_tac >>
     gvs[normalization_alloca_key_taints, stor_taint_ok_def]) >>
  qexistsl_tac [`t with vs_inst_idx := SUC s.vs_inst_idx`, `w2n w`,`H`,`tm`] >>
  gvs[ptr_val_ok_inst_idx, ptr_covers_inst_idx, lookup_var_def,
       eval_operand_def, stor_taint_ok_def, ADD1]
QED

Theorem raw_bytes_stage_counted_ptr:
  compile_alloc_buffer (type_memory_bytes ce dty) sm = (buf,sn) /\
  compile_store_memory_typed ce buf.buf_operand dty (Var src) sty sn = ((),sp) /\
  fn_has_code sm sn func /\ fn_has_code sn sp func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ not_fresh_at sm src /\
  expr_val_at ce cx sty se sm es (BytesV bs) (Var src) s /\
  lookup_var src s = SOME a /\
  ptr_val_ok cx sty (BytesV bs) (Var src) G tn s /\ stor_taint_ok cx tn s /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv (BytesV bs) /\ value_has_type dtv (BytesV bs) /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword(:256) /\
  LENGTH bs + 31 < dimword(:256) /\
  32 + 32 * ((LENGTH bs + 31) DIV 32) < dimword(:256) ==>
  ?u dst b H tm.
    buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u) /\
    u.vs_current_bb = sp.cs_current_bb /\
    u.vs_inst_idx = LENGTH sp.cs_current_insts /\ ~u.vs_halted /\
    lookup_var dst u = SOME (n2w b) /\
    ptr_covers H tm dst u (type_memory_size dtv) /\
    b + type_memory_size dtv < dimword(:256) /\
    (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
      val_in_memory dtv (BytesV bs) b m) /\ stor_taint_ok cx tm u
Proof
  strip_tac >>
  `~is_word_type sty /\ ~is_word_type dty` by
    metis_tac[bop_machine_word_not_bytestring] >>
  `type_memory_bytes ce dty < dimword(:256)` by simp[] >>
  drule_all raw_bytes_allocate_source_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `compile_store_memory_typed ce (Var dst) dty (Var src) sty =
     compile_store_memory ce (Var src) (Var dst) dty sty` by
    simp[Once compile_store_memory_typed_def,
         compile_store_memory_bytestring_compat_ptr] >>
  `compile_store_memory ce (Var src) (Var dst) dty sty sn = ((),sp)` by
    metis_tac[] >>
  `compile_store_bytestring (Var src) (Var dst) sn = ((),sp)` by
    metis_tac[compile_store_memory_bytestring_compat_ptr] >>
  `lookup_var src u = SOME a` by metis_tac[] >>
  `(!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
      val_in_memory stv (BytesV bs) (w2n a) m)` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ u` mp_tac >>
     simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  `val_footprint stv (BytesV bs) <> 0` by
    (qspecl_then [`get_tenv cx`,`sty`,`stv`] mp_tac bytestring_type_value >>
     simp[] >> strip_tac >>
     gvs[value_has_type_def, val_footprint_def]) >>
  `ptr_covers H tm src u (val_store_size stv (BytesV bs))` by
    (qpat_assum `ptr_val_ok _ _ _ _ H tm u`
       (mp_then Any mp_tac ptr_val_ok_store_read_covers) >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `ptr_covers H tm dst u (type_memory_size dtv)` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `ptr_covers H tm dst u cap` >>
  qabbrev_tac `n = 32 + 32 * ((LENGTH bs + 31) DIV 32)` >>
  `n <= type_memory_size dtv /\
   ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG H tm u 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sp.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sp.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n (n2w b : bytes32)) (w2n a) n u).vs_memory /\
    (sf with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
               vs_inst_idx := u.vs_inst_idx|>) = u /\
    tnf.t_stor = tm.t_stor /\ tnf.t_trans = tm.t_trans /\
    tnf.t_imm = tm.t_imm /\
    (!i. ~(w2n (n2w b : bytes32) <= i /\
            i < w2n (n2w b : bytes32)+type_memory_size dtv) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 u.vs_memory /\
      (i IN tnf.t_mem <=> i IN tm.t_mem)) /\
    (!i. i < n ==> (w2n (n2w b : bytes32)+i IN tnf.t_mem <=> w2n a+i IN tm.t_mem)) /\
    (!i. ~(w2n (n2w b : bytes32) <= i /\ i < w2n (n2w b : bytes32)+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 u.vs_memory /\
      (i IN tnf.t_mem <=> i IN tm.t_mem)) /\
    (!p. not_fresh_at sn p ==>
      lookup_var p sf = lookup_var p u /\ FLOOKUP Gf p = FLOOKUP H p /\
      op_taint tnf (Var p) = op_taint tm (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dtv (BytesV bs) (w2n (n2w b : bytes32)) m) /\
    (!ft fv p. val_wf ft fv /\
      (!i. p <= i /\ i < p + val_footprint ft fv ==>
        ~(w2n (n2w b : bytes32) <= i /\ i < w2n (n2w b : bytes32)+type_memory_size dtv)) /\
      (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)` by
    (irule normalize_bytes_child_counted_ptr >>
     simp[] >> conj_tac
     >- simp[Abbr `n`] >>
     qexistsl_tac [`cx`,`dst`,`dty`,`src`,`stv`,`sty`] >>
     simp[Abbr `cap`]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `lookup_var dst sf = SOME (n2w b)` by metis_tac[] >>
  `ptr_covers Gf tnf dst sf cap` by
    (irule annassign_ptr_covers_frame_ptr >> metis_tac[]) >>
  `b < dimword(:256)` by decide_tac >>
  `stor_taint_ok cx tnf sf` by
    (qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _;
       vs_inst_idx := _|>) = u` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     gvs[stor_taint_ok_def]) >>
  qexistsl_tac [`sf`,`dst`,`b`,`Gf`,`tnf`] >> gvs[]
QED
