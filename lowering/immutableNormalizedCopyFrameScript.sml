(* Operational boundaries for typed normalization and immutable copying. *)
Theory immutableNormalizedCopyFrame
Ancestors
  immutableNormalizeMem immutableAssignFixedMem immutableFixedCopyTransportMem
  immutableDeployAssignBytes stmtLowering compileEnv context
  immutableFixedCopyMem fragExec loweringSlice exprLoweringProps localPtrsProps valueEncodingProps
  venomState venomExecSemantics loweringStateRelDefs finite_map words arithmetic list pair

Theorem immutable_normalized_compiler_parts:
  compile_assign_value ce dst LocCode src F sl dty sty di
    (type_memory_bytes ce dty) sm = ((),sb) /\
  ce.ce_imm_alloca = SOME region /\ sty <> dty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_memory_bytes ce dty = sz /\ 0 < sz /\ sz MOD 32 = 0 ==>
  ?buf mid sn n.
    compile_alloc_buffer sz sm = (buf,mid) /\
    compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
    compile_imm_store_words (SOME region) buf.buf_operand dst n 0 sn = ((),sb) /\
    sz = 32*n /\ 0 < n
Proof
  strip_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_store_memory_typed _ _ _ _ _ mid = ((),sn)` >>
  `?n. type_memory_bytes ce dty = 32*n /\ 0 < n` by
    (qexists_tac `type_memory_bytes ce dty DIV 32` >>
     mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[] >>
     disch_then (qspec_then `type_memory_bytes ce dty` mp_tac) >> simp[] >> decide_tac) >>
  `compile_imm_store_words (SOME region) buf.buf_operand dst n 0 sn = ((),sb)` by
    (Cases_on `n = 1`
     >- (gvs[] >> CONV_TAC (DEPTH_CONV numLib.num_CONV) >>
         simp[compile_imm_store_words_def, compile_lit_byte_offset_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
         pairarg_tac >> gvs[] >> pairarg_tac >> gvs[comp_bind_def]) >>
     `~(32*n <= 32) /\ (32*n+31) DIV 32 = n` by simp[] >> gvs[]) >>
  qexists_tac `n` >> simp[]
QED

Theorem immutable_normalized_code_windows:
  compile_alloc_buffer sz sm = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
  compile_imm_store_words (SOME region) buf.buf_operand dst n 0 sn = ((),sb) /\
  fn_has_code sm sb func /\
  (emitted_blocks sm sb <> [] ==> ?bb.
    lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  fn_has_code sm mid func /\ fn_has_code mid sn func /\ fn_has_code sn sb func /\
  sn.cs_current_bb = sb.cs_current_bb /\ emitted_blocks sn sb = [] /\
  (emitted_blocks mid sn <> [] ==> ?bb.
    lookup_block sn.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `cs_extends sm mid /\ cs_extends mid sn /\ cs_extends sn sb` by
    (conj_tac
     >- metis_tac[externalEntryShapeTheory.compile_alloc_buffer_labels, SND] >>
     conj_tac
     >- metis_tac[externalEntryShapeTheory.typed_memory_family_labels, SND] >>
     metis_tac[externalEntryShapeTheory.compile_imm_store_words_labels, SND]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sn func /\ fn_has_code sn sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sn.cs_current_bb = sb.cs_current_bb /\ emitted_blocks sn sb = []` by
    (drule immutable_fixed_words_code >> simp[same_blocks_def, emitted_blocks_def] >>
     strip_tac >> simp[]) >>
  simp[] >> strip_tac >>
  `emitted_blocks sm sb <> []` by
    (gvs[emitted_blocks_def, cs_extends_def] >>
     metis_tac[TAKE_EQ_NIL, LENGTH_APPEND]) >>
  metis_tac[]
QED

Theorem immutable_normalized_allocation_extension:
  exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sm.cs_next_var)]) s (n2w sz : bytes32) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
  sz < dimword (:256) /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,sz) /\
  off + sz <= s.vs_alloca_next /\
  (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
    regions_disjoint off sz q k) ==>
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
    FLOOKUP u.vs_allocas aid = SOME (q,k)) /\
  (!aid q k. FLOOKUP u.vs_allocas aid = SOME (q,k) /\
    FLOOKUP s.vs_allocas aid = NONE ==>
    aid = sm.cs_next_id /\ q = s.vs_alloca_next /\ k = sz) /\
  regions_disjoint off sz b sz
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
    venomStateTheory.update_var_def, AllCaseEqs()] >> strip_tac >>
  gvs[venomStateTheory.venom_state_component_equality, FLOOKUP_UPDATE] >>
  qpat_x_assum `_ = u.vs_allocas` (assume_tac o SYM) >>
  gvs[FLOOKUP_UPDATE, regions_disjoint_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[ADD_COMM]
QED

Theorem immutable_normalized_copy_freshness:
  compile_alloc_buffer sz sm = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
  (!x. dst = Var x \/ region = Var x ==> not_fresh_at sm x) ==>
  sm.cs_next_var <= sn.cs_next_var /\
  (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
  (!x. dst = Var x ==> not_fresh_at sn x) /\
  (!x. region = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `sm.cs_next_var <= sn.cs_next_var /\ mid.cs_next_var <= sn.cs_next_var` by
    (drule typedCopyVarFlowTheory.compile_store_memory_typed_next_var >>
     qpat_assum `mid.cs_next_var = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `mid` >> simp[]) >>
  conj_tac >> rpt strip_tac >>
  irule loweringShapeDefsTheory.not_fresh_at_mono >>
  qexists_tac `sm` >> simp[]
QED

Theorem immutable_normalized_copy_operands:
  (r with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := mid.cs_current_bb; vs_inst_idx := LENGTH mid.cs_current_insts;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sm.cs_next_var)]) s (n2w sz : bytes32) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
  eval_operand dst s = SOME d /\ eval_operand region s = SOME rw /\
  (!x. dst = Var x \/ region = Var x ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> lookup_var x r = lookup_var x s) ==>
  r.vs_labels = s.vs_labels /\
  eval_operand dst r = SOME d /\ eval_operand region r = SOME rw
Proof
  strip_tac >>
  `r.vs_labels = s.vs_labels` by
    (qpat_assum `_ = u` (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >>
     qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
       venomStateTheory.update_var_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[venom_state_component_equality]) >>
  conj_tac >- simp[] >>
  qpat_assum `eval_operand dst s = _` mp_tac >>
  qpat_assum `eval_operand region s = _` mp_tac >>
  qpat_assum `!x. dst = Var x \/ _ ==> _` mp_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> lookup_var x r = _` mp_tac >>
  qpat_assum `r.vs_labels = s.vs_labels` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  Cases_on `dst` >> Cases_on `region` >>
  simp[eval_operand_def] >> metis_tac[]
QED

Theorem immutable_normalized_copy_terminal[local]:
  t = r with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
    vs_immutables := t.vs_immutables|> /\
  t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
  mem_cont_sim ctx func r (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x r) /\
  t.vs_memory = (mcopy off b (32*n) r).vs_memory /\
  mem_bytes_at off (32*n) t.vs_memory = mem_bytes_at b (32*n) r.vs_memory /\
  (!q k. q+k <= off \/ off+32*n <= q ==>
    mem_bytes_at q k t.vs_memory = mem_bytes_at q k r.vs_memory) /\
  type_memory_size dtv = 32*n /\ immutable_value_admissible dtv v /\
  val_in_memory dtv v b r.vs_memory /\
  alloca_inv r /\ alloca_room ctx func r /\
  ~r.vs_halted /\ r.vs_current_bb = sb.cs_current_bb ==>
  ?z. mem_cont_sim ctx func r z /\
    z.vs_allocas = r.vs_allocas /\ z.vs_alloca_next = r.vs_alloca_next /\
    alloca_inv z /\ alloca_room ctx func z /\
    val_in_memory dtv v off z.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) z.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
      mem_bytes_at q k z.vs_memory = mem_bytes_at q k r.vs_memory) /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x r) /\
    z = r with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
      vs_immutables := z.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `val_wf dtv v` by metis_tac[immutable_admissible_val_wf] >>
  `val_in_memory dtv v off (mcopy off b (32*n) r).vs_memory` by
    (qpat_assum `val_in_memory dtv v b _` mp_tac >>
     qpat_assum `val_wf dtv v` mp_tac >>
     qpat_assum `type_memory_size dtv = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule mcopy_establishes_val_in_memory >> simp[]) >>
  `immutable_value_bytes_rel dtv v (mem_bytes_at b (32*n) r.vs_memory)` by
    metis_tac[immutable_memory_bytes] >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `t = _` (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb)`) >>
     qpat_assum `~r.vs_halted` mp_tac >>
     qpat_assum `r.vs_current_bb = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `alloca_inv t /\ alloca_room ctx func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `alloca_inv r` mp_tac >>
     qpat_assum `alloca_room ctx func r` mp_tac >>
     qpat_assum `t.vs_allocas = _` mp_tac >>
     qpat_assum `t.vs_alloca_next = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 4 strip_tac >>
     conj_tac >- metis_tac[alloca_inv_fields] >>
     irule alloca_room_fields >> qexists_tac `r` >> simp[]) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts =
    r with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_immutables := t.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qpat_assum `t = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qpat_x_assum `t = _` kall_tac >>
  simp[NoAsms] >> asm_rewrite_tac[lookup_var_def] >>
  pure_rewrite_tac[mcopy_mem_bytes_at_same] >>
  rpt conj_tac
  >- asm_rewrite_tac[]
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac)
  >- (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  simp[NoAsms, venom_state_component_equality]
QED

Theorem immutable_normalized_copy_mem_endpoint:
  compile_imm_store_words (SOME region) buf.buf_operand dst n 0 sn = ((),sb) /\
  fn_has_code sn sb func /\ sn.cs_current_bb = sb.cs_current_bb /\
  eval_operand buf.buf_operand r = SOME (n2w b) /\
  eval_operand dst r = SOME (n2w off) /\ eval_operand region r = SOME 0w /\
  (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
  (!x. dst = Var x ==> not_fresh_at sn x) /\
  (!x. region = Var x ==> not_fresh_at sn x) /\ 0 < n /\
  type_memory_size dtv = 32*n /\ immutable_value_admissible dtv v /\
  val_in_memory dtv v b r.vs_memory /\
  b+32*n <= r.vs_alloca_next /\ off+32*n <= r.vs_alloca_next /\
  b+32*n < dimword (:256) /\ off+32*n < dimword (:256) /\
  regions_disjoint off (32*n) b (32*n) /\
  alloca_inv r /\ alloca_room ctx func r /\
  ~r.vs_halted /\ r.vs_current_bb = sb.cs_current_bb /\
  r.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?z. mem_cont_sim ctx func r z /\
    z.vs_allocas = r.vs_allocas /\ z.vs_alloca_next = r.vs_alloca_next /\
    alloca_inv z /\ alloca_room ctx func z /\
    val_in_memory dtv v off z.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) z.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
      mem_bytes_at q k z.vs_memory = mem_bytes_at q k r.vs_memory) /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x r) /\
    z = r with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
      vs_immutables := z.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `b+0+32*n <= r.vs_alloca_next /\ off+0+32*n <= r.vs_alloca_next /\
   b+0+32*n < dimword (:256) /\ off+0+32*n < dimword (:256) /\
   (off+0+32*n <= b+0 \/ b+0+32*n <= off+0)` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  drule immutable_fixed_copy_operand_mem_endpoint >>
  disch_then (qspecl_then [`r`,`func`,`ctx`,`off`,`b`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
  strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [ADD_0]) >>
  drule_all immutable_normalized_copy_terminal >>
  disch_then ACCEPT_TAC
QED

Theorem immutable_normalized_copy_bounds:
  sz = 32*n /\ sz' = sz /\
  b+sz <= r.vs_alloca_next /\ off+sz <= s.vs_alloca_next /\
  b+sz < dimword (:256) /\ off+sz < dimword (:256) /\
  s.vs_alloca_next <= u.vs_alloca_next /\ r.vs_alloca_next = u.vs_alloca_next /\
  regions_disjoint off sz' b sz' ==>
  b+32*n <= r.vs_alloca_next /\ off+32*n <= r.vs_alloca_next /\
  b+32*n < dimword (:256) /\ off+32*n < dimword (:256) /\
  regions_disjoint off (32*n) b (32*n) /\ regions_disjoint off sz b sz
Proof
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem immutable_normalized_allocation_transport:
  r.vs_allocas = u.vs_allocas /\ r.vs_alloca_next = u.vs_alloca_next /\
  t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
  sz' = sz /\ s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
    FLOOKUP u.vs_allocas aid = SOME (q,k)) /\
  (!aid q k. FLOOKUP u.vs_allocas aid = SOME (q,k) /\
    FLOOKUP s.vs_allocas aid = NONE ==>
    aid = site /\ q = s.vs_alloca_next /\ k = sz') ==>
  (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
    FLOOKUP t.vs_allocas aid = SOME (q,k)) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid q k. FLOOKUP t.vs_allocas aid = SOME (q,k) /\
    FLOOKUP s.vs_allocas aid = NONE ==>
    aid = site /\ q = s.vs_alloca_next /\ k = sz)
Proof
  strip_tac >> qpat_x_assum `sz' = sz` SUBST_ALL_TAC >> asm_rewrite_tac[]
QED
