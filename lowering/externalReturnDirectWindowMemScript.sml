(* Allocation provenance for a direct external return encoder. *)
Theory externalReturnDirectWindowMem
Ancestors
  externalReturnDirectSource externalReturnDestinationMem
  externalReturnEncoderSites externalReturnSourceWindow
  registeredAllocationWindow abiEncoderWindowContract abiEncoderProps
  exprLoweringProps localPtrsProps compileEnv venomMemDefs finite_map pred_set
  actualAllocExec allocaSiteResource externalReturnNormalizeRun loweringHalt exprSimOperands
  venomExecSemantics venomState venomInst words

Theorem direct_encoder_scratch_source:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty va vb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\ cap <= val_footprint tv v /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce st /\
  vb.cs_next_id <= st.cs_next_id ==>
  !inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (w2n p,cap) (b,sz)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all encoder_function_alloca_nonlocal >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
      simp[stmt_state_rel_def] >> strip_tac >>
      first_x_assum drule_all >> simp[wordsTheory.dimword_def]) >>
  `vb.cs_next_id <= inst.inst_id` by fs[frag_ids_def] >>
  drule_all expression_source_window_disjoint >> simp[]
QED

Theorem direct_encoder_scratch_after_destination:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty va vb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\ cap <= val_footprint tv v /\
  compile_alloc_buffer n sa = (buf,st) /\
  compile_abi_encode_to_buf buf.buf_operand src ei st = (out,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce st /\
  vb.cs_next_id <= st.cs_next_id /\
  alloca_inv u /\ FLOOKUP u.vs_allocas sa.cs_next_id = SOME (d,n) /\ k <= n /\
  (!id. id <> sa.cs_next_id ==> FLOOKUP u.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
  !inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (w2n p,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,k) (b,sz)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_id NOTIN frag_ids st en` by
    metis_tac[allocated_encoder_site_excluded] >>
  `inst.inst_id <> sa.cs_next_id` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (w2n p,cap) (b,sz)` by
    (drule_all direct_encoder_scratch_source >> simp[]) >>
  simp[] >>
  drule_all registered_allocation_subwindow_disjoint >> simp[]
QED

Theorem direct_encoder_window_from_alloca:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty va vb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\ cap <= val_footprint tv v /\
  w2n p + cap <= s.vs_alloca_next /\
  abi_encoder_window_input ei at av (w2n p) cap s.vs_memory /\
  abi_encoder_admissible ei /\ LENGTH (enc at av) <= n /\ n < dimword (:256) /\
  compile_alloc_buffer n sa = (buf,st) /\ fn_has_code sa st func /\
  compile_abi_encode_to_buf buf.buf_operand src ei st = (out,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  vb.cs_next_id <= sa.cs_next_id /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s (n2w n : bytes32) = OK t /\
  alloca_room ctx func t /\ alloca_inv t /\
  lookup_var (STRING #"%" (toString sa.cs_next_var)) t = SOME (n2w d) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (d,n) /\
  s.vs_alloca_next <= t.vs_alloca_next /\ d+n <= t.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH st.cs_current_insts) /\
  abi_encoder_window_pre ctx func st en buf.buf_operand src ei at av
    (w2n p) cap d (t with vs_inst_idx := LENGTH st.cs_current_insts)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all normalize_alloc_mem_cont >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!id. id <> sa.cs_next_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, mk_inst_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]) >>
  `venomMemDefs$regions_disjoint (w2n p,cap) (d,n)` by suspend "protection" >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `src <> Var (STRING #"%" (toString sa.cs_next_var))` by metis_tac[] >>
  `!op. op <> Var (STRING #"%" (toString sa.cs_next_var)) ==>
     eval_operand op t = eval_operand op s` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) actual_literal_alloca_frame >>
     simp[mk_inst_def]) >>
  `t.vs_memory = s.vs_memory` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) actual_literal_alloca_frame >>
     simp[mk_inst_def]) >>
  `alloca_room ctx func (t with vs_inst_idx := LENGTH st.cs_current_insts)` by
    (irule alloca_room_fields >> qexists_tac `t` >> simp[]) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (w2n p,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)` by
    (`vb.cs_next_id <= st.cs_next_id` by decide_tac >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all direct_encoder_scratch_after_destination >> simp[]) >>
  suspend "assembly"
QED

Resume direct_encoder_window_from_alloca[protection]:
  drule_all actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `exec_alloca inst s _ = _` >>
  `MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit (n2w n)] /\ inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by
    simp[Abbr `inst`, mk_inst_def] >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     irule fresh_not_local_ptr >> metis_tac[]) >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n (n2w n : bytes32) /\
    venomMemDefs$regions_disjoint (w2n p,cap) (b,sz)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
         simp[stmt_state_rel_def] >> strip_tac >>
         first_x_assum drule_all >> simp[Abbr `inst`, mk_inst_def]) >>
     `vb.cs_next_id <= inst.inst_id` by simp[Abbr `inst`, mk_inst_def] >>
     drule_all expression_source_window_disjoint >> simp[]) >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (d,w2n (n2w n : bytes32))` by
    (simp_tac (srw_ss()) [Abbr `inst`, mk_inst_def] >>
     qpat_x_assum `FLOOKUP t.vs_allocas _ = _` mp_tac >>
     qpat_x_assum `n < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  drule_all alloca_site_execute_protected >> simp[]
QED

Resume direct_encoder_window_from_alloca[assembly]:
  `eval_operand src t = SOME p` by metis_tac[] >>
  `eval_operand buf.buf_operand t = SOME (n2w d)` by
    simp[eval_operand_def] >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at st x` by
    (qpat_x_assum `!x. src = Var x ==> _` mp_tac >>
     qpat_x_assum `buf.buf_operand = _` mp_tac >>
     qpat_x_assum `not_fresh_at st _` mp_tac >>
     qpat_x_assum `!y. not_fresh_at sa y ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!op. op <> _ ==> _` kall_tac >>
  qpat_x_assum `!id. id <> _ ==> _` kall_tac >>
  simp_tac (srw_ss()) [abi_encoder_window_pre_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
      qpat_x_assum `LENGTH (enc at av) <= n` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp_tac (std_ss) [venomMemDefsTheory.regions_disjoint_def,
        Excl "LENGTH_EQ_NUM_compute"] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `~(_ with vs_inst_idx := _).vs_halted` mp_tac >> simp_tac (srw_ss()) []) >>
  qpat_x_assum `(_ with vs_inst_idx := _).vs_current_bb = _` mp_tac >>
  simp_tac (srw_ss()) []
QED

Finalise direct_encoder_window_from_alloca

Theorem direct_encoder_allocate_window:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty va vb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\ cap <= val_footprint tv v /\
  w2n p + cap <= s.vs_alloca_next /\
  abi_encoder_window_input ei at av (w2n p) cap s.vs_memory /\
  abi_encoder_admissible ei /\ LENGTH (enc at av) <= n /\ n < dimword (:256) /\
  compile_alloc_buffer n sa = (buf,st) /\ fn_has_code sa st func /\
  compile_abi_encode_to_buf buf.buf_operand src ei st = (out,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  vb.cs_next_id <= sa.cs_next_id /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u d. mem_cont_sim ctx func s u /\
    abi_encoder_window_pre ctx func st en buf.buf_operand src ei at av
      (w2n p) cap d u
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by
    simp[Abbr `inst`, mk_inst_def] >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = w2n (n2w n : bytes32))` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def] >> rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  drule_all alloca_site_execute >> strip_tac >>
  `w2n (n2w n : bytes32) = n` by simp[] >>
  pop_assum SUBST_ALL_TAC >> unabbrev_all_tac >>
  qpat_x_assum `FLOOKUP t.vs_allocas _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [mk_inst_def]) >>
  drule_all direct_encoder_window_from_alloca >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
