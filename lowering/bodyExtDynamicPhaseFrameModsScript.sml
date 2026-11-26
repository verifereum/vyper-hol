(* Lift the measured two-write phase at its actual endpoint. The cursor
   belongs to the registered sites, not to the list of payload writes. *)
Theory bodyExtDynamicPhaseFrameMods
Ancestors
  bodyAbiEncodeRegisteredFrameMods abiEncodeValuesPhases
  exprSimAbiEncodeSiteResources abiEncoderProps abiEncoderWindowContract
  abiEncoderWindowPhase exprSimAbiEncodeExecFrame
  bodyFullPostsMods bodyFullShadowBodyInv loweringPosts loweringStateRelDefs
  bodyPtrDefs ptrDiscipline compileEnv freshWrites fragGasOriginPtr
  exprLowering fragExec venomState venomInst venomMemDefs vyperContext
  memoryReadProps stateRelProj finite_map pred_set list pair arithmetic

Theorem dynamic_registered_sites[local]:
  compile_abi_encode_to_buf dst src ei ready = (len,encoded) /\
  fn_has_code ready encoded func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce front /\ front.cs_next_var <= ready.cs_next_var /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = shared /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  MEM cursor (fn_insts func) /\ cursor.inst_opcode = ALLOCA /\
  cursor.inst_id = loc /\ cursor.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var ==>
  !aid. aid IN shared INSERT loc INSERT window_alloca_sites func (frag_ids ready encoded) ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[IN_INSERT,window_alloca_sites_def] >>
  gen_tac >> disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
  >- (qexistsl [`owner`,`root`] >> simp[]) >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (qexistsl [`cursor`,`cursor_var`] >> simp[]) >>
  rename1 `inst.inst_id = aid` >>
  `inst.inst_id IN frag_ids ready encoded` by simp[] >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
  drule_all (Q.INST [`obs` |-> `func`,`earlier` |-> `front`,
                     `scopes` |-> `ee.scopes`]
    abi_encode_compiled_scratch_site) >>
  disch_then (qspec_then `ee` strip_assume_tac) >>
  rename1 `inst.inst_outputs = [scratch]` >>
  qexistsl [`inst`,`scratch`] >> simp[]
QED

Theorem ext_dynamic_phase_frame_mods:
  window_phase ctx func ready en (loc INSERT window_alloca_sites func (frag_ids ready encoded))
    [(b+32+h,32);(b+32+off,LENGTH bytes)] z t /\
  abi_encode_exec_frame func z t /\
  compile_abi_encode_to_buf dst src ei ready = (len,encoded) /\
  fn_has_code ready encoded func /\ fn_inst_ids_distinct func /\
  front.cs_next_id <= shared /\ shared < loc /\ loc < ready.cs_next_id /\
  local_ptrs_reserved ce front /\ front.cs_next_var <= ready.cs_next_var /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = shared /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  MEM cursor (fn_insts func) /\ cursor.inst_opcode = ALLOCA /\
  cursor.inst_id = loc /\ cursor.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\
  FLOOKUP z.vs_allocas shared = SOME (b,cap) /\
  h+32 <= off /\ 32 <= cap /\ off+LENGTH bytes <= cap-32 /\
  alloca_history func z /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\
    immutable_frame_mods func ce cx ee z) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gf,tt)) /\
  (!x. not_fresh_at ready x ==>
    FLOOKUP Gf x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)) /\
  tt.t_stor = tz.t_stor /\ tt.t_trans = tz.t_trans /\ tt.t_imm = tz.t_imm /\
  (!i. (i < b+32+h \/ b+32+h+32 <= i) /\
    (i < b+32+off \/ b+32+off+LENGTH bytes <= i) /\
    (!aid p n. aid IN loc INSERT window_alloca_sites func (frag_ids ready encoded) /\
      FLOOKUP t.vs_allocas aid = SOME (p,n) ==> i < p \/ p+n <= i) ==>
    (i IN tt.t_mem <=> i IN tz.t_mem)) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tt t /\
    immutable_frame_mods func ce cx ee t) /\
  pure_frame ce func ee front z t /\ wb_frame ce ee ee front z t /\
  ghost_kept_at lo ce ee front Gz tz z Gf tt /\ alloca_history func t /\
  window_alloca_growth z t /\ alloca_inv t /\ alloca_room ctx func t /\
  z.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts /\ t.vs_labels = z.vs_labels /\
  (!aid row. FLOOKUP z.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  (!x. not_fresh_at ready x ==>
    (!w. lookup_var x z = SOME w ==> lookup_var x t = SOME w) /\
    FLOOKUP Gf x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)) /\
  (!op w. (!x. op = Var x ==> not_fresh_at ready x) /\ eval_operand op z = SOME w ==>
    eval_operand op t = SOME w) /\
  (!x w n. not_fresh_at ready x /\ eval_operand (Var x) z = SOME w /\
             ptr_covers Gz tz x z n ==> ptr_covers Gf tt x t n) /\
  (!aid p cap' q n. FLOOKUP z.vs_allocas aid = SOME (p,cap') /\
    (aid = shared \/ aid < front.cs_next_id) /\ p <= q /\ q+n <= p+cap' /\
    venomMemDefs$regions_disjoint (q,n) (b+32+h,32) /\
    venomMemDefs$regions_disjoint (q,n) (b+32+off,LENGTH bytes) ==>
    mem_bytes_at q n t.vs_memory = mem_bytes_at q n z.vs_memory /\
    (!i. q <= i /\ i < q+n /\ i IN tt.t_mem ==> i IN tz.t_mem)) /\
  read_memory (b+28) 4 t = read_memory (b+28) 4 z /\
  (!i. b+28 <= i /\ i < b+32 /\ i IN tt.t_mem ==> i IN tz.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ids = loc INSERT window_alloca_sites func (frag_ids ready encoded)` >>
  `!aid. aid IN ids ==> loc <= aid` by
    (simp[Abbr `ids`,IN_INSERT,window_alloca_sites_def,frag_ids_def] >>
     rpt strip_tac >> decide_tac) >>
  `!aid. aid IN ids ==> front.cs_next_id <= aid` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp_tac bool_ss [Abbr `ids`] >>
     mp_tac dynamic_registered_sites >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `EVERY (\(p,n). b <= p /\ p+n <= b+cap) [(b+32+h,32);(b+32+off,LENGTH bytes)]` by
    (simp[] >> decide_tac) >>
  `!i. EVERY (\(p,n). i < p \/ p+n <= i) [(b+32+h,32);(b+32+off,LENGTH bytes)] /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==> i < p \/ p+n <= i) /\
    i IN tt.t_mem ==> i IN tz.t_mem` by
    (simp_tac bool_ss [EVERY_DEF, pairTheory.UNCURRY, FST, SND] >>
     gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!i. _ ==> (i IN tt.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  drule_all abi_encode_registered_phase_frame_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_phase_labels >>
  suspend "observations"
QED

Resume ext_dynamic_phase_frame_mods[observations]:
  `alloca_inv z` by
    (qpat_assum `?H. valid_horizon _ _ H _` strip_assume_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!aid p cap' q n. FLOOKUP z.vs_allocas aid = SOME (p,cap') /\
    (aid = shared \/ aid < front.cs_next_id) /\ p <= q /\ q+n <= p+cap' /\
    venomMemDefs$regions_disjoint (q,n) (b+32+h,32) /\
    venomMemDefs$regions_disjoint (q,n) (b+32+off,LENGTH bytes) ==>
    mem_bytes_at q n t.vs_memory = mem_bytes_at q n z.vs_memory /\
    (!i. q <= i /\ i < q+n /\ i IN tt.t_mem ==> i IN tz.t_mem)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `aid NOTIN ids` by
       (strip_tac >> `loc <= aid` by simp[] >> `front.cs_next_id <= aid` by simp[] >>
        qpat_x_assum `aid = shared \/ _` strip_assume_tac >> decide_tac) >>
     `EVERY (\r. venomMemDefs$regions_disjoint (q,n) r)
       [(b+32+h,32);(b+32+off,LENGTH bytes)]` by simp[] >>
     drule_all_then (ACCEPT_TAC o CONJUNCT2) abi_encode_values_registered_window) >>
  `mem_bytes_at (b+28) 4 t.vs_memory = mem_bytes_at (b+28) 4 z.vs_memory /\
   (!i. b+28 <= i /\ i < b+32 /\ i IN tt.t_mem ==> i IN tz.t_mem)` by
    (qpat_assum `!aid p cap' q n. FLOOKUP z.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`shared`,`b`,`cap`,`b+28`,`4`] mp_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >>
     (impl_tac >- decide_tac) >> simp[]) >>
  asm_rewrite_tac[read_memory_eq_mem_bytes_at] >> conj_tac
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC window_phase_operand) >>
  rpt strip_tac >> drule_all abi_encode_values_pointer_frame >> simp[]
QED

Finalise ext_dynamic_phase_frame_mods
