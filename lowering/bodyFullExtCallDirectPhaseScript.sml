Theory bodyFullExtCallDirectPhase
Ancestors
  bodyFullExtCallDirectWindows bodyFullExtCallDirectFrame
  abiEncoderWindowPhase abiEncoderWindowContract exprSimAbiEncodeExecFrame exprLoweringProps
  abiEncoderRegisteredEffect exprSimAbiEncodeFrameTransfer abiDecodeStaticProps
  bodyFullAbiEncodeOriginFloor abiEncodeValuesPhases memoryReadProps
  loweringStateRelDefs loweringPosts
  vyperStorageFootprint bodyPtrDefs fragGasOriginPtr
  compileEnv ptrDiscipline venomState venomInst venomMemDefs
  exprSimWordArgs wordArgsPtr fragGasOriginPtrLoop
  finite_map pred_set list words arithmetic pair
Libs horizonTypeLib

(* The owner and the registered scratch allocations account for every
   encoder write, including writes above the initial allocation frontier. *)
Theorem abi_encode_registered_pure_frame[local]:
  abi_encoder_registered_effect ids outs u v /\
  FLOOKUP u.vs_allocas owner = SOME (b,cap) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  (!id. id IN owner INSERT ids ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = id /\ cut.cs_next_id <= id) /\
  (!name p n. local_region ce ee.scopes u name p n ==>
    mem_bytes_at p n v.vs_memory = mem_bytes_at p n u.vs_memory) ==>
  pure_frame ce func ee cut u v
Proof
  strip_tac >> rewrite_tac[pure_frame_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  rename1 `mem_bytes_at off len v.vs_memory = _` >>
  `!id p n. id IN owner INSERT ids /\ FLOOKUP v.vs_allocas id = SOME (p,n) ==>
    off+len <= p \/ p+n <= off` by
    (rpt strip_tac >>
     qpat_assum `!id. id IN owner INSERT ids ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!inst p n. _ ==> loweringStateRelDefs$regions_disjoint off len p n`
       (qspecl_then [`inst`,`p`,`n`] mp_tac) >>
     asm_simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `FLOOKUP v.vs_allocas owner = SOME (b,cap)` by metis_tac[abi_encoder_registered_effect_allocated] >>
  `off+len <= b \/ b+cap <= off` by metis_tac[IN_INSERT] >>
  `EVERY (\(p,n). off+len <= p \/ p+n <= off) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac) >>
  `!id p n. id IN ids /\ FLOOKUP v.vs_allocas id = SOME (p,n) ==>
    off+len <= p \/ p+n <= off` by metis_tac[IN_INSERT] >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  mp_tac (Q.INST [`s` |-> `u`,`t` |-> `v`,`lo` |-> `off`,`n` |-> `len`,
    `a` |-> `i`] abi_encode_registered_protected_byte) >>
  asm_rewrite_tac[]
QED

(* Pack the pure execution result at its actual cut, with one endpoint
   for every valid storage horizon. Delayed unwrap has the same frame. *)
Theorem extcall_direct_row_phase_pure:
  window_phase ctx func st en ids outs s t /\
  abi_encode_exec_frame func s t /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved ce front /\ front.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\ front.cs_next_id <= shared /\
  (!aid. aid IN ids ==> front.cs_next_id <= aid) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  pure_frame ce func ee front s t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G' tn' t) /\
  wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts /\
  (!x. not_fresh_at st x ==>
    (!w. lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ ghost_inv_at (DF H) lo d ce cx ee G' tn' t /\
    wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
    alloca_history func t /\ pure_frame ce func ee front s t` by
    (qx_gen_tac `hz` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (qspec_then `hz` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >>
     `allocas_from lo s /\ lo <= s.vs_alloca_next` by metis_tac[ghost_inv_at_def] >>
     qpat_assum `window_phase ctx func st en ids outs s t`
       (mp_then (Pos hd) (mp_tac o SPEC_ALL)
         (Q.INST [`p` |-> `b`,`cut` |-> `(front:compile_state).cs_next_id`,`H` |-> `hz`]
           extcall_direct_encode_windows)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     `pure_frame ce func ee front s t` by
       (`abi_encoder_registered_effect ids outs s t` by metis_tac[window_phase_effect] >>
        mp_tac (Q.INST [`u` |-> `s`, `v` |-> `t`, `owner` |-> `shared`,
          `cut` |-> `front`] abi_encode_registered_pure_frame) >>
        impl_tac >-
          (asm_rewrite_tac[] >> conj_tac
           >- (gen_tac >> disch_tac >>
               qpat_assum `!aid. aid IN shared INSERT ids ==> _`
                 (drule_then strip_assume_tac) >>
               qexists_tac `inst` >> fs[IN_INSERT] >> metis_tac[]) >>
           metis_tac[]) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s`
       (mp_then (Pos (el 3)) (mp_tac o SPEC_ALL)
         (Q.INST [`H` |-> `hz`,`cut` |-> `front`,
           `D` |-> `(DF:((bool # bytes32 # type_value) list # num list) -> dead) hz`]
           (SPEC_ALL extcall_direct_encode_phase_frame))) >>
     impl_tac >- (rpt conj_tac >>> NTH_GOAL (simp[]) 4 >> first_assum ACCEPT_TAC) >>
     strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  drule_then strip_assume_tac window_phase_control >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_alloca_growth_frontier >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
        (drule_then strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `window_alloca_growth s t`
        (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def])) >>
  metis_tac[window_phase_vars]
QED

Theorem extcall_direct_row_phase =
  let val premise = fst (dest_imp (concl extcall_direct_row_phase_pure))
  in DISCH premise (CONJUNCT2 (UNDISCH extcall_direct_row_phase_pure)) end

(* Encoder writes start at the payload. Private scratch is registered
   separately, so the bytes immediately before the payload stay readable. *)
Theorem abi_encode_saved_prefix_frame:
  window_phase ctx func st en ids outs s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\ shared NOTIN ids /\
  LENGTH prefix <= dst_offset /\ dst_offset <= cap /\
  EVERY (\(p,n). b+dst_offset <= p) outs /\
  read_memory (b+dst_offset-LENGTH prefix) (LENGTH prefix) s = prefix /\
  (!i. b+dst_offset-LENGTH prefix <= i /\ i < b+dst_offset ==> i NOTIN tn.t_mem) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  FLOOKUP t.vs_allocas shared = SOME (b,cap) /\
  read_memory (b+dst_offset-LENGTH prefix) (LENGTH prefix) t = prefix /\
  (!i. b+dst_offset-LENGTH prefix <= i /\ i < b+dst_offset ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >>
  `b+dst_offset-LENGTH prefix+LENGTH prefix = b+dst_offset` by decide_tac >>
  `EVERY (\r. venomMemDefs$regions_disjoint (b+dst_offset-LENGTH prefix,LENGTH prefix) r) outs` by
    (simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD, venomMemDefsTheory.regions_disjoint_def] >>
     qx_genl_tac [`p`,`n`] >> disch_tac >>
     qpat_assum `EVERY (\(p,n). b+dst_offset <= p) outs`
       (qspec_then `(p,n)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     asm_simp_tac (srw_ss()) []) >>
  mp_tac (Q.INST [`owner` |-> `shared`,`q` |-> `b+dst_offset-LENGTH (prefix:word8 list)`,
    `n` |-> `LENGTH (prefix:word8 list)`,`sz` |-> `cap`]
    abi_encode_values_registered_window) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  PURE_REWRITE_TAC [read_memory_eq_mem_bytes_at] >> strip_tac >>
  qpat_assum `read_memory _ _ s = prefix`
    (assume_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* Writes for the ABI members start at byte 32. Cursor and scratch are
   registered apart from the selector word. *)
Theorem extcall_direct_selector_frame:
  window_phase ctx func st en ids outs s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\ shared NOTIN ids /\
  32 <= cap /\ EVERY (\(p,n). b+32 <= p) outs /\
  read_memory (b+28) 4 s = selector /\
  (!i. b+28 <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  FLOOKUP t.vs_allocas shared = SOME (b,cap) /\
  read_memory (b+28) 4 t = selector /\
  (!i. b+28 <= i /\ i < b+32 ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >>
  `LENGTH selector = 4` by
    (qpat_assum `read_memory (b+28) 4 s = selector` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[]) >>
  `b+32-4 = b+28 /\ 4 <= 32` by decide_tac >>
  pop_assum strip_assume_tac >>
  mp_tac (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`] abi_encode_saved_prefix_frame) >>
  asm_rewrite_tac[]
QED

(* Use the frame at each phase's actual cut, retaining the earlier
   allocation cutoff when the phases are composed. *)
Theorem abi_encode_saved_frames_trans:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx ee u /\
  local_ptrs_reserved ce se /\ se.cs_next_var <= a.cs_next_var /\
  se.cs_next_id <= a.cs_next_id /\
  (pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
  (pure_frame ce func ee a v z /\ wb_frame ce ee ee a v z) ==>
  pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (match_mp_tac (Q.SPECL [`ce`,`func`,`ee`,`ee`,`se`,`a`,
        `u`,`v`,`z`] exprSimPropsTheory.pure_frame_trans) >>
      asm_rewrite_tac[] >>
      fs[wb_frame_def]) >>
  match_mp_tac (Q.SPECL [`func`,`ce`,`cx`,`ee`,`u`,`se`,`ee`,`ee`,
    `a`,`v`,`z`,`ctx`]
    (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans)) >>
  asm_rewrite_tac[]
QED

(* Both frame relations stay at the Stage 1 boundary when later encoder
   phases run at later cuts. Compose the same zero-observation path. *)
Theorem extcall_direct_row_frame_trans:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx ee s /\ local_ptrs_reserved ce front /\
  front.cs_next_var <= st.cs_next_var /\ front.cs_next_id <= st.cs_next_id /\
  wb_frame ce ee ee front s u /\ ghost_kept_at lo ce ee front G tn s Gu tu /\
  wb_frame ce ee ee st u t /\ ghost_kept_at lo ce ee st Gu tu u G' tn' /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,G',tn')) ==>
  wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn'))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  conj_tac
  >- (mp_tac (Q.SPECL [`func`,`ce`,`cx`,`ee`,`s`,`front`,`ee`,`ee`,
        `st`,`u`,`t`,`ctx`]
       (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans)) >>
      asm_rewrite_tac[])
  >> conj_tac
  >- (irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
      qpat_assum `stmt_state_rel H ctx func ce cx ee s` (irule_at Any) >>
      qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
      qpat_assum `ghost_kept_at lo ce ee front G tn s Gu tu` (irule_at Any) >>
      qpat_assum `ghost_kept_at lo ce ee st Gu tu u G' tn'` (irule_at Any) >>
      simp[])
  >> gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED
