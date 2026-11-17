(* Joint fixed-byte Keccak suffix: instruction certificates precede horizons. *)
Theory bodyFullHashKeccakFixed
Ancestors
  bodyPtrHashBuiltinsKeccakFixedRun bodyPtrHashBuiltinsKeccakFixedFrame
  allocationPtr bodyPtrHashBuiltinsKeccakFixed instIdxIndep
  ptrSafeRun codegenRel contextCodegenRel memLocDefs bodyPtrHashBuiltinsBoundary
  bodyFullAllocGeneric bodyFullGhostFrame instSeqPtrLo
  bodyFullHashAllocFrame bodyFullHashCleanFrame bodyPtrHashBuiltinsCursor
  bodyPtrHashBuiltinsKeccak builtinHashing fragExec
  ptrSafetyTransport fragGasSeqPtr exprSimHash exprSimAlloc
  bodyPtrDefs venomState venomExecSemantics venomInst ptrDiscipline
  bodyPtrHashBuiltinsAllocFrame bodyPtrIfExpAllocCompiler
  context emitHelper loweringStateRelDefs loweringHalt
  bodyPtrPrecompileBuiltinsAllocationFrame
  exprLowering exprLoweringProps emitHelperProps compileEnv words list

Theorem stmt_state_rel_allocas_below_fmp:
  !H ctx func cenv cx es s.
    stmt_state_rel H ctx func cenv cx es s ==>
    (ctx_has_dalloca ctx ==> allocas_below_fmp s)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  fs[stmt_state_rel_def, fmp_room_def, allocas_below_fmp_def,
     venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Theorem fixed_sequence_checked_at[local]:
  stmt_state_rel H ctx fn cenv cx es s /\
  MEM (mk_inst aid ALLOCA [Lit 32w] [p]) (fn_insts fn) /\
  step_inst_base (mk_inst aid ALLOCA [Lit 32w] [p]) s = OK t /\
  eval_operand value t = SOME v /\
  op_taint (step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn) value = {} /\
  m <= 32 /\ stmt_state_rel H ctx fn cenv cx es t /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?Gf tnf. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst aid ALLOCA [Lit 32w] [p];
     mk_inst sid MSTORE [Var p;value] [];
     mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]] s Gf tnf
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `ptr_covers (step_prov PG G (mk_inst aid ALLOCA [Lit 32w] [p]) t)
    (step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn) p t 32` by
    (irule alloca_step_ptr_covers >> simp[] >> metis_tac[]) >>
  `?a. lookup_var p t = SOME a` by gvs[ptr_covers_def] >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst aid ALLOCA [Lit 32w] [p]) t` >>
  qabbrev_tac `tn1 = step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn` >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst aid ALLOCA [Lit 32w] [p]) s`
    by suspend "alloca" >>
  `step_inst_base (mk_inst sid MSTORE [Var p;value] []) t =
     OK (mstore (w2n a) v t)` by
    (simp[Once step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `allocas_from lo t` by
    (irule (cj 1 step_inst_allocas_from) >>
     qexistsl_tac [`ctx`, `0`, `mk_inst aid ALLOCA [Lit 32w] [p]`, `s`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  drule_all hash_store_covered_clean >>
  disch_then (qspecl_then [`PG`, `sid`] strip_assume_tac) >>
  `ptr_inst_ok D lo 0 ctx fn G1 tn1 (mk_inst sid MSTORE [Var p;value] [])
     (t with vs_inst_idx := SUC s.vs_inst_idx)` by suspend "store" >>
  simp[Once inst_seq_ptr_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
    mk_inst_def, is_terminator_def] >>
  simp[Once inst_seq_ptr_def, GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo 0 ctx fn G2 tn2 _ t2` >>
  `ptr_inst_ok D lo 0 ctx fn G2 tn2
     (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) t2` by suspend "sha3" >>
  simp[inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) t2` >>
  simp[inst_seq_ptr_def] >> metis_tac[]
QED

Resume fixed_sequence_checked_at[alloca]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
    op_taint_def, step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def]
QED

Resume fixed_sequence_checked_at[store]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    allocas_below_fmp_def, mk_inst_def, source_memory_write_ranges_def,
    source_memory_read_ranges_def, fixed_source_write_range_def, eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
    eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

Resume fixed_sequence_checked_at[sha3]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `m < dimword (:256)` by decide_tac >>
  `ptr_covers G2 tn2 p t2 32 /\ lookup_var p t2 = SOME a` by
    gvs[Abbr `t2`, ptr_covers_def, lookup_var_def, mstore_def] >>
  `!i. w2n a <= i /\ i < w2n a + m ==> i NOTIN tn2.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn2.t_mem` irule >> decide_tac) >>
  `access_ok lo G2 fn (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) t2` by
    (`access_ok 0 G2 fn (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) t2`
       suffices_by (gvs[access_ok_def] >> metis_tac[]) >>
     gvs[ptr_covers_def] >> irule hash_sha3_access >>
     simp[eval_operand_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `taint_ok fn tn2 (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) t2` by
    (gvs[ptr_covers_def] >> irule hash_sha3_taint >>
     simp[eval_operand_def, op_taint_def]) >>
  `step_inst_base (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) t2 =
    OK (update_var out (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at (w2n a) m t2.vs_memory))) t2)` by
    (irule step_SHA3_bytes >> simp[eval_operand_def]) >>
  simp[ptr_inst_ok_def, mk_inst_def, step_inst_non_invoke] >>
  simp[Abbr `t2`, mstore_def, allocas_from_def, allocas_below_fmp_def] >>
  rpt strip_tac >> gvs[update_var_def, allocas_from_def, allocas_below_fmp_def] >>
  metis_tac[]
QED

Finalise fixed_sequence_checked_at

Theorem fixed_alloc_code[local]:
  compile_keccak256_bytesm value m sa = (op,sb) /\
  compile_alloc_buffer 32 sa = (buf,sm) /\ fn_has_code sa sb fn ==>
  fn_has_code sa sm fn
Proof
  strip_tac >>
  gvs[compile_keccak256_bytesm_def, comp_bind_def, comp_return_def] >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    (mp_tac cs_appends_emit_helpers >>
     simp[cs_appends_def] >> strip_tac >>
     qpat_x_assum `_ sm = (op,sb)` mp_tac >>
     simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
     metis_tac[cs_extends_trans]) >>
  metis_tac[fn_has_code_split]
QED

Theorem hash_fixed_keccak_joint_run:
  !H0:(bool # bytes32 # type_value) list # num list.
  compile_keccak256_bytesm value (LENGTH bs) sa = (op,sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel H0 ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ fn_has_code sa sb fn /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s ==>
  ?u Gf tnf.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    u.vs_current_bb = s.vs_current_bb /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
    eval_operand op u = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!(H:(bool # bytes32 # type_value) list # num list) D. stmt_state_rel H ctx fn cenv cx es s /\
       ghost_inv_at D lo d cenv cx es G tn s ==>
       stmt_state_rel H ctx fn cenv cx es u /\
       ghost_inv_at D lo d cenv cx es Gf tnf u /\
       ghost_kept_at lo cenv es sa G tn s Gf tnf)
Proof
  gen_tac >> strip_tac >> drule_all compile_keccak256_bytesm_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  drule hash_fixed_keccak_emission >> strip_tac >>
  `?buf sm. compile_alloc_buffer 32 sa = (buf,sm)` by metis_tac[pairTheory.PAIR] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  qpat_x_assum `stmt_state_rel H0 ctx fn cenv cx es u` kall_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK allocated` >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK allocated` by
    (drule emitted_allocation_singleton >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  `!x. value = Var x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  drule_all hash_alloca_old_operand >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all fixed_sequence_checked_at >>
  disch_then (qspecl_then [`sa.cs_next_id+1`,
    `STRING #"%" (toString (sa.cs_next_var+1))`, `sa.cs_next_id+2`, `PG`, `G`, `ARB`] strip_assume_tac) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[] >>
  suspend "endpoint"
QED

Resume hash_fixed_keccak_joint_run[endpoint]:
  conj_tac >- (irule hash_run_inst_seq_current_bb >>
    goal_assum (drule_at Any) >> metis_tac[keccak_suffix_shape]) >>
  conj_tac >- suspend "origin" >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) allocated = SOME w'` by
    metis_tac[eval_operand_def] >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+1) MSTORE
    [Var (STRING #"%" (toString sa.cs_next_var));value] []` >>
  qabbrev_tac `i3 = mk_inst (sa.cs_next_id+2) SHA3
    [Var (STRING #"%" (toString sa.cs_next_var));Lit (n2w (LENGTH bs))]
    [STRING #"%" (toString (sa.cs_next_var+1))]` >>
  qabbrev_tac `stored = mstore (w2n w') w allocated` >>
  `step_inst_base i2 allocated = OK stored` by
    (simp[Abbr `i2`, Abbr `stored`, Once step_inst_base_def,
      mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `step_inst_base i3 stored = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  `~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode` by
    simp[Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  drule_all hash_inst_seq_triple_endpoint_raw >> strip_tac >>
  suspend "frames"
QED

Resume hash_fixed_keccak_joint_run[origin]:
  gen_tac >>
  drule_all fixed_sequence_checked_at >>
  disch_then (qspecl_then [`sa.cs_next_id+1`,
    `STRING #"%" (toString (sa.cs_next_var+1))`, `sa.cs_next_id+2`, `PG`, `G`, `D`] strip_assume_tac) >>
  `Gf = Gf' /\ tnf = tnf'` by metis_tac[inst_seq_ptr_ghost_unique] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by metis_tac[] >>
  qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Resume hash_fixed_keccak_joint_run[frames]:
  `?h. u = update_var (STRING #"%" (toString (sa.cs_next_var+1))) h stored` by
    (qsuff_tac `?h. step_inst_base i3 stored = OK
       (update_var (STRING #"%" (toString (sa.cs_next_var+1))) h stored)`
     >- (strip_tac >> qexists_tac `h` >> fs[]) >>
     qexists_tac `word_of_bytes T (0w:bytes32) (Keccak_256_w64
       (mem_bytes_at (w2n w') (w2n (n2w (LENGTH bs):bytes32)) stored.vs_memory))` >>
     simp[NoAsms, Abbr `i3`] >> irule step_SHA3_bytes >>
     simp[eval_operand_def, Abbr `stored`, lookup_var_def, mstore_def]) >>
  `~not_fresh_at sa (STRING #"%" (toString (sa.cs_next_var+1)))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  conj_tac >- simp[hash_sha3_ghost, Abbr `i3`, op_taint_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[hash_sha3_ghost, Abbr `i3`, op_prov_def,
    finite_mapTheory.FLOOKUP_DRESTRICT] >>
  conj_tac >- suspend "frontier" >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (qunabbrev_tac `i1` >>
    qpat_x_assum `stmt_state_rel H0 ctx fn cenv cx es s` kall_tac >>
    qpat_x_assum `stmt_state_rel H0 ctx fn cenv cx es allocated` kall_tac >>
    drule_all compile_keccak256_bytesm_frame >>
    strip_tac >> gvs[]) >>
  suspend "conditional"
QED

Resume hash_fixed_keccak_joint_run[frontier]:
  gvs[Abbr `stored`, mstore_def, update_var_def] >>
  qpat_x_assum `step_inst_base i1 s = OK allocated` mp_tac >>
  simp[Abbr `i1`, Once step_inst_base_def, mk_inst_def,
    exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Resume hash_fixed_keccak_joint_run[conditional]:
  `fn_has_code sa sm fn` by metis_tac[fixed_alloc_code] >>
  qunabbrev_tac `i1` >>
  `ghost_kept_at lo cenv es sa G tn s
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) allocated)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) s allocated tn)` by
    (irule (INST_TYPE [alpha |-> ``:256``] hash_compile_alloc_entry_kept_at) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ghost_inv_at D lo d cenv cx es
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) allocated)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) s allocated tn) allocated` by
    (irule compile_alloc_buffer_ghost_frame_at >>
     simp[] >> conj_tac
     >- (qexists_tac `sa` >> simp[]) >>
     metis_tac[]) >>
  `lo <= w2n w'` by
    (qpat_x_assum `ghost_inv_at D lo d cenv cx es _ _ allocated` mp_tac >>
     simp[ghost_inv_at_def, allocas_from_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `!n b k i. local_region cenv es.scopes allocated n b k /\
      b <= i /\ i < b+k ==> ~(w2n w' <= i /\ i < w2n w' + 32)` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  qunabbrev_tac `i2` >> qunabbrev_tac `stored` >>
  drule_all (INST_TYPE [alpha |-> ``:256``] hash_clean_mstore_frame_at) >>
  disch_then (qspecl_then [`PG`, `sa.cs_next_id+1`] strip_assume_tac) >>
  qunabbrev_tac `i3` >>
  drule_all hash_sha3_fresh_frame_at >>
  disch_then (qspecl_then [`h`, `PG`, `sa.cs_next_id+2`,
    `Var (STRING #"%" (toString sa.cs_next_var))`,
    `Lit (n2w (LENGTH bs))`] strip_assume_tac) >>
  gvs[]
QED

Finalise hash_fixed_keccak_joint_run
