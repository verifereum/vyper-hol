(* Allocation-free execution of flat members on their actual source bytes. *)
Theory abiDecodePtrPhysicalFlatRun
Ancestors
  abiDecodePtrPhysicalMemberRun abiDecodePtrFlatLayout abiDecodePtrMemberInterface
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderReentry abiDecoderCounters
  abiDecoderMemberSetup abiDecoderRange vyperTypeABI
  abiDecoderComplexGuard abiDecoderComplexExecute abiDecoderComplexHead
  abiDecoderReentryPointer abiDecoderDynamicLoopSetup abiDecoderReservation
  abiDecoderFrameCompose abiDecoderFrame abiDecoderMemberFrames abiDecoderTypedContract
  abiDecoderContract abiValidMembers abiDecodeRanges abiEncoder exprLowering
  compileEnv valueEncoding vyperABI venomExecSemantics venomState
  fragExec emitHelperProps exprLoweringProps supportedTypes
  words list rich_list arithmetic

Theorem abi_decode_physical_flat_sequence:
  !tys tvs vs pre q st last s.
  EVERY supported_scalar_type tys /\
  LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) tys tvs /\
  vyper_decode_valid_enc_tuple (pre ++ MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)) = SOME vs /\
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
    (abi_decoder_member_infos ce.ce_struct_fields ce tys)
    (SUM (MAP abi_member_head_size pre)) q st = ((),last) /\
  mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B+z+LENGTH bs < dimword(:256) /\
  d+q+SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) /\
  (B+z+LENGTH bs <= d+q \/
    d+q+SUM (MAP (type_memory_bytes ce) tys) <= B+z) /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand pos s = SOME (n2w z) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var (Var src) /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z+LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last /\
    tuple_in_memory vs tvs (d+q) t.vs_memory /\
    abi_decode_frame (d+q) (SUM (MAP (type_memory_bytes ce) tys)) s t /\
    fresh_vars_wrt last t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD t) = bs /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  Induct >- suspend "nil" >>
  qx_gen_tac `ty` >> rpt gen_tac >>
  Cases_on `tvs` >- simp[] >>
  simp_tac bool_ss [EVERY_DEF, LIST_REL_def, MAP] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rename1 `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` >>
  qpat_x_assum `abi_to_vyper_list _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once abi_to_vyper_def, abi_decode_members_def,
    AllCaseEqs(), Excl "dec_def"] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  suspend "cons"
QED

Resume abi_decode_physical_flat_sequence[nil]:
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def, abi_decode_members_def, Once abi_to_vyper_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def,
    inst_extends_def, Once val_in_memory_def, abi_decode_frame_def]
QED

Resume abi_decode_physical_flat_sequence[cons]:
  qpat_x_assum `?v. _` strip_assume_tac >>
  rename1 `abi_to_vyper env ty _ = SOME v` >>
  rename1 `LIST_REL _ tys tailtvs` >>
  qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once abi_decoder_member_infos_def, MAP] >>
  disch_then (strip_assume_tac o MATCH_MP abi_decode_flat_compile_cons) >>
  drule_all abi_decode_physical_member_code_phases >> strip_tac >>
  `d+q+type_memory_bytes ce ty < dimword(:256)` by (fs[SUM] >> decide_tac) >>
  SUBGOAL_THEN ``B+z+LENGTH (bs:word8 list) <= d+q \/ d+q+type_memory_bytes ce ty <= B+z`` assume_tac
  >- (fs[SUM] >> decide_tac) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_decode_physical_member_sequence) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts st sm) s = OK after_head` >>
  suspend "tail"
QED

Resume abi_decode_physical_flat_sequence[tail]:
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `st.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `ready.cs_next_var = _` mp_tac >>
     rpt IF_CASES_TAC >> simp[] >> decide_tac) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
        abi_decoder_operand_live sm.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  first_x_assum (qspecl_then [`tailtvs`, `vs'`, `pre ++ [vyper_to_abi_type env ty]`,
    `q + type_memory_bytes ce ty`, `sm`, `last`, `after_head`] mp_tac) >>
  impl_tac >- suspend "tail_pre" >>
  strip_tac >> suspend "combine"
QED

Resume abi_decode_physical_flat_sequence[tail_pre]:
  rule_assum_tac (PURE_REWRITE_RULE [DROP_DROP_T]) >>
  NO_STRIP_FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP, SUM_APPEND, SUM,
    ADD_0, DROP_DROP_T, ADD_COMM, abi_decoder_member_infos_def] >>
  asm_simp_tac bool_ss [arithmeticTheory.ADD] >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  metis_tac[]
QED

Resume abi_decode_physical_flat_sequence[combine]:
  rename1 `run_inst_seq (emitted_insts sm last) after_head = OK result` >>
  `run_inst_seq (emitted_insts st last) s = OK result /\ inst_extends st last` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`after_head`, `sm`] >> simp[]) >>
  `abi_decode_frame (d+q) (type_memory_bytes ce ty + SUM (MAP (type_memory_bytes ce) tys)) s result` by
    (irule abi_decode_frame_adjacent >> qexists_tac `after_head` >> metis_tac[ADD_ASSOC]) >>
  `value_has_type tv v` by metis_tac[vyperTypeABITheory.abi_to_vyper_well_typed] >>
  `val_in_memory tv v (d+q) result.vs_memory` by
    (irule abi_decoder_value_frame >> conj_tac >- (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`[(d+(q+type_memory_bytes ce ty), SUM (MAP (type_memory_bytes ce) tys))]`, `after_head`] >>
     asm_simp_tac bool_ss [GSYM abi_decode_frame_footprint, abi_footprint_disjoint_def,
       listTheory.EVERY_DEF, pairTheory.FST, pairTheory.SND] >> simp[]) >>
  qexists_tac `result` >>
  asm_simp_tac bool_ss [] >>
  suspend "combine_post"
QED

Resume abi_decode_physical_flat_sequence[combine_post]:
  qpat_x_assum `v::vs' = vs` (SUBST1_TAC o SYM) >>
  asm_simp_tac bool_ss [Once val_in_memory_def, LET_THM, list_case_def, ADD_ASSOC] >> simp[]
QED

Finalise abi_decode_physical_flat_sequence

Theorem abi_decode_physical_flat_run:
  EVERY supported_scalar_type tys /\
  LIST_REL (abi_decoder_coherent ce env ce.ce_struct_fields) tys tvs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) = SOME vs /\
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last) /\
  mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B+z+LENGTH bs < dimword(:256) /\
  d+SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) /\
  (B+z+LENGTH bs <= d \/ d+SUM (MAP (type_memory_bytes ce) tys) <= B+z) /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand pos s = SOME (n2w z) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var (Var src) /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z+LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_decode_frame d (SUM (MAP (type_memory_bytes ce) tys)) s t /\
    fresh_vars_wrt last t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD t) = bs /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard pos hi _ st = ((),middle)` >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  drule abi_valid_members_view >> strip_tac >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z + FOLDR (\(_,asz,_) acc. asz+acc) 0
      (abi_decoder_member_infos ce.ce_struct_fields ce tys) <= h /\ h < dimword(:256)`` assume_tac >-
    (Cases_on `hi = Lit 0w` >- simp[] >>
     qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >>
     strip_tac >> qexists_tac `h` >> asm_simp_tac bool_ss [] >> decide_tac) >>
  drule abi_decode_complex_head_guard_sequence >>
  disch_then (qspecl_then [`z`, `s`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK prepared` >>
  suspend "members"
QED

Resume abi_decode_physical_flat_run[members]:
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `st.cs_next_var <= middle.cs_next_var` by simp[] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  mp_tac (Q.SPECL [`tys`, `tvs`, `vs`, `[]`, `0`, `middle`, `last`, `prepared`]
    abi_decode_physical_flat_sequence) >>
  simp_tac bool_ss [MAP, SUM, APPEND, ADD_CLAUSES, DROP_0] >>
  impl_tac >- suspend "member_pre" >>
  strip_tac >> suspend "post"
QED

Resume abi_decode_physical_flat_run[member_pre]:
  NO_STRIP_FULL_SIMP_TAC (srw_ss()) [abi_decode_source_def] >>
  Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ ?h. _ /\ z + LENGTH bs <= h /\ _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >> qexists_tac `h` >> simp[]
QED

Resume abi_decode_physical_flat_run[post]:
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  `run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`, `middle`] >> simp[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `abi_decode_frame _ _ prepared t` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_frame_def] >> metis_tac[]
QED

Finalise abi_decode_physical_flat_run
