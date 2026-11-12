(* Calldata decoder shell and setup lemmas the entry2 decoder tower uses,
   kept from the theories the trunk prune removed. *)
Theory decoderCalldataShell
Ancestors
  physicalArrayInitSequence abiDecoderRange
  actualAllocExec fragExecMem allocaFrontierBound allocaBudgetProps
  abiDecoderIndexInit abiDecoderContract compileEnv emitHelper venomState
  venomInst venomExecSemantics venomMemProps venomMemDefs valueEncodingProps
  finite_map words arithmetic list rich_list abiDecoderIndexedAddress
  abiDecoderReentryAddress abiDecoderReentry abiDecoderGuards abiDecoderFrame
  emitHelperProps exprLoweringProps abiEncoder abiDecoderExecution
  valueEncoding valueEncodingDefs instIdxIndep abiDecoderStaticLoopSetup
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderLoopEmit
  abiDecoderCounters abiDecoderDynarrayPrefix abiDecoderDynarrayBound
  abiDecoderArrayHeader abiDecoderReservation abiDecoderArrayLoopInit
  abiDecoderFrameCompose calldataDynOwned abiDecoderLoopCode
  abiDecoderCoherence abiCallerAllocation abiDecoderRecursiveLoopLayout
  abiDecoderArraySetupCode abiDecoderPhi fragExec abiDecoderAppend
  abiDecoderArrayInit abiDecoderMemberInfos actualAllocCredit context
  vyperCompiler memSafeRun unitTransformDefs contextCodegenRel codegenRel
  abiDecoderLoopSetup valueEncodingProofs abiDecoderBytesTyped
  abiCanonicalHeadSize abiDecoderBytes abiDecoderComposition abiDecoderCopy
  abiDecoderAllocation

Theorem calldata_live_excludes_generated:
  abi_decoder_operand_live next op /\ next <= n ==>
  op <> Var (STRING #"%" (toString n))
Proof
  Cases_on `op` >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  metis_tac[]
QED


Theorem calldata_index_init_result_live:
  abi_decode_index_init st = (ip,st') ==>
  abi_decoder_operand_live st'.cs_next_var ip
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  rpt strip_tac >> irule fresh_var_distinct >> decide_tac
QED


Theorem calldata_shell_operand_protection:
  first <= loop_st.cs_next_var /\
  abi_decoder_operand_live loop_st.cs_next_var src /\
  abi_decoder_operand_live loop_st.cs_next_var dst /\
  abi_decoder_operand_live loop_st.cs_next_var ip /\
  abi_decode_loop_prefix ip src opc (Lit 0w) loop_st = (labels,st0) /\
  st0.cs_next_var <= st1.cs_next_var /\
  hiv = STRING #"%" (toString loop_st.cs_next_var) /\
  hcv = STRING #"%" (toString (loop_st.cs_next_var+1)) /\
  hcmp = STRING #"%" (toString (loop_st.cs_next_var+2)) /\
  hdone = STRING #"%" (toString (loop_st.cs_next_var+3)) /\
  nv = STRING #"%" (toString st1.cs_next_var) ==>
  !op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live first op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op
Proof
  strip_tac >>
  `st0.cs_next_var = loop_st.cs_next_var + 4` by
    (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def, abi_decode_position_header_zero, abi_decode_position_header_delta_def] >>
     strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!n. loop_st.cs_next_var <= n ==>
      op <> Var (STRING #"%" (toString n))` by
    (gen_tac >> disch_tac >> irule calldata_live_excludes_generated >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_operand_live st0.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `loop_st.cs_next_var <= st1.cs_next_var` by decide_tac >> simp[]
QED


Theorem calldata_element_setup_static_live:
  abi_decode_array_element_setup ip src dst opc (Lit 0w) hi di abi_sz mem_sz st = (ops,middle) ==>
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op)
Proof
  strip_tac >> drule abi_decode_array_element_setup_operands >> strip_tac >>
  simp[] >> rpt strip_tac >> irule abi_decoder_operand_live_mono >>
  goal_assum (drule_at Any) >> simp[]
QED


Theorem calldata_shell_static_producer:
  first <= loop_st.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first dst /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src opc (Lit 0w) loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst opc (Lit 0w) hi di abi_sz mem_sz st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc (Lit 0w) hi di middle = ((),st1) ==>
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live first op ==>
    op <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
    op <> Var (STRING #"%" (toString (loop_st.cs_next_var+1))) /\
    op <> Var (STRING #"%" (toString (loop_st.cs_next_var+2))) /\
    op <> Var (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
    op <> Var (STRING #"%" (toString st1.cs_next_var)) /\
    abi_decoder_operand_live st0.cs_next_var op)
Proof
  strip_tac >> drule calldata_element_setup_static_live >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `st0.cs_next_var <= st1.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule calldata_index_init_result_live >> strip_tac >>
  simp[] >> ho_match_mp_tac (GEN_ALL calldata_shell_operand_protection) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `st1` >> simp[] >> qexistsl_tac [`opc`,`labels`] >> simp[]
QED


Theorem calldata_loop_child_static:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
    (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
  fn_has_code loop_st last fn ==>
  fn_has_code st0 st1 fn /\ fn_has_code middle st1 fn /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  middle.cs_next_id <= st1.cs_next_id /\
  middle.cs_next_var <= st1.cs_next_var /\
  ?bb. lookup_block st0.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule calldata_element_setup_static_live >> strip_tac >>
  `ci_mono middle st1` by
    (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`SND (SND ops)`,`FST (SND ops)`,
       `CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`di`,`middle`] mp_tac) >> simp[]) >>
  `st0.cs_current_insts = []` by
    (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def, abi_decode_position_header_zero, abi_decode_position_header_delta_def] >>
     strip_tac >> gvs[]) >>
  drule_all abi_decoder_array_body_entry_phi >> strip_tac >>
  fs[ci_mono_def] >> metis_tac[]
QED


Theorem calldata_loop_cfg_producer:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
    (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
  fn_has_code loop_st last fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  lookup_block (FST labels) fn.fn_blocks = SOME
    <|bb_label := FST labels; bb_instructions :=
      abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
        (STRING #"%" (toString loop_st.cs_next_var))
        (STRING #"%" (toString (loop_st.cs_next_var+1)))
        (STRING #"%" (toString (loop_st.cs_next_var+2)))
        (STRING #"%" (toString (loop_st.cs_next_var+3))) st0.cs_current_bb (SND (SND labels))|> /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
        (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|> /\
  FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
  st0.cs_current_bb = FST (SND labels) /\ st0.cs_current_insts = [] /\
  last.cs_current_bb = SND (SND labels) /\ last.cs_current_insts = [] /\
  (?bb. lookup_block (SND (SND labels)) fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  loop_st.cs_next_id <= middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule (SIMP_RULE (srw_ss()) [abi_decode_position_header_zero,
      abi_decode_position_header_delta_def]
    (Q.INST [`base_op` |-> `Lit 0w`] abi_decoder_loop_prefix_facts)) >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule_all calldata_loop_child_static >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  `?bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb` by
    fs[fn_has_code_def] >>
  fs[abi_decode_position_header_zero] >> rpt conj_tac >> FIRST [decide_tac, metis_tac[]]
QED


Theorem calldata_nonbulk_parent_intervals:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray di asz msz dyn maxn) st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st last fn ==>
  ?ip cnt guard_st header_st loop_st labels st0 ops middle st1.
    abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
      ((ip,cnt),loop_st) /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
      (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
    fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\
    fn_has_code st1 last fn /\ fn_has_code loop_st last fn /\
    st.cs_next_id <= header_st.cs_next_id /\
    header_st.cs_next_id < middle.cs_next_id /\
    middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id /\
    st.cs_next_var <= loop_st.cs_next_var /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf dst src _ _ _ _ st = _` kall_tac >>
  qpat_x_assum `dyn \/ _` kall_tac >>
  drule calldata_array_loop_init_trace >> strip_tac >> gvs[] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decoder_loop_prefix_extends >> strip_tac >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_extends >> strip_tac >>
  `cs_extends st loop_st /\ cs_extends st0 middle` by
    metis_tac[cs_extends_same_block, inst_extends_def] >>
  `cs_extends loop_st st1 /\ cs_extends loop_st last` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code st loop_st fn /\ fn_has_code loop_st last fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code loop_st st0 fn /\ fn_has_code st0 st1 fn /\
   fn_has_code st1 last fn /\ fn_has_code st0 middle fn /\ fn_has_code middle st1 fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `ci_mono middle st1` by
    (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`SND (SND ops)`,`FST (SND ops)`,
       `CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`di`,`middle`] mp_tac) >> simp[]) >>
  drule (SIMP_RULE (srw_ss()) [abi_decode_position_header_zero,
      abi_decode_position_header_delta_def]
    (Q.INST [`base_op` |-> `Lit 0w`] abi_decoder_loop_prefix_facts)) >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `?bb. lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX loop_st.cs_current_insts bb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  `!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)` by
    (rpt strip_tac >> irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`,`loop_st.cs_current_bb`] >> simp[] >>
     irule rich_listTheory.IS_PREFIX_MEM >>
     qexists_tac `loop_st.cs_current_insts` >> simp[] >>
     irule rich_listTheory.MEM_DROP_IMP >>
     qexists_tac `LENGTH header_st.cs_current_insts` >> fs[emitted_insts_def]) >>
  qexistsl_tac [`labels`,`st0`,`ops`,`middle`,`st1`] >>
  gvs[ci_mono_def]
QED


Theorem calldata_nonbulk_parent_shell:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray di asz msz dyn maxn) st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st last fn /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?ip cnt guard_st header_st loop_st labels st0 ops middle st1 body_bb exit_bb.
    abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
      ((ip,cnt),loop_st) /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
      (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
    st.cs_next_id <= header_st.cs_next_id /\
    header_st.cs_next_id < middle.cs_next_id /\
    middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
    fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\ fn_has_code st1 last fn /\
    lookup_block (FST labels) fn.fn_blocks = SOME
      <|bb_label := FST labels; bb_instructions :=
        abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
          (STRING #"%" (toString loop_st.cs_next_var))
          (STRING #"%" (toString (loop_st.cs_next_var+1)))
          (STRING #"%" (toString (loop_st.cs_next_var+2)))
          (STRING #"%" (toString (loop_st.cs_next_var+3)))
          (FST (SND labels)) (SND (SND labels))|> /\
    lookup_block (FST (SND labels)) fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    st0.cs_current_bb = FST (SND labels) /\ st0.cs_current_insts = [] /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
          (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|> /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    lookup_block (SND (SND labels)) fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 /\
    last.cs_current_bb = SND (SND labels) /\ last.cs_current_insts = [] /\
    STRING #"%" (toString loop_st.cs_next_var) <>
      STRING #"%" (toString (loop_st.cs_next_var+1)) /\
    src <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
    ip <> Var (STRING #"%" (toString st1.cs_next_var)) /\
    (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
      op <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+1))) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+2))) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
      op <> Var (STRING #"%" (toString st1.cs_next_var)) /\
      abi_decoder_operand_live st0.cs_next_var op) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st0.cs_next_var op ==>
      abi_decoder_operand_live middle.cs_next_var op) /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_nonbulk_parent_intervals >> strip_tac >>
  qpat_x_assum `dyn \/ _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf dst src _ _ _ _ st = _` kall_tac >>
  drule_all calldata_loop_cfg_producer >> strip_tac >>
  drule_all calldata_loop_child_static >> strip_tac >>
  drule_all calldata_shell_static_producer >> strip_tac >>
  rename1 `lookup_block st0.cs_current_bb fn.fn_blocks = SOME body_bb` >>
  rename1 `lookup_block (SND (SND labels)) fn.fn_blocks = SOME exit_bb` >>
  qexistsl_tac [`ip`,`cnt`,`guard_st`,`header_st`,`loop_st`,`labels`,
    `st0`,`ops`,`middle`,`st1`,`body_bb`,`exit_bb`] >>
  asm_simp_tac bool_ss [] >>
  `STRING #"%" (toString loop_st.cs_next_var) <>
   STRING #"%" (toString (loop_st.cs_next_var+1))` by
    (rw[integer_wordTheory.toString_def, integerTheory.Num_EQ] >>
     strip_tac >> gvs[] >> intLib.COOPER_TAC) >>
  simp[] >> metis_tac[]
QED


Theorem calldata_element_setup_reentry:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t =
      SOME (if dec_info_needs_offset di then
        n2w (sb + 32 + w2n (abi_decode_load CALLDATALOAD
          (n2w (sb + 32 + j * abi_sz) : bytes32) s))
        else n2w (sb + 32 + j * abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + j * mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >- (`abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
      `abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
       eval_operand (Lit 0w) s = SOME (n2w 0)` by
        simp[abi_decoder_operand_live_def, eval_operand_def] >>
      `abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s =
        n2w (w2n (abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s))` by
        simp[] >>
      drule_all (SIMP_RULE (srw_ss()) []
        (Q.INST [`hi` |-> `Lit 0w`, `base_op` |-> `Lit 0w`, `B` |-> `0`]
          abi_decode_dynamic_element_setup_reentry)) >>
      strip_tac >> qexists_tac `t` >> simp[]) >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_address_frame_def]
QED


Theorem calldata_bytes_allocation_shape:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem calldata_index_init_owned_fields:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
   (FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= s.vs_alloca_next)) /\
  (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
  (if FLOOKUP s.vs_allocas st.cs_next_id = NONE then
     t.vs_alloca_next = s.vs_alloca_next+32
   else t.vs_alloca_next = s.vs_alloca_next) ==>
  alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!id b cap. FLOOKUP s.vs_allocas id = SOME (b,cap) ==>
    FLOOKUP t.vs_allocas id = SOME (b,cap))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> drule calldata_index_init_instructions >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `?a. step_inst_base inst s = OK a /\
    a.vs_allocas = t.vs_allocas /\ a.vs_alloca_next = t.vs_alloca_next` by
    suspend "transition" >>
  `alloca_inv a` by metis_tac[actual_alloca_slots_preserved] >>
  `alloca_frontier_inv ctx fn site a` by metis_tac[actual_alloca_frontier_preserved] >>
  conj_tac
  >- (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac >>
  gvs[] >> rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[]
QED

Resume calldata_index_init_owned_fields[transition]:
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac
  >- (`FLOOKUP s.vs_allocas inst.inst_id = NONE` by simp[] >>
      drule_all actual_word_alloca_fresh_run >> strip_tac >>
      qexists_tac `t'` >> gvs[] >>
      simp_tac bool_ss [fmap_eq_flookup] >> gen_tac >> Cases_on `x = st.cs_next_id` >>
      gvs[FLOOKUP_UPDATE]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)` by simp[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  qexists_tac `t'` >> gvs[] >>
  simp_tac bool_ss [fmap_eq_flookup] >> gen_tac >> Cases_on `x = st.cs_next_id` >> gvs[]
QED

Finalise calldata_index_init_owned_fields


Theorem calldata_binary_repeat_frame[local]:
  emit_op opc [lhs;rhs] st = (out,st') /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (if opc = ADD then a+b else a*b) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  disch_then (strip_assume_tac o MATCH_MP calldata_binary_repeat) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem calldata_index_init_live_frame:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op (mstore p 0w allocated) = eval_operand op s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  simp[calldata_update_protected] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED


Theorem calldata_indexed_address_repeat:
  abi_decode_indexed_address base_op idx stride st = (address,st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand address t = SOME (n2w (sb+32+j*stride)) /\
    abi_decoder_operand_live st'.cs_next_var address /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset,c2)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j)` by metis_tac[] >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand data s2 = SOME ((n2w sb : bytes32)+32w)` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, word_mul_n2w, update_var_def]
QED


Theorem calldata_element_pointer_repeat:
  !head data stride st ptr st' s hp dp.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD (Lit 0w) head data (Lit 0w) stride st =
    (ptr,st') /\ eval_operand head s = SOME hp /\ eval_operand data s = SOME dp /\
  abi_decoder_operand_live st.cs_next_var head /\
  abi_decoder_operand_live st.cs_next_var data ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ptr t = SOME (dp + abi_decode_load CALLDATALOAD hp s) /\
    abi_decoder_operand_live st'.cs_next_var ptr /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  rpt gen_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [head] st = (off,c1)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand data s1 = SOME dp` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[update_var_def]
QED


Theorem calldata_alloca_invariants_fields:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def]
QED


Theorem calldata_header_owned_state:
  t = jump_to lbl (abi_decode_header_state iv cv cmp done j n s) ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. op <> Var iv /\ op <> Var cv /\ op <> Var cmp /\ op <> Var done ==>
    eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  drule_all calldata_alloca_invariants_fields >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED


Theorem calldata_mload_repeat:
  emit_op MLOAD [src] st = (out,st') /\ eval_operand src s = SOME p ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (mload (w2n p) s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (mload (w2n p) s) s` >>
  `step_inst_base (mk_inst st.cs_next_id MLOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_MLOAD >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var, update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED


Theorem calldata_static_setup_repeat:
  abi_decode_array_element_setup ip src dst opc (Lit 0w) hi di abi_sz mem_sz st = (ops,st') /\
  ~dec_info_needs_offset di /\ eval_operand ip s = SOME p /\
  mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb+32+j*abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decode_static_element_setup_operands >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_element_setup_phases, comp_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_address src idx abi_sz c1 = (child_src,c2)` >>
  rename1 `abi_decode_indexed_address dst idx mem_sz c2 = (child_dst,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_address_counters >>
  drule_all calldata_mload_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j)` by metis_tac[] >>
  `eval_operand src s1 = SOME (n2w sb) /\ eval_operand dst s1 = SOME (n2w d)`
    by metis_tac[] >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c2.cs_next_var idx /\
   abi_decoder_operand_live c2.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\ eval_operand idx s2 = SOME (n2w j)`
    by metis_tac[] >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 end_st) s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED


Theorem calldata_coordinates_repeat:
  abi_decode_indexed_coordinates base_op idx stride st = ((data,address),st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand data t = SOME (n2w (sb+32)) /\
    eval_operand address t = SOME (n2w (sb+32+j*stride)) /\
    abi_decoder_operand_live st'.cs_next_var data /\
    abi_decoder_operand_live st'.cs_next_var address /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset,c2)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j)` by metis_tac[] >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand data s2 = SOME ((n2w sb : bytes32)+32w)` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat_frame)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  `abi_decoder_operand_live c2.cs_next_var data /\
   abi_decoder_operand_live st'.cs_next_var data` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand data t = SOME ((n2w sb : bytes32)+32w)` by metis_tac[] >>
  qexists_tac `t` >> gvs[word_add_n2w, word_mul_n2w, update_var_def]
QED


Theorem calldata_head_setup_repeat:
  abi_decode_array_head_setup ip src abi_sz st = ((idx,data,head),st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand data t = SOME (n2w (sb+32)) /\
    eval_operand head t = SOME (n2w (sb+32+j*abi_sz)) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    abi_decoder_operand_live st'.cs_next_var data /\
    abi_decoder_operand_live st'.cs_next_var head /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_array_head_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_coordinates src idx abi_sz c1 = ((data,head),end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_coordinates_counters >>
  drule_all calldata_mload_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j) /\ eval_operand src s1 = SOME (n2w sb)`
    by metis_tac[] >>
  `abi_decoder_operand_live c1.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_coordinates_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 end_st) s1 = OK t` >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var idx` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     metis_tac[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED


Theorem calldata_dynamic_setup_repeat:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\ dec_info_needs_offset di /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME
      (n2w (sb+32) + abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynamic_element_setup_phases,
    abi_decode_array_source_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  PairCases_on `src_ops` >> PairCases_on `head_ops` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_array_head_setup ip src abi_sz st = ((idx,data,head),c1)` >>
  rename1 `compile_abi_decode_dyn_elem_ptr CALLDATALOAD (Lit 0w) head data (Lit 0w) abi_sz c1 =
    (child_src,c2)` >>
  rename1 `abi_decode_indexed_address dst idx mem_sz c2 = (child_dst,end_st)` >>
  imp_res_tac abi_decode_array_head_setup_counters >>
  imp_res_tac abi_decoder_array_pointer_counters >>
  imp_res_tac abi_decode_indexed_address_counters >>
  drule_all calldata_head_setup_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all calldata_element_pointer_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c1.cs_next_var dst /\
   abi_decoder_operand_live c2.cs_next_var dst /\
   abi_decoder_operand_live c2.cs_next_var idx` by
    (conj_tac
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     conj_tac
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\ eval_operand idx s2 = SOME (n2w j)`
    by metis_tac[] >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 end_st) s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[abi_decode_load_def, abi_decode_source_def] >> metis_tac[]
QED


Theorem calldata_element_setup_repeat:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME
      (if dec_info_needs_offset di then
        n2w (sb+32) + abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s
       else n2w (sb+32+j*abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decoder_address_frame st.cs_next_var s t /\ inst_extends st st'
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >- (drule_all calldata_dynamic_setup_repeat >> strip_tac >>
      qexists_tac `t` >> simp[abi_decoder_address_frame_def]) >>
  drule_all calldata_static_setup_repeat >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_address_frame_def]
QED


Theorem calldata_elems_memory_from_index:
  !vs off. (!k. k < LENGTH vs ==>
    val_in_memory tv (EL k vs) (off+k*type_memory_size tv) mem) ==>
    elems_in_memory vs off tv mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `SUC k` mp_tac) >>
  simp_tac bool_ss [EL, TL, LESS_MONO_EQ, MULT_CLAUSES] >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> simp[]
QED


Theorem calldata_gt_repeat:
  emit_op GT [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (bool_to_word (w2n a > w2n b)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (w2n a > w2n b)) s` >>
  `step_inst_base (mk_inst st.cs_next_id GT [lhs;rhs]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_GT >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED


Theorem calldata_iszero_repeat:
  emit_op ISZERO [arg] st = (out,st') /\ eval_operand arg s = SOME a ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (bool_to_word (a = 0w)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (a = 0w)) s` >>
  `step_inst_base (mk_inst st.cs_next_id ISZERO [arg]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_ISZERO >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED


Theorem calldata_count_guard_repeat_sequence:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= limit ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all calldata_gt_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all calldata_iszero_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last_st)` >>
  `run_inst_seq (emitted_insts c3 last_st) s3 = OK s3` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def, assert_ok]) >>
  imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >>
  conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`,`c2`] >>
      conj_tac >- (irule run_inst_seq_compose_ok >>
        goal_assum (drule_at Any) >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      metis_tac[inst_extends_trans]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  conj_tac
  >- (`abi_decoder_operand_live c1.cs_next_var count_op` by
        metis_tac[abi_decoder_operand_live_emit] >>
      `abi_decoder_operand_live c2.cs_next_var count_op` by
        metis_tac[abi_decoder_operand_live_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live c1.cs_next_var op /\
   abi_decoder_operand_live c2.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  metis_tac[]
QED


Theorem calldata_index_init_repeat_memory_frame:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated ==>
  abi_decode_frame p 32 s (mstore p 0w allocated)
Proof
  strip_tac >>
  `abi_decode_frame p 32 allocated (mstore p 0w allocated)` by
    irule abi_decode_mstore_frame >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[abi_decode_frame_def, update_var_def] >> first_assum ACCEPT_TAC
QED

