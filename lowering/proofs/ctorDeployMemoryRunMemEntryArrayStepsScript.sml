Theory ctorDeployMemoryRunMemEntryArraySteps
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunMemEntryCompositeEdges ctorDeployMemoryRunMemEntryCompositeSetup
  ctorAbiActualArrayEntry ctorAbiActualArrayFinite ctorAbiActualArrayHeader
  abiDecoderExecution abiDecoderLoopRegisters abiDecoderLoop abiDecoderContract
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderArrayBackedge
  fragExecMem instMemFrontier unitTransformDefs fragGasPathMem allocaHistory
  venomInst venomExecSemantics venomState exprLoweringProps compileEnv
  words arithmetic list rich_list finite_map unitTransformDefs venomInstProofs
  abiDecoderRecursiveLoopContext abiDecoderTypedContract abiCanonicalHeadSize
  contractABI byte venomMemDefs ctorAbiActualAlloc abiDecoderIndexInit
  fragGasSeqMem venomInstProofs1 ctorAbiActualSites emitHelperProps fragExec
  ctorDeployMemoryRunMemEntryWord emitHelper ctorAbiActualArrayPrepare
  abiDecoderArrayLoopInit abiDecoderVarSequence abiEncoderRegisteredEffect valueEncodingProps
  allocaFrontierBound allocaBudgetProps ctorAbiActualFrame
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderGuards abiDecoderGuard
  ctorAbiActualArrayInvariant ctorAbiActualArrayBody
  abiDecoderLoopSetup abiDecoderIndexedAddress abiEncoder abiDecodeRanges
  abiDecoderArraySetupInputs abiDecoderCoherence abiDecoderOffset
  ctorAbiActualArrayIteration entrySinkExtraction instIdxIndep

Theorem ctor_checked_header_prefix_mem_ok:
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb + 32 <= LENGTH s.vs_data_section /\ src <> Var iv ==>
  run_inst_seq_mem_ok
    (TAKE 4 (abi_decode_header_insts id ip src DLOAD iv cv cmp done body_lbl exit_lbl)) s
Proof
  strip_tac >>
  simp_tac (srw_ss()) [abi_decode_header_insts_def, TAKE_def] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- simp[below_frontier_MLOAD, w2n_n2w] >>
  simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       step_inst_base_opcode_eqs, exec_read1_def, w2n_n2w] >>
  `eval_operand src (update_var iv (mload slot s) s) = SOME (n2w sb)` by
    (Cases_on `src` >> gvs[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var]) >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  conj_tac
  >- (simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def, w2n_n2w] >>
      simp[update_var_def]) >>
  Cases_on `step_inst_base (mk_inst (id+1) DLOAD [src] [cv])
    (update_var iv (mload slot s) s)` >> gvs[mk_inst_def] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >> conj_tac >>
  rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem ctor_checked_header_path:
  abi_decode_loop_cfg func hdr body_lbl exit_lbl id ip src DLOAD iv cv cmp done /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb + 32 <= LENGTH s.vs_data_section /\ src <> Var iv /\ iv <> cv /\
  mload slot s = n2w j /\ abi_decode_load DLOAD (n2w sb : bytes32) s = n2w ncount /\
  j <= ncount /\ ncount < dimword (:256) /\ alloca_history func s ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done j ncount s))) /\
  (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done j ncount s)).vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done j ncount s))
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq (TAKE 4 (abi_decode_header_insts id ip src DLOAD iv cv cmp done body_lbl exit_lbl)) s =
    OK (abi_decode_header_state iv cv cmp done j ncount s)` by
    (irule abi_decode_header_prefix >> simp[w2n_n2w] >> metis_tac[]) >>
  `run_inst_seq_mem_ok
    (TAKE 4 (abi_decode_header_insts id ip src DLOAD iv cv cmp done body_lbl exit_lbl)) s` by
    (irule ctor_checked_header_prefix_mem_ok >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s = OK hs` >>
  `hs.vs_allocas = s.vs_allocas /\ hs.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `hs`, abi_decode_header_state_def, update_var_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    simp[Abbr `code`, abi_decode_header_insts_def, mk_inst_def, is_terminator_def] >>
  `?bb. lookup_block hdr func.fn_blocks = SOME bb /\
    bb.bb_instructions = code ++ [mk_inst (id+4) JNZ [Var done;Label exit_lbl;Label body_lbl] []]` by
    (gvs[abi_decode_loop_cfg_def, Abbr `code`, abi_decode_header_insts_def]) >>
  `LENGTH code = 4` by simp[Abbr `code`, abi_decode_header_insts_def] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[IS_PREFIX_APPEND] >>
  `gas_path_mem ctx func s 0 (OK (hs with vs_inst_idx := 4)) /\
   hs.vs_gas_readings = s.vs_gas_readings /\
   alloca_history func (hs with vs_inst_idx := 4)` by
    (irule ctor_checked_sequence_endpoint >> simp[] >> qexists_tac `code` >> simp[IS_PREFIX_APPEND]) >>
  qmatch_asmsub_abbrev_tac `alloca_history func u` >>
  `~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 4` by
    simp[Abbr `u`, Abbr `hs`, abi_decode_header_state_def, update_var_def] >>
  `get_instruction bb u.vs_inst_idx =
    SOME (mk_inst (id+4) JNZ [Var done;Label exit_lbl;Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `eval_operand (Var done) u = SOME (bool_to_word (~(j < ncount)))` by
    simp[Abbr `u`, Abbr `hs`, abi_decode_header_state_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `?target. lookup_block (if j < ncount then body_lbl else exit_lbl) func.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0` by
    (fs[abi_decode_loop_cfg_def] >> Cases_on `j < ncount` >> simp[] >> metis_tac[]) >>
  `gas_path_mem ctx func u 0 (OK (jump_to (if j < ncount then body_lbl else exit_lbl) u)) /\
   (jump_to (if j < ncount then body_lbl else exit_lbl) u).vs_gas_readings = u.vs_gas_readings /\
   alloca_history func (jump_to (if j < ncount then body_lbl else exit_lbl) u)` by
    (irule ctor_checked_branch_path >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`id+4`, `body_lbl`, `exit_lbl`] >> gvs[] >>
     Cases_on `j < ncount` >> simp[bool_to_word_def]) >>
  `jump_to (if j < ncount then body_lbl else exit_lbl) u =
   jump_to (if j < ncount then body_lbl else exit_lbl) hs` by
    simp[Abbr `u`, jump_to_def] >>
  `u.vs_gas_readings = hs.vs_gas_readings` by simp[Abbr `u`] >>
  conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  metis_tac[]
QED

Theorem ctor_checked_array_header_run:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid ip src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb) /\
  abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs) /\
  slot < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  slot + 32 <= s.vs_alloca_next /\ sb < dimword (:256) /\
  sb + 32 <= LENGTH s.vs_data_section /\ alloca_history func s ==>
  ?h. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    gas_path_mem ctx func s 0 (OK h) /\
    h.vs_gas_readings = s.vs_gas_readings /\ alloca_history func h
Proof
  strip_tac >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by
    fs[ctorAbiActualArrayInvariantTheory.ctor_actual_array_observation_def] >>
  `src <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `STRING #"%" (toString first) <> STRING #"%" (toString (first+1))` by simp[] >>
  drule_all ctor_checked_header_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_loop_ready hdr ip src DLOAD (n2w slot) (n2w sb) (LENGTH vs) j s` by
    simp[abi_decode_loop_ready_def, w2n_n2w] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_ready_header_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all ctor_actual_array_header_observation >> strip_tac >>
  qexists `jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem ctor_checked_array_header_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
    LENGTH initial.vs_data_section /\
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?h. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    gas_path_mem ctx func s 0 (OK h) /\
    h.vs_gas_readings = s.vs_gas_readings /\ alloca_history func h
Proof
  strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (fs[abi_decoder_ranges_def, Excl "enc_def"] >>
     metis_tac[ctorAbiActualArrayInvariantTheory.ctor_actual_array_observation_operand]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[ctorAbiActualArrayInvariantTheory.ctor_actual_array_observation_def,
       abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256)` by
    fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  `32 <= LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))` by
    (pure_rewrite_tac[canonical_array_tuple] >> simp[enc_number_def, LENGTH_word_to_bytes]) >>
  `sb < dimword (:256) /\ sb+32 <= LENGTH s.vs_data_section` by
    (fs[ctorAbiActualArrayInvariantTheory.ctor_actual_array_observation_def, Excl "enc_def"] >> decide_tac) >>
  `slot+32 <= s.vs_alloca_next` by
    (fs[ctorAbiActualArrayInvariantTheory.ctor_actual_array_observation_def,
        alloca_inv_def, alloca_next_valid_def, Excl "enc_def"] >> metis_tac[]) >>
  drule_all ctor_checked_array_header_run >> simp[]
QED

Theorem ctor_checked_index_sequence_mem_ok:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id IN ids` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all ctor_actual_word_alloca_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `p < dimword (:256)` by (irule ctor_actual_index_slot_bound >> metis_tac[mk_inst_def]) >>
  `p+32 <= t.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[Abbr `inst`, mk_inst_def]) >>
  simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  gvs[Abbr `inst`] >>
  pure_once_rewrite_tac[GSYM mk_inst_def] >>
  rewrite_tac[run_inst_seq_mem_ok_last] >> conj_tac
  >- simp[below_frontier_MSTORE, w2n_n2w] >>
  simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]
QED

Theorem ctor_checked_alloca_path:
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = ALLOCA /\
  step_inst_base inst s = OK t ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  t.vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    simp[is_terminator_def] >>
  `inst_mem_below_frontier inst s` by
    (irule below_frontier_no_ranges >> simp[]) >>
  `memSafeRun$inst_dload_in_section inst s` by
    simp[memSafeRunTheory.inst_dload_in_section_def] >>
  drule_all straight_line_mem_edge >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `~t.vs_halted` by
    (drule step_inst_base_preserves_all >> simp[] >> metis_tac[]) >>
  `gas_path_mem ctx func (t with vs_inst_idx := SUC s.vs_inst_idx) 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (gvs[] >> drule_all (cj 2 gas_path_mem_rules) >> simp[]) >>
  drule gas_path_mem_ok_suffix >> simp[] >> strip_tac >> simp[] >>
  drule_all alloca_history_base_step >> simp[]
QED

Theorem ctor_checked_index_endpoint:
  abi_decode_index_init st = (ip,st') /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := s.vs_inst_idx + 2)) /\
  t.vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (t with vs_inst_idx := s.vs_inst_idx + 2)
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := s.vs_inst_idx + 2))` by
    gvs[mk_inst_def] >>
  drule gas_path_mem_ok_suffix >> simp[] >> strip_tac >> simp[] >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[run_inst_seq_def] >>
  simp_tac (srw_ss()) [AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base (mk_inst st.cs_next_id ALLOCA _ _) s = OK a` >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString st.cs_next_var)])` by
    (gvs[IS_PREFIX_APPEND] >>
     `s.vs_inst_idx < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP]) >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >>
     simp[get_instruction_def, HD_DROP]) >>
  `alloca_history func (a with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule_all alloca_history_base_step >> simp[mk_inst_def, is_terminator_def]) >>
  `alloca_inv a` by
    (irule venomMemPropsTheory.alloca_inv_step_inst >>
     qexistsl [`ctx`, `0`, `mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]`, `s`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  `a.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `step_inst_base _ s = OK a`
       (mp_then Any mp_tac step_inst_base_preserves_all) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (st.cs_next_id+1) MSTORE
      [Var (STRING #"%" (toString st.cs_next_var)); Lit 0w] [])` by
    (gvs[IS_PREFIX_APPEND] >>
     `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP]) >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `EL 1`) >>
     simp[get_instruction_def, EL_DROP, ADD1, ADD_COMM]) >>
  `step_inst_base (mk_inst (st.cs_next_id+1) MSTORE
      [Var (STRING #"%" (toString st.cs_next_var)); Lit 0w] [])
      (a with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def, mk_inst_def, is_terminator_def] >>
  `alloca_inv (a with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `alloca_inv a` mp_tac >>
     simp[alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def]) >>
  `lookup_block a.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all (SRULE [] (Q.SPECL [`func`, `a with vs_inst_idx := SUC s.vs_inst_idx`]
    alloca_history_base_step)) >>
  simp[mk_inst_def, is_terminator_def, ADD1]
QED

Theorem ctor_checked_array_index_entry:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t p. eval_operand ip t = SOME (n2w p) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_index_observation >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  `st.cs_next_id IN ids` by fs[ctor_actual_sites_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule ctor_checked_index_sequence_mem_ok >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule ctor_actual_index_insts >> strip_tac >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
    emitted_insts st st' = code` by
    (fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
    t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all ctor_checked_index_endpoint >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[] >> gvs[]) >>
  `~t.vs_halted` by (drule_all ctor_actual_index_var_frame >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by gvs[mk_inst_def, is_terminator_def] >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`, `p`] >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem ctor_checked_array_count_header_mem_ok:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH s.vs_data_section /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  d+32 <= s.vs_alloca_next /\ abi_decoder_operand_live st.cs_next_var dst ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [abiDecoderArrayHeaderTheory.abi_decode_array_header_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def, w2n_n2w] >>
  `dst <> Var (STRING #"%" (toString st.cs_next_var))` by
    (Cases_on `dst` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `eval_operand dst (update_var (STRING #"%" (toString st.cs_next_var))
    (abi_decode_load DLOAD (n2w sb : bytes32) s) s) = SOME (n2w d)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst st.cs_next_id DLOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load DLOAD (n2w sb : bytes32) s) s)` by
    (irule abi_decode_read_step >> simp[abi_decode_source_opcode_def]) >>
  gvs[mk_inst_def] >> pure_once_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE, w2n_n2w,
    update_var_def]
QED

Theorem ctor_checked_array_count_header_reach:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  d+32 <= initial.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history func initial ==>
  ?actual. eval_operand cnt actual = SOME (abi_decode_load DLOAD (n2w sb : bytes32) initial) /\
    mem_word_at d actual.vs_memory = abi_decode_load DLOAD (n2w sb : bytes32) initial /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_count_header_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule_all ctor_actual_array_count_header_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule ctor_checked_array_count_header_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _ /\ _ /\ ~is_alloca_op _` drule >>
     qpat_x_assum `!i. MEM i _ ==> abi_decoder_reentry_opcode _` drule >>
     simp[abi_decoder_reentry_opcode_def, is_alloca_op_def] >>
     rpt strip_tac >> gvs[]) >>
  `actual.vs_current_bb = initial.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  `actual.vs_halted = initial.vs_halted` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_halted` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decode_frame_def,
    fresh_vars_wrt_def, lookup_var_def, abi_encoder_registered_effect_def] >>
  metis_tac[]
QED

Theorem ctor_checked_array_header_index_entry:
  abi_decode_array_header dst src DLOAD st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st header_st func /\ fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func initial ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `d+32 <= initial.vs_alloca_next` by decide_tac >>
  drule_all ctor_checked_array_count_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial header` >>
  `alloca_inv header /\ alloca_frontier_inv ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     qpat_x_assum `alloca_frontier_inv ctx func site initial` mp_tac >>
     qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_checked_array_index_entry >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func header actual` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial header` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `header.vs_call_ctx = initial.vs_call_ctx /\
    header.vs_data_section = initial.vs_data_section` by fs[abi_decode_frame_def] >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id p initial 0 0 actual` by
    (irule ctor_actual_array_observation_rebase >>
     qexistsl [`header_st.cs_next_var`, `header`] >> simp[abi_decode_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]) >>
  qexistsl [`actual`, `p`] >> simp[] >>
  conj_tac >- (irule abi_decode_sim_trans >> qexists `header` >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem ctor_checked_array_prefix_mem_ok:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH s.vs_data_section ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_dynarray_prefix_def,
    abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
    abi_decode_dynarray_end_def, abi_decode_le_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND] >>
  (once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
   >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
   simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def, w2n_n2w] >>
   BasicProvers.TOP_CASE_TAC >> simp[] >> irule run_inst_seq_mem_ok_every >>
   simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
   rpt strip_tac >> gvs[] >> irule below_frontier_no_ranges >> simp[])
QED

Theorem ctor_checked_array_prefix_reach:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+n*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history func initial ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_prefix_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `actual.vs_allocas = initial.vs_allocas` by fs[abi_decoder_address_frame_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule ctor_checked_array_prefix_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     simp[abi_decoder_reentry_opcode_def, is_alloca_op_def] >>
     rpt strip_tac >> gvs[]) >>
  `actual.vs_current_bb = initial.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  `actual.vs_halted = initial.vs_halted` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_halted` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decoder_address_frame_def,
    fresh_vars_wrt_def, lookup_var_def, abi_encoder_registered_effect_def] >>
  metis_tac[]
QED

Theorem ctor_checked_array_prefix_header_index_entry:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+LENGTH vs*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func initial ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_checked_array_prefix_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  `guard.vs_allocas = initial.vs_allocas /\
    guard.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  `alloca_inv guard /\ alloca_frontier_inv ctx func site guard /\
    ctor_actual_scratch func ids D N guard /\ D+N <= guard.vs_alloca_next` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     qpat_x_assum `alloca_frontier_inv ctx func site initial` mp_tac >>
     qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `eval_operand src guard = SOME (n2w sb) /\
    eval_operand dst guard = SOME (n2w d)` by fs[abi_decoder_address_frame_def] >>
  `guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `sb+32 <= LENGTH guard.vs_data_section` by simp[] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ initial = _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_load_def, abi_decode_source_def] >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live guard_st.cs_next_var src /\
    abi_decoder_operand_live guard_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all ctor_checked_array_header_index_entry >>
  disch_then (qspec_then `tv` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func guard actual` >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
    guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual` by
    (irule ctor_actual_array_observation_rebase >>
     qexistsl [`guard_st.cs_next_var`, `guard`] >> simp[] >>
     rpt strip_tac >> irule ctor_actual_address_old_vars >>
     goal_assum (drule_at Any) >> qexists `st.cs_next_var` >> simp[]) >>
  qexistsl [`actual`, `slot`] >> simp[] >>
  conj_tac >- (irule abi_decode_sim_trans >> qexists `guard` >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem ctor_checked_increment_mem_ok:
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ ip <> Var nv ==>
  run_inst_seq_mem_ok (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s
Proof
  strip_tac >> simp_tac (srw_ss()) [abi_decode_backedge_insts_def, TAKE_def] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def,
    step_inst_base_opcode_eqs, exec_pure2_def] >>
  Cases_on `eval_operand (Var iv) s` >> simp[] >>
  `eval_operand ip (update_var nv (x + 1w) s) = SOME (n2w slot)` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  simp[eval_operand_lit, run_inst_seq_mem_ok_last, below_frontier_MSTORE, w2n_n2w,
    GSYM update_var_def] >>
  pure_once_rewrite_tac[GSYM mk_inst_def] >>
  simp[below_frontier_MSTORE, w2n_n2w, update_var_def]
QED

Theorem ctor_checked_backedge_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  eval_operand ip s = SOME (n2w slot) /\ ip <> Var nv /\
  j < ncount /\ ncount < dimword (:256) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ alloca_history func s ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))) /\
  (jump_to hdr (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s))).vs_gas_readings =
    s.vs_gas_readings /\
  alloca_history func (jump_to hdr (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)))
Proof
  strip_tac >>
  `run_inst_seq (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s =
    OK (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s))` by
    (drule_all abi_decode_increment_prefix >> simp[w2n_n2w]) >>
  `run_inst_seq_mem_ok (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s` by
    (irule ctor_checked_increment_mem_ok >> conj_tac >- simp[] >>
     qexists `slot` >> simp[]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s = OK hs` >>
  `hs.vs_allocas = s.vs_allocas /\ hs.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `hs`, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    simp[Abbr `code`, abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `code`, abi_decode_backedge_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  `gas_path_mem ctx func s 0 (OK (hs with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
   hs.vs_gas_readings = s.vs_gas_readings /\
   alloca_history func (hs with vs_inst_idx := s.vs_inst_idx + LENGTH code)` by
    (irule ctor_checked_sequence_endpoint >> goal_assum (drule_at Any) >> simp[] >>
     qexists `code` >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `alloca_history func u` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = LENGTH prefix + 2` by
    simp[Abbr `u`, Abbr `hs`, Abbr `code`, abi_decode_backedge_insts_def,
      mstore_def, update_var_def, write_memory_with_expansion_def] >>
  `get_instruction bb u.vs_inst_idx = SOME (mk_inst (id+2) JMP [Label hdr] [])` by
    simp[get_instruction_def, abi_decode_backedge_insts_def, EL_APPEND_EQN] >>
  `gas_path_mem ctx func u 0 (OK (jump_to hdr u)) /\
    (jump_to hdr u).vs_gas_readings = u.vs_gas_readings /\
    alloca_history func (jump_to hdr u)` by
    (irule ctor_checked_jump_path >> simp[] >>
     qexists `id+2` >> simp[] >> metis_tac[]) >>
  `jump_to hdr u = jump_to hdr hs` by simp[Abbr `u`, jump_to_def] >>
  `u.vs_gas_readings = hs.vs_gas_readings` by simp[Abbr `u`] >>
  conj_tac >- (drule_all gas_path_mem_then >> gvs[]) >> metis_tac[]
QED

Theorem ctor_checked_array_backedge_run:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString nv)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  eval_operand ip s = SOME (n2w slot) /\ abi_decoder_operand_live next ip /\
  slot < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  alloca_history func s ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\ gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  strip_tac >>
  `ip <> Var (STRING #"%" (toString nv))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `slot+32 <= s.vs_alloca_next` by
    (fs[ctor_actual_array_observation_def, alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  drule_all ctor_checked_backedge_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decode_backedge_sim >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[w2n_n2w] >> disch_tac >>
  drule_all ctor_actual_array_observation_backedge >> strip_tac >>
  qexists `jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem ctor_checked_array_address_prefix_mem_ok:
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\
  (!t. run_inst_seq_mem_ok tail t) ==>
  run_inst_seq_mem_ok
    (mk_inst id MLOAD [ip] [iv] ::
     mk_inst (id+1) ADD [src;Lit 32w] [sv] ::
     mk_inst (id+2) MUL [Var iv;Lit (n2w asz)] [ov] ::
     mk_inst (id+3) ADD [Var sv;Var ov] [hv] :: tail) s
Proof
  strip_tac >> once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- simp[below_frontier_MLOAD, w2n_n2w] >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  Cases_on `tail`
  >- (simp[run_inst_seq_mem_ok_last, mk_inst_def,
      memSafeRunTheory.inst_dload_in_section_def] >>
      irule below_frontier_no_ranges >> simp[]) >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem ctor_checked_array_static_setup_mem_ok:
  abi_decode_array_element_setup ip src dst DLOAD hi di asz msz st = (ops,st') /\
  ~dec_info_needs_offset di /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  irule ctor_checked_array_address_prefix_mem_ok >> simp[] >>
  reverse conj_tac >- (qexists `slot` >> simp[]) >>
  gen_tac >> irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem ctor_checked_array_head_setup_mem_ok:
  abi_decode_array_head_setup ip src asz st = (ops,st') /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  irule ctor_checked_array_address_prefix_mem_ok >>
  simp[run_inst_seq_mem_ok_def] >> qexists `slot` >> simp[]
QED

Theorem ctor_checked_indexed_address_mem_ok:
  abi_decode_indexed_address base_op idx stride st = (address_op,st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[abi_decode_indexed_address_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    emitted_insts_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem ctor_checked_dyn_elem_ptr_mem_ok:
  compile_abi_decode_dyn_elem_ptr DLOAD elem_src src_data hi asz st = (ptr_op,st') /\
  eval_operand elem_src s = SOME (n2w head) /\ head < dimword (:256) /\
  head+32 <= LENGTH s.vs_data_section ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def, emitted_insts_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def,
    eval_operand_def, w2n_n2w] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, memSafeRunTheory.inst_dload_in_section_def] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem ctor_checked_emitted_mem_chain:
  inst_extends st middle /\ inst_extends middle st' /\
  run_inst_seq (emitted_insts st middle) s = OK prepared /\
  run_inst_seq_mem_ok (emitted_insts st middle) s /\
  run_inst_seq_mem_ok (emitted_insts middle st') prepared ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  `emitted_insts st st' = emitted_insts st middle ++ emitted_insts middle st'` by
    (irule emitted_insts_append >>
     fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_LENGTH_APPEND]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED

Theorem ctor_checked_dyn_elem_ptr_extends:
  compile_abi_decode_dyn_elem_ptr DLOAD elem_src src_data hi asz st = (ptr_op,st') ==>
  inst_extends st st'
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >> strip_tac >> gvs[] >>
  simp[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem ctor_checked_array_source_setup_mem_ok:
  abi_decode_array_source_setup ip src DLOAD hi asz st = (ops,st') /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w idx /\
  eval_operand src s = SOME (n2w sb) /\
  sb+32+idx*asz < dimword (:256) /\
  sb+32+idx*asz+32 <= LENGTH s.vs_data_section /\
  abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule abi_decode_array_source_setup_split >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decoder_array_pointer_counters >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var` by
    (Cases_on `hi = Lit 0w` >> gvs[] >> decide_tac) >>
  `mload (w2n (n2w slot : bytes32)) s = n2w idx` by simp[w2n_n2w] >>
  drule_all abi_decode_array_head_setup_reentry >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (drule ctor_checked_array_head_setup_mem_ok >> disch_then irule >>
     qexists `slot` >> simp[]) >>
  `inst_extends c1 st'` by metis_tac[ctor_checked_dyn_elem_ptr_extends] >>
  `run_inst_seq_mem_ok (emitted_insts c1 st') t` by
    (drule ctor_checked_dyn_elem_ptr_mem_ok >> disch_then irule >>
     qexists `sb+32+idx*asz` >> gvs[abi_decoder_address_frame_def]) >>
  drule_all ctor_checked_emitted_mem_chain >> simp[]
QED

Theorem ctor_checked_array_dynamic_setup_mem_ok:
  abi_decode_array_element_setup ip src dst DLOAD hi di asz msz st = (ops,st') /\
  dec_info_needs_offset di /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w idx /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load DLOAD (n2w (sb+32+idx*asz) : bytes32) s = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
     sb+32+child_off+asz <= hb /\ hb < dimword (:256)) /\
  sb+32+idx*asz < dimword (:256) /\
  sb+32+idx*asz+32 <= LENGTH s.vs_data_section /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynamic_element_setup_split >> strip_tac >>
  drule abi_decode_array_source_setup_counters >> strip_tac >>
  drule abi_decode_indexed_address_counters >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `mload (w2n (n2w slot : bytes32)) s = n2w idx` by simp[w2n_n2w] >>
  drule_all abi_decode_array_source_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK prepared` >>
  `eval_operand dst prepared = SOME (n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  drule_all abi_decode_indexed_address_reentry >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (drule ctor_checked_array_source_setup_mem_ok >> disch_then irule >>
     conj_tac >- (qexistsl [`idx`, `sb`, `slot`] >> simp[]) >>
     simp[] >> qexists `limit_st` >>
     Cases_on `hi = Lit 0w` >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts c1 st') prepared` by
    metis_tac[ctor_checked_indexed_address_mem_ok] >>
  drule_all ctor_checked_emitted_mem_chain >> simp[]
QED

Theorem ctor_checked_array_head_contained:
  has_type (Array NONE aty) (ListV (pre ++ av::post)) /\ is_dynamic aty /\
  sb + LENGTH (enc (Array NONE aty) (ListV (pre ++ av::post))) < dimword (:256) /\
  sb + LENGTH (enc (Array NONE aty) (ListV (pre ++ av::post))) <= LENGTH section ==>
  sb+32+LENGTH pre*abi_member_head_size aty < dimword (:256) /\
  sb+32+LENGTH pre*abi_member_head_size aty+32 <= LENGTH section
Proof
  strip_tac >>
  drule canonical_array_member_ranges >> simp_tac bool_ss [LET_THM] >>
  simp[abi_member_head_size_def, Excl "enc_def"] >> strip_tac >> decide_tac
QED

Theorem ctor_checked_array_setup_mem_ok:
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) <= LENGTH s.vs_data_section /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)`
  >- (drule_all abi_decoder_dynarray_child_layout >> strip_tac >>
      `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
      `abi_embedded_static_size ce.ce_struct_fields ty =
         abi_member_head_size (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
      `is_dynamic (vyper_to_abi_type env ty)` by
        metis_tac[abi_decoder_array_child_offset] >>
      qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
      `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
          (ListV (pre ++ av::post)))) (abi_decode_source DLOAD s) =
        enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))` by
        (qpat_x_assum `mem_bytes_at _ _ s.vs_data_section = _` mp_tac >>
         simp[abi_decode_source_def, Excl "enc_def"]) >>
      drule_all abi_decoder_canonical_dynamic_setup_inputs >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all ctor_checked_array_head_contained >> strip_tac >>
      drule ctor_checked_array_dynamic_setup_mem_ok >> disch_then irule >>
      asm_simp_tac bool_ss [] >>
      conj_tac >- (qexists `d` >> asm_rewrite_tac[]) >>
      conj_tac >- (qexistsl [`LENGTH (pre ++ av::post) * abi_member_head_size (vyper_to_abi_type env ty) +
          SUM (MAP (abi_member_tail_size (vyper_to_abi_type env ty)) pre)`,
          `LENGTH pre`, `sb`, `slot`] >>
        qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >>
        qpat_x_assum `hi = Lit 0w \/ ?hb. _` mp_tac >>
        simp[Excl "enc_def"]) >>
      asm_rewrite_tac[] >> qexists `limit_st` >> asm_rewrite_tac[]) >>
  drule ctor_checked_array_static_setup_mem_ok >> disch_then irule >>
  asm_rewrite_tac[] >> qexists `slot` >> simp[]
QED

Theorem ctor_checked_array_setup_labels:
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) <= LENGTH s.vs_data_section /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    gas_path_mem ctx func s 0 (OK t) /\ t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `mload (w2n (n2w slot : bytes32)) s = n2w (LENGTH pre)` by simp[] >>
  drule_all ctor_actual_array_setup_labels >> strip_tac >>
  drule ctor_actual_array_setup_opcodes >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
     Cases_on `hi = Lit 0w` >>
     simp[abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
       compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, emitted_insts_def] >>
     strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all ctor_checked_array_setup_mem_ok >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `t.vs_allocas = s.vs_allocas` by fs[abi_decoder_address_frame_def] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
      fresh_vars_wrt_def, eval_op_inst_idx]
QED
