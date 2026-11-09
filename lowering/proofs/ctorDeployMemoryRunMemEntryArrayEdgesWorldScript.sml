Theory ctorDeployMemoryRunMemEntryArrayEdgesWorld
Ancestors
  ctorDeployMemoryRunMemEntryArrayEntryWorld
  ctorDeployMemoryRunMemEntryShiftedCheckedArrayEdges
  ctorDeployMemoryRunMemEntryArraySteps
  ctorDeployMemoryRunMemEntryShiftedObservation
  ctorDeployMemoryFrontier ctorAbiActualArrayInvariant ctorAbiActualArrayHeader
  ctorAbiActualWorld ctorAbiActualSites ctorAbiActualFrame ctorAbiActualNarrow
  abiDecoderLoopRegisters abiDecoderExecution abiDecoderLoop abiDecoderArrayBackedge
  abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderReentry
  abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
  venomState venomExecSemantics venomMemDefs compileEnv words list arithmetic finite_map
  abiDecoderRecursiveLoopContext abiDecoderTypedContract abiCanonicalHeadSize
  contractABI byte valueEncodingProps abiDecoderDynarrayBound abiDecoderGuards abiDecodeRanges

val O = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s``;
val Ow = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    (^O) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot base prefix cursor s /\
    s.vs_tx_ctx = base.vs_tx_ctx /\ s.vs_block_ctx = base.vs_block_ctx /\
    s.vs_outcomes = base.vs_outcomes``;

Theorem ctor_actual_array_header_world_observation_from[local]:
  (^Ow) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  next <= first /\ first+4 <= limit_st.cs_next_var ==>
  (^Ow) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s))
Proof
  simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`LENGTH vs`, `j`] strip_assume_tac) >>
  qabbrev_tac `t = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
    (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
    (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  `abi_encoder_registered_effect {} [] s t` by
    (irule ctor_actual_empty_effect >>
     simp[Abbr `t`, abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `alloca_inv t = alloca_inv s /\
   alloca_frontier_inv_from k ctx func site t = alloca_frontier_inv_from k ctx func site s /\
   ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s` by
    simp_tac (srw_ss()) [LET_THM, Abbr `t`, abi_decode_header_state_def,
      jump_to_def, update_var_def, alloca_inv_def, allocas_non_overlapping_def,
      alloca_next_valid_def, alloca_frontier_inv_from_def, remaining_alloca_budget_def,
      ctor_actual_scratch_def] >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
   t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
   t.vs_outcomes = s.vs_outcomes /\ fresh_vars_wrt limit_st t` by
    simp[Abbr `t`, abi_decode_header_state_def, jump_to_def, update_var_def,
      abi_decoder_fresh_jump] >>
  `mload d t = mload d s /\ mload slot t = mload slot s` by
    simp[NoAsms, mload_def, Abbr `t`, abi_decode_header_state_def, jump_to_def, update_var_def] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >>
      `lookup_var x s = SOME w` by metis_tac[] >>
      `abi_decoder_operand_live first (Var x)` by
        (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF] >>
         metis_tac[LESS_EQ_TRANS]) >>
      `eval_operand (Var x) t = eval_operand (Var x) s` by
        (simp[Abbr `t`, abi_decoder_operand_jump] >>
         first_x_assum irule >> simp[]) >>
      fs[eval_operand_def]) >>
  irule abi_encoder_registered_effect_trans >> qexists `s` >>
  simp[] >> irule abi_encoder_registered_effect_enlarge >>
  qexistsl [`{}`, `[]`] >> simp[]
QED

Theorem ctor_checked_array_header_world_run_from:
  (^Ow) k ctx func site ids D N d outsz next limit_st
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
  ?h. (^Ow) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    gas_path_mem ctx func s 0 (OK h) /\
    h.vs_gas_readings = s.vs_gas_readings /\ alloca_history func h
Proof
  strip_tac >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by fs[] >>
  `src <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `STRING #"%" (toString first) <> STRING #"%" (toString (first+1))` by simp[] >>
  drule_all ctor_checked_header_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_loop_ready hdr ip src DLOAD (n2w slot) (n2w sb) (LENGTH vs) j s` by
    simp[abi_decode_loop_ready_def, w2n_n2w] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_ready_header_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all ctor_actual_array_header_world_observation_from >> strip_tac >>
  qexists `jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem ctor_checked_array_backedge_world_run_from:
  (^Ow) k ctx func site ids D N d outsz next limit_st
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
  ?t. (^Ow) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\ gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  simp_tac bool_ss [] >> strip_tac >>
  `ip <> Var (STRING #"%" (toString nv))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `slot+32 <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  drule_all ctor_checked_backedge_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decode_backedge_sim >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[w2n_n2w] >> disch_tac >>
  drule_all (BETA_RULE ctor_actual_array_observation_backedge_from) >>
  disch_then (qspec_then `hdr` (strip_assume_tac o BETA_RULE)) >>
  qexists `jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem ctor_checked_array_header_world_reach_from:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD (Lit 0w) hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) hi ip src dst
    0 sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
    LENGTH initial.vs_data_section /\
  (^Ow) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?h. (^Ow) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h /\
    gas_path_mem ctx func s 0 (OK h) /\
    h.vs_gas_readings = s.vs_gas_readings /\ alloca_history func h
Proof
  strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
      eval_operand op s = SOME w` by
    (rpt gen_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, eval_operand_def, Excl "enc_def"] >>
     rpt strip_tac >> first_x_assum irule >> fs[IN_DEF]) >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_ranges_def, eval_operand_def] >> strip_tac >> conj_tac >>
     first_x_assum irule >> simp[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256)` by
    fs[abi_decoder_ranges_def, eval_operand_def, Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  `32 <= LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))` by
    (pure_rewrite_tac[canonical_array_tuple] >> simp[enc_number_def, LENGTH_word_to_bytes]) >>
  `sb < dimword (:256) /\ sb+32 <= LENGTH s.vs_data_section` by
    (fs[Excl "enc_def"] >> decide_tac) >>
  `slot+32 <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def, Excl "enc_def"] >> metis_tac[]) >>
  drule_all ctor_checked_array_header_world_run_from >> simp[]
QED
