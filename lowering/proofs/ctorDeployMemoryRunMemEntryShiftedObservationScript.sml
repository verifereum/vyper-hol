(* Expanded persistent array observations with reserved allocation credit.
   O is only an ML quotation, not a logical definition. *)
Theory ctorDeployMemoryRunMemEntryShiftedObservation
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunMemEntryShiftedFrame ctorDeployMemoryFrontier
  ctorAbiActualArrayInvariant ctorAbiActualArrayEntry
  ctorAbiActualSites ctorAbiActualFrame abiDecoderReentryAddress abiDecoderDynamicLoopSetup
  abiDecoderContract abiDecoderExecution abiDecoderArraySetupInputs abiDecoderTypedContract
  abiDecoderArrayInvariant abiEncoderRegisteredEffect abiDecoderReentry
  allocaBudgetProps allocaFrontierBound valueEncoding venomMemDefs
  venomState compileEnv finite_map list words arithmetic pred_set
  ctorAbiActualArrayIteration ctorAbiActualObservations abiDecoderVarSequence
  ctorAbiActualChildFrame ctorAbiActualMemory
  abiEncoderPrimitiveEffect abiDecoderArrayPrefix abiEncoderProps
  venomExecSemantics valueEncodingProps vyperTyping rich_list

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

Theorem ctor_actual_array_observation_entry_from:
  mload d initial = n2w (LENGTH vs) /\
  FLOOKUP initial.vs_allocas slot_id = SOME (slot,32) /\ mload slot initial = 0w /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  fresh_vars_wrt limit_st initial ==>
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial 0 0 initial
Proof
  simp[val_in_memory_def, abi_encoder_registered_effect_refl]
QED

Theorem ctor_actual_array_observation_terminal_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) s ==>
  elems_in_memory vs (d+32) tv s.vs_memory /\
  mload d s = n2w (LENGTH vs) /\ mload slot s = n2w (LENGTH vs)
Proof
  simp[]
QED

Theorem ctor_actual_array_observation_operand_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
  eval_operand op s = SOME w
Proof
  strip_tac >> Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, eval_operand_def] >>
  first_x_assum irule >> fs[IN_DEF]
QED

Theorem ctor_actual_array_observation_ranges_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  abi_decoder_ranges DLOAD hi src dst sb len d outsz b cap initial ==>
  abi_decoder_ranges DLOAD hi src dst sb len d outsz b cap s
Proof
  strip_tac >>
  `!op w. abi_decoder_operand_live next op /\
      eval_operand op initial = SOME w ==> eval_operand op s = SOME w` by
    (rpt gen_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, eval_operand_def] >>
     rpt strip_tac >> first_x_assum irule >> fs[IN_DEF]) >>
  fs[abi_decoder_ranges_def] >> metis_tac[]
QED

Theorem ctor_actual_address_allocations_from:
  abi_decoder_address_frame next s t ==>
  (alloca_inv t = alloca_inv s) /\
  (alloca_frontier_inv_from k ctx func site t = alloca_frontier_inv_from k ctx func site s) /\
  (ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s)
Proof
  simp[abi_decoder_address_frame_def] >> strip_tac >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_from_def, remaining_alloca_budget_def, ctor_actual_scratch_def]
QED

Theorem ctor_actual_array_observation_inst_idx_from[simp]:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (s with vs_inst_idx := idx) <=>
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s
Proof
  simp[alloca_inv_def, alloca_frontier_inv_from_def, remaining_alloca_budget_def,
    allocas_non_overlapping_def, alloca_next_valid_def,
    ctor_actual_scratch_def, fresh_vars_wrt_def, lookup_var_def,
    abi_encoder_registered_effect_def, mload_def]
QED

Theorem ctor_actual_array_observation_setup_inputs_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_operand_live next ip /\ eval_operand ip initial = SOME (n2w slot) /\
  mem_bytes_at sb len initial.vs_data_section = bytes ==>
  eval_operand ip s = SOME (n2w slot) /\
  mload (w2n (n2w slot : bytes32)) s = n2w cursor /\
  mem_bytes_at sb len s.vs_data_section = bytes
Proof
  strip_tac >>
  `eval_operand ip s = SOME (n2w slot)` by
    (Cases_on `ip` >>
     gvs[abi_decoder_operand_live_def, eval_operand_def] >>
     first_x_assum irule >> fs[IN_DEF]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_frontier_inv_from_word_bound] >>
  `slot + 32 <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `slot < dimword (:256)` by decide_tac >> fs[]
QED

Theorem ctor_actual_array_observation_rebase_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot prepared prefix cursor s /\
  earlier <= next /\
  prepared.vs_data_section = initial.vs_data_section /\
  prepared.vs_call_ctx = initial.vs_call_ctx /\
  prepared.vs_labels = initial.vs_labels /\
  (!x w. abi_decoder_older_vars earlier x /\ lookup_var x initial = SOME w ==>
    lookup_var x prepared = SOME w) /\
  abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial prepared ==>
  (^O) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor s
Proof
  simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial s` by
    (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_older_vars next x` by
    (fs[abi_decoder_older_vars_def, IN_DEF] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem ctor_actual_array_observation_child_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j prepared /\
  j < LENGTH vs /\ all_have_type tv vs /\ D <= d /\
  d+32+j*type_memory_size tv+type_memory_size tv <= d+outsz /\
  d+outsz <= D+N /\ child SUBSET ids /\ slot_id NOTIN child /\
  venomMemDefs$regions_disjoint (slot,32) (d+32+j*type_memory_size tv,type_memory_size tv) /\
  next <= middle.cs_next_var /\
  abi_encoder_registered_effect (ctor_actual_sites func child)
    [(d+32+j*type_memory_size tv,type_memory_size tv)] prepared t /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory /\
  alloca_inv t /\ alloca_frontier_inv_from k ctx func site t /\
  ctor_actual_scratch func ids D N t /\ D+N <= t.vs_alloca_next /\
  fresh_vars_wrt limit_st t /\ t.vs_data_section = prepared.vs_data_section /\
  t.vs_call_ctx = prepared.vs_call_ctx /\ t.vs_labels = prepared.vs_labels /\
  (!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==> lookup_var x t = SOME w) ==>
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j t
Proof
  simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  `D <= d+32 /\ d+32+j*type_memory_size tv <= D+N` by
    (qpat_x_assum `D <= d` mp_tac >>
     qpat_x_assum `d+outsz <= D+N` mp_tac >>
     qpat_x_assum `_ + type_memory_size tv <= d+outsz` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `all_have_type tv (TAKE j vs)` by
    (fs[all_have_type_EVERY] >> simp[EVERY_TAKE]) >>
  `elems_in_memory (TAKE j vs ++ [EL j vs]) (d+32) tv t.vs_memory` by
    (irule ctor_actual_child_append_element >> asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     qexistsl [`D`, `N`, `ids`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `mload slot t = mload slot prepared` by
    (metis_tac[ctor_actual_child_preserves_slot]) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 prepared.vs_memory` by
    (irule ctor_actual_registered_window >>
     qexistsl [`ctor_actual_sites func child`,
       `[(d+32+j*type_memory_size tv,type_memory_size tv)]`] >>
     asm_simp_tac bool_ss [] >> conj_tac
     >- (rpt strip_tac >> irule (cj 2 ctor_actual_sites_scratch_contained) >>
         goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
         qexistsl [`child`, `D`, `func`, `ids`, `N`] >>
         asm_simp_tac bool_ss [] >>
         qpat_x_assum `d+32+j*type_memory_size tv <= D+N` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] prepared t` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  asm_simp_tac bool_ss [TAKE_SUC, TAKE1_DROP] >>
  conj_tac >- simp[] >>
  conj_tac >- fs[mload_def, mem_bytes_at_def] >>
  conj_tac >- fs[abi_encoder_registered_effect_def] >>
  reverse conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  rpt strip_tac >>
  `lookup_var x prepared = SOME w` by metis_tac[] >>
  `not_fresh_at middle x` by
    (fs[abi_decoder_older_vars_def, not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem ctor_actual_array_observation_backedge_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var ==>
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) (SUC j)
    (jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s)))
Proof
  simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `t = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString nv),n2w (SUC j)) /\
   t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `abi_decode_frame slot 32 s t` by
    (simp[abi_decode_frame_def, Abbr `t`, jump_to_def, update_var_def] >>
     rpt strip_tac >> irule EQ_TRANS >>
     irule_at Any mstore_mem_bytes_at_disjoint >> simp[]) >>
  `all_have_type tv (TAKE (SUC j) vs)` by
    (fs[all_have_type_EVERY] >> irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
  `SUC j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
    simp[LE_MULT_RCANCEL, LENGTH_TAKE] >>
  `elems_in_memory (TAKE (SUC j) vs) (d+32) tv t.vs_memory` by
    (irule abi_decode_frame_preserves_elements >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`s`, `slot`, `32`] >>
     full_simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >>
     asm_simp_tac bool_ss [LENGTH_TAKE] >> decide_tac) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (qpat_x_assum `abi_decode_frame slot 32 s t` mp_tac >>
     simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
     first_x_assum irule >>
     fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mload d t = mload d s` by
    (qpat_x_assum `mem_bytes_at d 32 _ = _` mp_tac >>
     simp_tac bool_ss [mem_bytes_at_def, mload_def, LET_THM] >>
     disch_then SUBST1_TAC >> REFL_TAC) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s t` by
    (`abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s
       (mstore slot (n2w (SUC j)) s)` by
       (irule abi_encoder_registered_slot_store >> qexists `slot_id` >> simp[]) >>
     pop_assum mp_tac >>
     simp[Abbr `t`, jump_to_def, abi_encoder_registered_effect_def,
       update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  `alloca_inv t = alloca_inv s /\
   alloca_frontier_inv_from k ctx func site t = alloca_frontier_inv_from k ctx func site s /\
   ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx` by
    simp_tac (srw_ss()) [LET_THM, Abbr `t`, jump_to_def, mstore_def, update_var_def,
      write_memory_with_expansion_def, alloca_inv_def, allocas_non_overlapping_def,
      alloca_next_valid_def, alloca_frontier_inv_from_def, remaining_alloca_budget_def,
      ctor_actual_scratch_def] >>
  `mload slot t = n2w (SUC j)` by
    (simp[Abbr `t`, abi_decode_mload_jump,
       venomMemProofsTheory.mload_mstore_same_proof]) >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >>
      `lookup_var x s = SOME w` by metis_tac[] >>
      `abi_decoder_operand_live nv (Var x)` by
        (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF] >>
         metis_tac[LESS_EQ_TRANS]) >>
      qpat_x_assum `!op. _` (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def]) >>
  irule abi_encoder_registered_effect_trans >> qexists `s` >>
  asm_simp_tac bool_ss []
QED
