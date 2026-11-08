(* Shifted persistent observations; Ok is an ML abbreviation, not a definition. *)
Theory ctorDeployLoweringEntryArrayFrame
Ancestors
  valueEncodingDefs
  ctorDeployLoweringEntryAllocation ctorAbiActualArrayContext
  ctorAbiActualArrayInvariant ctorAbiActualArrayEntry ctorDeployMemoryFrontier
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiEncoderRegisteredEffect
  ctorAbiActualFrame ctorAbiActualSites
  allocaBudgetProps allocaFrontierBound valueEncoding valueEncodingProps
  venomMemDefs venomState venomExecSemantics compileEnv finite_map list words
  arithmetic pred_set

val Ok = ``\k ctx func site ids D N d outsz next limit_st
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
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem deploy_ctor_shifted_frontier_bound:
  alloca_frontier_inv_from k ctx func site s /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  s.vs_alloca_next < dimword (:256)
Proof
  simp[alloca_frontier_inv_from_def] >> strip_tac >> decide_tac
QED

Theorem deploy_ctor_array_observation_operand:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
  eval_operand op s = SOME w
Proof
  BETA_TAC >> strip_tac >> Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, eval_operand_def] >>
  first_x_assum irule >> fs[IN_DEF]
QED

Theorem deploy_ctor_array_observation_ranges:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  abi_decoder_ranges DLOAD hi src dst sb len d outsz b cap initial ==>
  abi_decoder_ranges DLOAD hi src dst sb len d outsz b cap s
Proof
  BETA_TAC >> strip_tac >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op s = SOME w` by
    (rpt gen_tac >> Cases_on `op` >>
     simp[abi_decoder_operand_live_def, eval_operand_def] >>
     rpt strip_tac >> first_x_assum irule >> fs[IN_DEF]) >>
  fs[abi_decoder_ranges_def] >> metis_tac[]
QED

Theorem deploy_ctor_array_allocation_state:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv_from k ctx func site t <=>
   alloca_frontier_inv_from k ctx func site s) /\
  (ctor_actual_scratch func ids D N t <=> ctor_actual_scratch func ids D N s)
Proof
  strip_tac >>
  simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_from_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
  asm_rewrite_tac[]
QED

Theorem deploy_ctor_array_observation_exit:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) s ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  BETA_TAC >> simp[val_in_memory_dynarray, mem_word_at_eq_mload]
QED

Theorem deploy_ctor_array_observation_self:
  (^Ok) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor s ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot s prefix cursor s
Proof
  BETA_TAC >> strip_tac >> simp[abi_encoder_registered_effect_refl]
QED

Theorem deploy_ctor_array_observation_rebase:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot prepared prefix cursor s /\
  earlier <= next /\
  prepared.vs_data_section = initial.vs_data_section /\
  prepared.vs_call_ctx = initial.vs_call_ctx /\
  prepared.vs_labels = initial.vs_labels /\
  prepared.vs_gas_readings = initial.vs_gas_readings /\
  prepared.vs_code = initial.vs_code /\
  (!x w. abi_decoder_older_vars earlier x /\ lookup_var x initial = SOME w ==>
    lookup_var x prepared = SOME w) /\
  abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial prepared ==>
  (^Ok) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor s
Proof
  BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial s` by
    (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_older_vars next x` by
    (fs[abi_decoder_older_vars_def, IN_DEF] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem deploy_ctor_array_observation_compose:
  (^Ok) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot prepared prefix cursor final ==>
  (^Ok) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor final
Proof
  strip_tac >> irule deploy_ctor_array_observation_rebase >>
  qexistsl [`next`, `prepared`] >> fs[]
QED

Theorem deploy_ctor_array_observation_setup_inputs:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_operand_live next ip /\ eval_operand ip initial = SOME (n2w slot) /\
  mem_bytes_at sb len initial.vs_data_section = bytes ==>
  eval_operand ip s = SOME (n2w slot) /\
  mload (w2n (n2w slot : bytes32)) s = n2w cursor /\
  mem_bytes_at sb len s.vs_data_section = bytes
Proof
  BETA_TAC >> strip_tac >>
  `eval_operand ip s = SOME (n2w slot)` by
    (Cases_on `ip` >> gvs[abi_decoder_operand_live_def, eval_operand_def] >>
     first_x_assum irule >> fs[IN_DEF]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule_all deploy_ctor_shifted_frontier_bound >> simp[]) >>
  `slot + 32 <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `slot < dimword (:256)` by decide_tac >> simp[]
QED

Theorem deploy_ctor_array_zero_prefix_memory:
  elems_in_memory (TAKE 0 vs) (d+32) tv s.vs_memory
Proof
  simp[Once val_in_memory_def]
QED

Theorem deploy_ctor_array_zero_terminal_memory:
  mload d s = 0w ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV [])) d s.vs_memory
Proof
  simp[val_in_memory_dynarray, mem_word_at_eq_mload, Once val_in_memory_def]
QED
