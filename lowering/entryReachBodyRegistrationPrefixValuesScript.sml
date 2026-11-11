Theory entryReachBodyRegistrationPrefixValues
Ancestors
  valueEncodingDefs entryReachBodyRegistrationSingleton entryReachBodyCanonicalArrayChild
  abiDecoderReentry abiEncoderRegisteredEffect abiEncoderWindowContract
  abiDecoderAllocation compileEnv venomState finite_map pred_set arithmetic

Theorem registration_prefix_value:
  array_child_result ctx fn k root extent ambient
    (window_alloca_sites fn (abi_decoder_ids lo hi)) b cap site limit
    first last cell tv value ready t /\
  old_id < k /\ k < lo /\
  FLOOKUP initial.vs_allocas old_id = SOME (old_root,old_extent) /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) /\
  ready.vs_memory = initial.vs_memory /\
  old_root <= p /\ p + type_memory_size old_tv <= old_root + old_extent /\
  val_in_memory old_tv old_value p initial.vs_memory /\ val_wf old_tv old_value ==>
  val_in_memory old_tv old_value p t.vs_memory
Proof
  strip_tac >>
  `old_id <> k` by decide_tac >>
  `old_id NOTIN window_alloca_sites fn (abi_decoder_ids lo hi)` by
    (simp[window_alloca_sites_def, abi_decoder_ids_def] >> decide_tac) >>
  irule registration_result_previous_value >>
  simp[] >>
  qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> simp[] >>
  qexistsl_tac [`old_root`, `old_id`, `old_extent`] >> simp[]
QED

Theorem registration_prefix_allocation:
  array_child_result ctx fn k root extent ambient ids b cap site limit
    first last cell tv value ready t /\
  FLOOKUP initial.vs_allocas old_id = SOME entry /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) ==>
  FLOOKUP t.vs_allocas old_id = SOME entry
Proof
  strip_tac >>
  `FLOOKUP ready.vs_allocas old_id = SOME entry` by metis_tac[] >>
  fs[array_child_result_def] >>
  metis_tac[abi_encoder_registered_effect_allocated]
QED

Theorem registration_prefix_operand:
  array_child_result ctx fn k root extent ambient ids b cap site limit
    first last cell tv value ready t /\
  next <= first.cs_next_var /\
  (!op. abi_decoder_operand_live next op ==>
    eval_operand op ready = eval_operand op initial) /\
  abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
  eval_operand op t = SOME w
Proof
  strip_tac >>
  `abi_decoder_operand_live first.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `eval_operand op ready = SOME w` by metis_tac[] >>
  fs[array_child_result_def] >> metis_tac[]
QED
