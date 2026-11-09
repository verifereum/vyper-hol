(* Pure ambient-output and actual registered scratch observations. *)
Theory ctorAbiActualFrame
Ancestors
  actualAllocExec actualDecoderSites abiDecoderReentry
  abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps venomMemDefs
  venomState venomInst finite_map pred_set list arithmetic

Definition ctor_actual_scratch_def:
  ctor_actual_scratch fn ids d n (s:venom_state) <=>
    !inst b sz.
      MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN ids /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ regions_disjoint (d,n) (b,sz)
End

Theorem ctor_actual_scratch_restrict:
  ctor_actual_scratch fn ids d n s /\ child SUBSET ids ==>
  ctor_actual_scratch fn child d n s
Proof
  simp[ctor_actual_scratch_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ctor_actual_region_contained:
  d <= c /\ c + k <= d + n /\ regions_disjoint (d,n) (b,sz) ==>
  regions_disjoint (c,k) (b,sz)
Proof
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem ctor_actual_scratch_subregion:
  ctor_actual_scratch fn ids d n s /\ d <= c /\ c + k <= d + n ==>
  ctor_actual_scratch fn ids c k s
Proof
  simp_tac bool_ss [ctor_actual_scratch_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule ctor_actual_region_contained >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_actual_scratch_prune[simp]:
  ctor_actual_scratch fn ids d n (abi_decoder_prune_vars next s) <=>
  ctor_actual_scratch fn ids d n s
Proof
  simp[ctor_actual_scratch_def, abi_decoder_prune_vars_def]
QED

Theorem ctor_actual_prune_observations[simp]:
  (abi_decoder_prune_vars next s).vs_allocas = s.vs_allocas /\
  (abi_decoder_prune_vars next s).vs_alloca_next = s.vs_alloca_next /\
  (abi_decoder_prune_vars next s).vs_memory = s.vs_memory /\
  (abi_decoder_prune_vars next s).vs_data_section = s.vs_data_section /\
  (abi_decoder_prune_vars next s).vs_call_ctx = s.vs_call_ctx
Proof
  simp[abi_decoder_prune_vars_def]
QED

Theorem ctor_actual_prune_alloca_inv[simp]:
  alloca_inv (abi_decoder_prune_vars next s) <=> alloca_inv s
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem ctor_actual_prune_frontier_inv[simp]:
  alloca_frontier_inv ctx fn site (abi_decoder_prune_vars next s) <=>
  alloca_frontier_inv ctx fn site s
Proof
  simp[alloca_frontier_inv_def, remaining_alloca_budget_def,
       abi_decoder_prune_vars_def]
QED

Theorem ctor_actual_registered_effect_prune[simp]:
  abi_encoder_registered_effect ids outs
    (abi_decoder_prune_vars first s) (abi_decoder_prune_vars last t) <=>
  abi_encoder_registered_effect ids outs s t
Proof
  simp[abi_encoder_registered_effect_def, abi_decoder_prune_vars_def]
QED

Theorem ctor_actual_live_eval:
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op (abi_decoder_prune_vars next s) = SOME w
Proof
  simp[abi_decoder_prune_eval]
QED
