(* Registered footprints preserve completed disjoint output windows. *)
Theory ctorAbiActualMemory
Ancestors
  ctorAbiActualFrame abiEncoderPrimitiveEffect valueEncodingProps
  venomExecSemantics allocaBudgetProps
  abiEncoderRegisteredEffect venomMemDefs allocaFrontierBound venomState
  list arithmetic finite_map pred_set abiEncoderZeroFrame

Theorem ctor_actual_registered_window:
  abi_encoder_registered_effect ids outs s t /\
  (!a. p <= a /\ a < p+n ==>
    EVERY (\(b,k). a < b \/ b+k <= a) outs) /\
  (!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    regions_disjoint (p,n) (b,sz)) ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  irule abi_encoder_mem_bytes_singletons >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  `regions_disjoint (p,n) (b,sz)` by metis_tac[] >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Theorem ctor_actual_registered_value:
  abi_encoder_registered_effect ids outs s t /\
  val_in_memory tv v p s.vs_memory /\ val_wf tv v /\
  (!a. p <= a /\ a < p + type_memory_size tv ==>
    EVERY (\(b,k). a < b \/ b+k <= a) outs) /\
  (!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    regions_disjoint (p,type_memory_size tv) (b,sz)) ==>
  val_in_memory tv v p t.vs_memory
Proof
  strip_tac >> irule val_in_memory_mem_agree >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
  irule EQ_SYM >> irule ctor_actual_registered_window >>
  qexistsl [`ids`, `outs`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem ctor_actual_child_effect:
  abi_encoder_registered_effect child [(c,k)] s t /\ child SUBSET ids /\
  d <= c /\ c+k <= d+n ==>
  abi_encoder_registered_effect ids [(d,n)] s t
Proof
  strip_tac >> irule abi_encoder_registered_effect_enlarge >>
  qexistsl [`child`, `[(c,k)]`] >> simp[] >> rpt strip_tac >> decide_tac
QED

Theorem ctor_actual_store_observations[simp]:
  (mstore p w s).vs_data_section = s.vs_data_section /\
  (mstore p w s).vs_call_ctx = s.vs_call_ctx /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (alloca_frontier_inv ctx fn site (mstore p w s) <=>
    alloca_frontier_inv ctx fn site s)
Proof
  simp[mstore_def, write_memory_with_expansion_def,
    alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

Theorem ctor_actual_update_var_observations[simp]:
  (update_var x w s).vs_data_section = s.vs_data_section /\
  (update_var x w s).vs_call_ctx = s.vs_call_ctx /\
  (update_var x w s).vs_memory = s.vs_memory /\
  (update_var x w s).vs_allocas = s.vs_allocas /\
  (update_var x w s).vs_alloca_next = s.vs_alloca_next /\
  (alloca_frontier_inv ctx fn site (update_var x w s) <=>
    alloca_frontier_inv ctx fn site s)
Proof
  simp[update_var_def, alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

Theorem ctor_actual_index_frontier[simp]:
  alloca_frontier_inv ctx fn site (s with vs_inst_idx := ix) <=>
  alloca_frontier_inv ctx fn site s
Proof
  simp[alloca_frontier_inv_def, remaining_alloca_budget_def]
QED
