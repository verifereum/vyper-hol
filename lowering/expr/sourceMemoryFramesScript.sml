(* TOP-LEVEL: private typed copies preserve source-state and live-local
   relations when their destination misses the live source values.
   Helpers separate external state, typed RAM and allocator backing. *)
Theory sourceMemoryFrames
Ancestors
  allocationGrowth sourceValueFrames localPtrsProps valueLoadProps memoryValueTyping
  typedStoreFrames typedSArrayDynInvariant abiStateFrame abiFieldOperands
  compileEnv valueEncoding memoryValueDefs vyperTypeEnv vyperTypeInvariants
  venomState venomExecSemantics finite_map list words arithmetic

Definition source_memory_separated_def:
  source_memory_separated cenv scopes before dst byte_count <=>
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      compileEnv$regions_disjoint offset (type_memory_size entry.type) dst byte_count) /\
    (!name entry p region_size ptr_addr. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\
      lookup_var p before = SOME ptr_addr ==>
      compileEnv$regions_disjoint (w2n ptr_addr) (type_memory_size entry.type) dst byte_count)
End

Theorem source_pointer_lifetimes_mono:
  !cenv scopes bound next_var.
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    bound <= next_var ==>
    !name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before next_var (Var p)
Proof
  rpt gen_tac >> strip_tac >> MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`] >> strip_tac >>
  `abi_operand_before bound (Var p)` by
    (qpat_x_assum `!name entry p region_size. _` (qspecl_then [`name`, `entry`, `p`, `region_size`] mp_tac) >> simp[]) >>
  irule abi_operand_before_mono >> qexists_tac `bound` >> simp[]
QED

Theorem source_memory_separated_frame:
  !cenv scopes before after dst byte_count.
    source_memory_separated cenv scopes before dst byte_count /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    source_memory_separated cenv scopes after dst byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_memory_separated _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_memory_separated_def]) >>
  simp_tac bool_ss [source_memory_separated_def] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
  `lookup_var p after = lookup_var p before` by
    (qpat_x_assum `!name entry p region_size. _ ==> lookup_var p after = lookup_var p before`
       (qspecl_then [`name`, `entry`, `p`, `region_size`] mp_tac) >> simp[]) >>
  qpat_x_assum `!name entry p region_size ptr_addr. _`
    (qspecl_then [`name`, `entry`, `p`, `region_size`, `ptr_addr`] mp_tac) >> gvs[]
QED

Theorem abi_state_frame_source_fields:
  !before after. abi_state_frame before after ==>
    after.vs_data_section = before.vs_data_section /\ after.vs_tx_ctx = before.vs_tx_ctx /\
    after.vs_block_ctx = before.vs_block_ctx
Proof
  simp_tac (srw_ss()) [abi_state_frame_def, abi_state_context_def, venom_state_component_equality] >>
  rpt strip_tac >> simp[]
QED

Theorem state_rel_simple_external_vars_frame:
  !cenv cx es before after.
    state_rel_simple cenv cx es before /\ vars_rel cenv es.scopes after /\ abi_state_frame before after ==>
    state_rel_simple cenv cx es after
Proof
  rpt gen_tac >> strip_tac >> drule abi_state_frame_observables >> strip_tac >>
  drule abi_state_frame_source_fields >> strip_tac >>
  fs[state_rel_simple_def, storage_rel_def, transient_rel_def, immutables_rel_def,
    logs_rel_def, call_ctx_rel_def, contract_storage_def, contract_transient_def]
QED

Theorem source_memloc_copy_frame:
  !cenv scopes before after ftv copy_count dst name entry offset region_size.
    EVERY scope_well_typed scopes /\ vars_rel cenv scopes before /\
    source_memory_separated cenv scopes before dst (copy_count * type_memory_size ftv) /\
    array_copy_frame ftv copy_count dst before.vs_memory after.vs_memory /\
    lookup_scopes name scopes = SOME entry /\ FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
    memory_value_rel entry.type entry.value offset after.vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  drule_all vars_rel_memloc_value >> DISCH_TAC >>
  `compileEnv$regions_disjoint offset (type_memory_size entry.type) dst (copy_count * type_memory_size ftv)` by
    (qpat_x_assum `source_memory_separated _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [source_memory_separated_def]) >>
     disch_then (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`ftv`, `entry.type`, `entry.value`, `copy_count`, `dst`, `offset`,
    `before.vs_memory`, `after.vs_memory`] array_copy_frame_source) >>
  impl_tac >- fs[compileEnvTheory.regions_disjoint_def] >> simp[]
QED

Theorem vars_rel_copy_frame:
  !cenv scopes before after ftv copy_count dst.
    EVERY scope_well_typed scopes /\ vars_rel cenv scopes before /\
    source_memory_separated cenv scopes before dst (copy_count * type_memory_size ftv) /\
    array_copy_frame ftv copy_count dst before.vs_memory after.vs_memory ==>
    vars_rel cenv scopes after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [vars_rel_def] >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
  drule_all source_memloc_copy_frame >> simp[]
QED

Theorem source_ptrvar_copy_frame:
  !cenv scopes before after ftv copy_count dst name entry p region_size ptr_addr.
    EVERY scope_well_typed scopes /\
    source_memory_separated cenv scopes before dst (copy_count * type_memory_size ftv) /\
    array_copy_frame ftv copy_count dst before.vs_memory after.vs_memory /\
    lookup_scopes name scopes = SOME entry /\ FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\
    lookup_var p before = SOME ptr_addr /\ memory_value_rel entry.type entry.value (w2n ptr_addr) before.vs_memory ==>
    memory_value_rel entry.type entry.value (w2n ptr_addr) after.vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  `compileEnv$regions_disjoint (w2n ptr_addr) (type_memory_size entry.type) dst (copy_count * type_memory_size ftv)` by
    (qpat_x_assum `source_memory_separated _ _ _ _ _`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [source_memory_separated_def]) >>
     disch_then (qspecl_then [`name`, `entry`, `p`, `region_size`, `ptr_addr`] mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`ftv`, `entry.type`, `entry.value`, `copy_count`, `dst`, `w2n (ptr_addr:bytes32)`,
    `before.vs_memory`, `after.vs_memory`] array_copy_frame_source) >>
  impl_tac >- fs[compileEnvTheory.regions_disjoint_def] >> simp[]
QED

Theorem local_ptrs_rel_copy_frame:
  !func cenv scopes before after ftv copy_count dst bound.
    EVERY scope_well_typed scopes /\ local_ptrs_rel func cenv scopes before /\
    allocation_growth before after /\
    source_memory_separated cenv scopes before dst (copy_count * type_memory_size ftv) /\
    array_copy_frame ftv copy_count dst before.vs_memory after.vs_memory /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    local_ptrs_rel func cenv scopes after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`bound`, `cenv`, `scopes`, `before`, `after`] local_pointer_operands_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qpat_x_assum `allocation_growth _ _` (strip_assume_tac o REWRITE_RULE [allocation_growth_def]) >>
  irule local_ptrs_rel_frame >> qexists_tac `before` >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC,
    MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
      drule_all source_ptrvar_copy_frame >> simp[]]
QED

Theorem source_relations_copy_frame:
  !func cenv cx es before after ftv copy_count dst bound.
    state_well_typed es /\ state_rel_simple cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
    abi_state_frame before after /\ allocation_growth before after /\
    source_memory_separated cenv es.scopes before dst (copy_count * type_memory_size ftv) /\
    array_copy_frame ftv copy_count dst before.vs_memory after.vs_memory /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    state_rel_simple cenv cx es after /\ local_ptrs_rel func cenv es.scopes after
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY scope_well_typed es.scopes /\ vars_rel cenv es.scopes before` by
    fs[state_well_typed_def, state_rel_simple_def] >>
  `vars_rel cenv es.scopes after` by (drule_all vars_rel_copy_frame >> simp[]) >>
  conj_tac >- (drule_all state_rel_simple_external_vars_frame >> simp[]) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `es.scopes`, `before`, `after`, `ftv`, `copy_count`, `dst`, `bound`]
    local_ptrs_rel_copy_frame) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem vars_rel_memory_eq:
  !cenv scopes before after.
    after.vs_memory = before.vs_memory ==> vars_rel cenv scopes after = vars_rel cenv scopes before
Proof
  simp[vars_rel_def]
QED

Theorem local_ptrs_rel_memory_frame:
  !func cenv scopes before after.
    local_ptrs_rel func cenv scopes before /\ allocation_growth before after /\
    after.vs_memory = before.vs_memory /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    local_ptrs_rel func cenv scopes after
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `allocation_growth _ _` (strip_assume_tac o REWRITE_RULE [allocation_growth_def]) >>
  irule local_ptrs_rel_frame >> qexists_tac `before` >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]
QED

Theorem source_relations_memory_frame:
  !func cenv cx es before after bound.
    state_rel_simple cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
    abi_state_frame before after /\ allocation_growth before after /\ after.vs_memory = before.vs_memory /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    state_rel_simple cenv cx es after /\ local_ptrs_rel func cenv es.scopes after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cenv`, `es.scopes`, `before`, `after`] vars_rel_memory_eq) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  `vars_rel cenv es.scopes after` by fs[state_rel_simple_def] >> conj_tac
  >- (drule_all state_rel_simple_external_vars_frame >> simp[]) >>
  mp_tac (Q.SPECL [`bound`, `cenv`, `es.scopes`, `before`, `after`] local_pointer_operands_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`func`, `cenv`, `es.scopes`, `before`, `after`] local_ptrs_rel_memory_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED
