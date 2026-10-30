(* TOP-LEVEL: ABI writes preserve complete source values and live pointer
   backing when their windows avoid those values. Native Log paths derive
   allocation growth from execution, including successful internal calls. *)
Theory sourceAbiFrames
Ancestors
  sourceMemoryFrames sourceValueFrames sourceLogFrames allocationPathGrowth allocationGrowth localPtrsProps valueLoadProps
  abiFieldValueFrame abiMemoryFrame abiStateFrame abiFieldOperands memoryValueTyping
  compileEnv valueEncoding vyperTypeEnv vyperTypeInvariants vyperState
  fragBlockPath venomState list pair words

Definition source_writes_separated_def:
  source_writes_separated cenv scopes before writes <=>
    EVERY (\(region_base,write_count). write_count = 0 \/
      source_memory_separated cenv scopes before region_base write_count) writes
End

Theorem source_writes_separated_structure[simp]:
  (!cenv scopes before. source_writes_separated cenv scopes before []) /\
  (!cenv scopes before left right.
    source_writes_separated cenv scopes before (left ++ right) <=>
    source_writes_separated cenv scopes before left /\ source_writes_separated cenv scopes before right)
Proof
  simp[source_writes_separated_def, EVERY_APPEND]
QED

Theorem source_writes_memloc:
  !cenv scopes before writes name entry offset region_size.
    source_writes_separated cenv scopes before writes /\ lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
    EVERY (\(region_base,write_count).
      abi_window_separated offset (type_memory_size entry.type) region_base write_count) writes
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`region_base`, `write_count`] >> DISCH_TAC >>
  qpat_x_assum `source_writes_separated _ _ _ _`
    (mp_tac o REWRITE_RULE [source_writes_separated_def, EVERY_MEM]) >>
  disch_then (qspec_then `(region_base,write_count)` mp_tac) >> simp[] >> strip_tac
  >- simp[abi_window_separated_def] >>
  `compileEnv$regions_disjoint offset (type_memory_size entry.type) region_base write_count` by
    (qpat_x_assum `source_memory_separated _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [source_memory_separated_def]) >>
     disch_then (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >> simp[]) >>
  simp[abi_window_separated_def]
QED

Theorem source_writes_ptrvar:
  !cenv scopes before writes name entry p region_size ptr_addr.
    source_writes_separated cenv scopes before writes /\ lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\ lookup_var p before = SOME ptr_addr ==>
    EVERY (\(region_base,write_count).
      abi_window_separated (w2n ptr_addr) (type_memory_size entry.type) region_base write_count) writes
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`region_base`, `write_count`] >> DISCH_TAC >>
  qpat_x_assum `source_writes_separated _ _ _ _`
    (mp_tac o REWRITE_RULE [source_writes_separated_def, EVERY_MEM]) >>
  disch_then (qspec_then `(region_base,write_count)` mp_tac) >> simp[] >> strip_tac
  >- simp[abi_window_separated_def] >>
  `compileEnv$regions_disjoint (w2n ptr_addr) (type_memory_size entry.type) region_base write_count` by
    (qpat_x_assum `source_memory_separated _ _ _ _ _`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [source_memory_separated_def]) >>
     disch_then (qspecl_then [`name`, `entry`, `p`, `region_size`, `ptr_addr`] mp_tac) >> simp[]) >>
  simp[abi_window_separated_def]
QED

Theorem vars_rel_abi_memory_frame:
  !cenv scopes before after writes.
    EVERY scope_well_typed scopes /\ vars_rel cenv scopes before /\
    source_writes_separated cenv scopes before writes /\ abi_memory_frame writes before after ==>
    vars_rel cenv scopes after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [vars_rel_def] >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  drule value_has_type_val_wf >> DISCH_TAC >>
  drule_all vars_rel_memloc_value >> DISCH_TAC >> drule_all source_writes_memloc >> DISCH_TAC >>
  mp_tac (Q.SPECL [`entry.type`, `entry.value`, `offset`, `writes`, `before`, `after`] abi_memory_frame_value) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem source_ptrvar_abi_memory_frame:
  !cenv scopes before after writes name entry p region_size ptr_addr.
    EVERY scope_well_typed scopes /\ source_writes_separated cenv scopes before writes /\
    abi_memory_frame writes before after /\ lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\ lookup_var p before = SOME ptr_addr /\
    memory_value_rel entry.type entry.value (w2n ptr_addr) before.vs_memory ==>
    memory_value_rel entry.type entry.value (w2n ptr_addr) after.vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  drule value_has_type_val_wf >> DISCH_TAC >>
  drule_all source_writes_ptrvar >> DISCH_TAC >>
  mp_tac (Q.SPECL [`entry.type`, `entry.value`, `w2n (ptr_addr:bytes32)`, `writes`, `before`, `after`]
    abi_memory_frame_value) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem local_ptrs_rel_abi_memory_frame:
  !func cenv scopes before after writes bound.
    EVERY scope_well_typed scopes /\ local_ptrs_rel func cenv scopes before /\ allocation_growth before after /\
    source_writes_separated cenv scopes before writes /\ abi_memory_frame writes before after /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg. abi_operand_before bound arg ==> eval_operand arg after = eval_operand arg before) ==>
    local_ptrs_rel func cenv scopes after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`bound`, `cenv`, `scopes`, `before`, `after`] local_pointer_operands_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qpat_x_assum `allocation_growth _ _` (strip_assume_tac o REWRITE_RULE [allocation_growth_def]) >>
  irule local_ptrs_rel_frame >> qexists_tac `before` >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC,
    MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
      drule_all source_ptrvar_abi_memory_frame >> simp[]]
QED

Theorem source_relations_abi_memory_frame:
  !func cenv cx es before after writes bound.
    state_well_typed es /\ state_rel_simple cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
    abi_state_frame before after /\ allocation_growth before after /\
    source_writes_separated cenv es.scopes before writes /\ abi_memory_frame writes before after /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg. abi_operand_before bound arg ==> eval_operand arg after = eval_operand arg before) ==>
    state_rel_simple cenv cx es after /\ local_ptrs_rel func cenv es.scopes after
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY scope_well_typed es.scopes /\ vars_rel cenv es.scopes before` by fs[state_well_typed_def, state_rel_simple_def] >>
  `vars_rel cenv es.scopes after` by (drule_all vars_rel_abi_memory_frame >> simp[]) >>
  conj_tac >- (drule_all state_rel_simple_external_vars_frame >> simp[]) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `es.scopes`, `before`, `after`, `writes`, `bound`] local_ptrs_rel_abi_memory_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem source_relations_native_log_frame:
  !ctx func cenv cx es before after writes events bound.
    state_well_typed es /\ state_rel_simple cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
    alloca_inv before /\ fragment_path ctx func before after /\
    abi_state_frame before (after with vs_logs := before.vs_logs) /\
    source_writes_separated cenv es.scopes before writes /\ abi_memory_frame writes before after /\
    after.vs_logs = before.vs_logs ++ events /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg. abi_operand_before bound arg ==> eval_operand arg after = eval_operand arg before) ==>
    state_rel_simple cenv cx (es with logs := es.logs ++ events) after /\ local_ptrs_rel func cenv es.scopes after
Proof
  rpt gen_tac >> strip_tac >> drule_all fragment_path_allocation_growth >> DISCH_TAC >>
  `EVERY scope_well_typed es.scopes /\ vars_rel cenv es.scopes before` by fs[state_well_typed_def, state_rel_simple_def] >>
  `vars_rel cenv es.scopes after` by (drule_all vars_rel_abi_memory_frame >> simp[]) >>
  conj_tac >- (drule_all state_rel_simple_log_frame >> simp[]) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `es.scopes`, `before`, `after`, `writes`, `bound`] local_ptrs_rel_abi_memory_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED
