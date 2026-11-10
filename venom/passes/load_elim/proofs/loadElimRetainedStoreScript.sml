Theory loadElimRetainedStore
Ancestors
  loadElimTransferRetention loadElimConfiguredGeneration loadElimAbsoluteKey
  loadElimKeyReadOperational loadElimKeyRead loadElimBPEmpty
  loadElimDefs basePtrDefs memLocDefs venomMemDefs venomState
  finite_map pred_set words memAliasProps venomEffects
  venomExecSemantics mem2varBlockSimHelpers deadStoreElimProofs
  loadElimGenerationSound

Theorem le_invalidation_member_nonalias:
  key IN FDOM (load_invalidate aliases bp space ll wk) ==>
  load_key_to_memloc bp space key <> ml_undefined /\
  load_key_to_memloc bp space wk <> ml_undefined /\
  ~ma_may_alias aliases (load_key_to_memloc bp space key)
    (load_key_to_memloc bp space wk)
Proof
  simp[load_invalidate_def] >> IF_CASES_TAC >> simp[FDOM_DRESTRICT] >>
  metis_tac[]
QED

Theorem le_nonalias_absolute_offsets:
  wf_alias_sets sets /\ ~ma_may_alias sets l1 l2 /\
  l1.ml_alloca = NONE /\ l2.ml_alloca = NONE /\
  l1.ml_size <> SOME 0 /\ l2.ml_size <> SOME 0 ==>
  IS_SOME l1.ml_offset /\ IS_SOME l2.ml_offset
Proof
  strip_tac >>
  `~may_overlap l1 l2` by metis_tac[ma_may_alias_iff] >>
  Cases_on `l1.ml_offset` >> Cases_on `l2.ml_offset` >>
  gvs[may_overlap_def]
QED

Theorem le_empty_key_location_fields:
  (!v. bp_get_ptrs bp v = []) /\ le_absolute_key space key ==>
  (load_key_to_memloc bp space key).ml_alloca = NONE /\
  (load_key_to_memloc bp space key).ml_size <> SOME 0
Proof
  strip_tac >> Cases_on `key`
  >- (rename1 `LK_Op op` >>
      `bp_ptr_from_op bp op = NONE` by metis_tac[le_bp_empty_ptr_from_op] >>
      Cases_on `op` >>
      simp[load_key_to_memloc_def, operand_to_memloc_def,
           bp_segment_from_ops_def, ml_undefined_def] >>
      Cases_on `space` >> simp[addr_space_word_scale_def, dimword_def]) >>
  gvs[le_absolute_key_def, load_key_to_memloc_def] >>
  Cases_on `space` >> simp[addr_space_word_scale_def]
QED

Theorem le_empty_key_fixed_runtime:
  (!v. bp_get_ptrs bp v = []) /\ le_absolute_key space key /\
  IS_SOME (load_key_to_memloc bp space key).ml_offset /\
  le_key_address space key s = SOME a ==>
  memloc_runtime_region (load_key_to_memloc bp space key) s =
    SOME (a,addr_space_word_scale space)
Proof
  strip_tac >> Cases_on `key`
  >- (rename1 `LK_Op op` >>
      `bp_ptr_from_op bp op = NONE` by metis_tac[le_bp_empty_ptr_from_op] >>
      Cases_on `op` >>
      gvs[load_key_to_memloc_def, operand_to_memloc_def,
          bp_segment_from_ops_def, ml_undefined_def, le_key_address_def,
          eval_operand_def, memloc_runtime_region_def]) >>
  gvs[le_absolute_key_def, load_key_to_memloc_def,
      le_key_address_def, memloc_runtime_region_def]
QED

Theorem le_retained_store_regions:
  (!v. bp_get_ptrs bp v = []) /\ wf_alias_sets aliases /\
  le_absolute_key space key /\ le_absolute_key space wk /\
  key IN FDOM (load_invalidate aliases bp space ll wk) /\
  le_key_address space key s = SOME a /\
  le_key_address space wk s = SOME b ==>
  regions_disjoint (a,addr_space_word_scale space)
    (b,addr_space_word_scale space)
Proof
  strip_tac >> drule le_invalidation_member_nonalias >> strip_tac >>
  ` (load_key_to_memloc bp space key).ml_alloca = NONE /\
    (load_key_to_memloc bp space key).ml_size <> SOME 0` by
    (irule le_empty_key_location_fields >> simp[]) >>
  ` (load_key_to_memloc bp space wk).ml_alloca = NONE /\
    (load_key_to_memloc bp space wk).ml_size <> SOME 0` by
    (irule le_empty_key_location_fields >> simp[]) >>
  drule_all le_nonalias_absolute_offsets >> strip_tac >>
  `memloc_runtime_region (load_key_to_memloc bp space key) s =
    SOME (a,addr_space_word_scale space)` by
    (irule le_empty_key_fixed_runtime >> simp[]) >>
  `memloc_runtime_region (load_key_to_memloc bp space wk) s =
    SOME (b,addr_space_word_scale space)` by
    (irule le_empty_key_fixed_runtime >> simp[]) >>
  gvs[memloc_runtime_region_def, AllCaseEqs()] >>
  drule ma_may_alias_sound_no_alloca >>
  disch_then (qspecl_then [`load_key_to_memloc bp space key`,
                          `load_key_to_memloc bp space wk`] mp_tac) >> simp[]
QED

Theorem le_store_read_disjoint_step:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] /\ eval_operand addr s = SOME w /\
  step_inst fuel ctx inst s = OK t /\ a < dimword (:256) /\
  regions_disjoint (a,addr_space_word_scale space)
    (w2n w,addr_space_word_scale space) ==>
  le_read_address space a t = le_read_address space a s
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def] >>
  rpt IF_CASES_TAC >> gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[addr_space_word_scale_def]
  >- (irule mload_mstore_disjoint >> gvs[regions_disjoint_def])
  >- (irule sload_sstore_disjoint >> simp[n2w_11] >>
      gvs[regions_disjoint_def] >>
      spose_not_then assume_tac >> gvs[]) >>
  irule tload_tstore_disjoint >> simp[n2w_11] >>
  gvs[regions_disjoint_def] >>
  spose_not_then assume_tac >> gvs[]
QED

Theorem le_retained_store_read_step:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  (!v. bp_get_ptrs bp v = []) /\ le_absolute_key space key /\
  inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  wf_alias_sets aliases /\
  key IN FDOM (load_invalidate aliases bp space ll
    (load_get_write_key bp space norm inst)) /\
  le_key_address space key s = SOME a /\ a < dimword (:256) /\
  step_inst fuel ctx inst s = OK t ==>
  le_read_address space a t = le_read_address space a s
Proof
  strip_tac >>
  `le_absolute_key space (load_get_write_key bp space norm inst)` by
    (irule le_empty_write_key_shape >> simp[] >> metis_tac[]) >>
  `le_key_address space (load_get_write_key bp space norm inst) s =
    SOME (w2n w)` by
    (irule le_empty_write_key_address >> simp[] >> metis_tac[]) >>
  drule_all le_retained_store_regions >> strip_tac >>
  irule le_store_read_disjoint_step >> metis_tac[]
QED

Theorem le_retained_store_key_read_step:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  (!v. bp_get_ptrs bp v = []) /\ le_absolute_key space key /\
  inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  wf_alias_sets aliases /\
  key IN FDOM (load_invalidate aliases bp space ll
    (load_get_write_key bp space norm inst)) /\
  le_key_address space key s = SOME a /\ a < dimword (:256) /\
  step_inst fuel ctx inst s = OK t ==>
  le_key_read space key t = le_key_read space key s
Proof
  strip_tac >>
  drule_all le_retained_store_read_step >> strip_tac >>
  drule_all le_generating_store_state >> strip_tac >>
  `le_key_address space key t = le_key_address space key s` by
    (irule le_absolute_key_same_bindings >> simp[]) >>
  simp[le_key_read_def]
QED
