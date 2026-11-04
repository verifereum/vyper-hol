Theory loadElimKeyReadOperational
Ancestors
  loadElimKeyRead memAliasProps mem2varBlockSimHelpers deadStoreElimProofs
  venomMemDefs venomEffects words venomInstProps
  basePtrDefs memLocDefs venomState memoryCopyElisionSound

Theorem le_memory_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Memory) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Memory) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Memory a (mstore b value s) =
  le_read_address AddrSp_Memory a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule mload_mstore_disjoint >> simp[]
QED

Theorem le_storage_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Storage) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Storage) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Storage a (sstore (n2w b) value s) =
  le_read_address AddrSp_Storage a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule sload_sstore_disjoint >>
  simp[n2w_11] >> decide_tac
QED

Theorem le_transient_read_nonalias_store:
  wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
  allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
  memloc_within_alloca writeloc s /\
  memloc_runtime_region readloc s = SOME (a,addr_space_word_scale AddrSp_Transient) /\
  memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale AddrSp_Transient) /\
  a < dimword (:256) /\ b < dimword (:256) ==>
  le_read_address AddrSp_Transient a (tstore (n2w b) value s) =
  le_read_address AddrSp_Transient a s
Proof
  strip_tac >> drule_all ma_may_alias_sound >>
  simp[regions_disjoint_def, addr_space_word_scale_def] >>
  strip_tac >> simp[] >> irule tload_tstore_disjoint >>
  simp[n2w_11] >> decide_tac
QED

Theorem le_calldata_read_step_nonterminator:
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode ==>
  le_read_address AddrSp_Calldata a t = le_read_address AddrSp_Calldata a s
Proof
  strip_tac >> drule_all step_preserves_call_ctx >> simp[]
QED

Theorem le_data_read_step_nonterminator:
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode ==>
  le_read_address AddrSp_Data a t = le_read_address AddrSp_Data a s
Proof
  strip_tac >> drule_all step_preserves_data_section >> simp[]
QED

Theorem le_fixed_segment_runtime_word:
  bp_ptr_sound bp s /\ allocas_in_word s /\
  bp_segment_from_ops bp ops = ml /\ ml_is_fixed ml /\
  ops.iao_max_size = SOME (Lit (n2w (addr_space_word_scale space))) /\
  eval_operand ops.iao_ofst s = SOME w /\ memloc_within_alloca ml s ==>
  memloc_runtime_region ml s = SOME (w2n w, addr_space_word_scale space)
Proof
  strip_tac >>
  `addr_space_word_scale space < dimword (:256)` by
    (Cases_on `space` >> simp[addr_space_word_scale_def, dimword_def]) >>
  `IS_SOME (eval_operand ops.iao_ofst s)` by simp[] >>
  drule_all bp_segment_from_ops_runtime_region >>
  strip_tac >>
  Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, ml_is_fixed_def, ml_undefined_def,
      memloc_runtime_region_def, eval_operand_def] >>
  rename1 `bp_ptr_from_op bp (Var v)` >>
  Cases_on `bp_ptr_from_op bp (Var v)` >> gvs[] >>
  rename1 `bp_ptr_from_op bp (Var v) = SOME ptr` >>
  Cases_on `ptr` >> gvs[] >>
  rename1 `bp_ptr_from_op bp (Var v) = SOME (Ptr alloc off)` >> Cases_on `off` >> gvs[] >>
  Cases_on `alloc` >>
  gvs[memloc_within_alloca_def] >>
  rename1 `FLOOKUP s.vs_allocas aid` >>
  Cases_on `FLOOKUP s.vs_allocas aid` >> gvs[] >>
  fs[allocas_in_word_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME region` >>
  PairCases_on `region` >>
  first_x_assum drule >> simp[] >> decide_tac
QED
