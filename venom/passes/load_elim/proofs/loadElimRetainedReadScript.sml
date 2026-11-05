Theory loadElimRetainedRead
Ancestors
  loadElimAbsoluteKey loadElimKeyReadOperational loadElimKeyRead loadElimBPEmpty
  loadElimDefs basePtrDefs memLocDefs memAliasDefs memAliasProps
  venomState venomEffects venomMemDefs words finite_map pred_set
  mem2varBlockSimHelpers deadStoreElimProofs

Theorem le_invalidate_retained_locations:
  k IN FDOM (load_invalidate aliases bp space ll wk) ==>
  load_key_to_memloc bp space wk <> ml_undefined /\
  load_key_to_memloc bp space k <> ml_undefined /\
  ~ma_may_alias aliases (load_key_to_memloc bp space k)
                       (load_key_to_memloc bp space wk)
Proof
  simp[load_invalidate_def] >> IF_CASES_TAC >> simp[FDOM_DRESTRICT]
QED

Theorem le_empty_absolute_key_location:
  (!v. bp_get_ptrs bp v = []) /\ le_absolute_key space k /\
  load_key_to_memloc bp space k <> ml_undefined ==>
  (load_key_to_memloc bp space k).ml_alloca = NONE /\
  (load_key_to_memloc bp space k).ml_size = SOME (addr_space_word_scale space)
Proof
  strip_tac >> Cases_on `k`
  >> gvs[le_absolute_key_def, load_key_to_memloc_def]
  >> rename1 `operand_to_memloc bp space op` >> Cases_on `op`
  >> gvs[operand_to_memloc_def]
  >> `bp_ptr_from_op bp (Var s) = NONE` by metis_tac[le_bp_empty_ptr_from_op]
  >> simp[bp_segment_from_ops_def]
  >> Cases_on `space` >> simp[addr_space_word_scale_def, dimword_def]
QED

Theorem le_empty_absolute_key_fixed_address:
  (!v. bp_get_ptrs bp v = []) /\ le_absolute_key space k /\
  IS_SOME (load_key_to_memloc bp space k).ml_offset /\
  le_key_address space k s = SOME a ==>
  (load_key_to_memloc bp space k).ml_offset = SOME a /\ a < dimword (:256)
Proof
  strip_tac >> reverse (Cases_on `k`)
  >- (gvs[le_absolute_key_def, load_key_to_memloc_def,
          le_key_address_def, memloc_runtime_region_def])
  >> rename1 `LK_Op op` >> Cases_on `op`
  >> gvs[operand_to_memloc_def, load_key_to_memloc_def,
         le_key_address_def, eval_operand_def, w2n_lt, ml_undefined_def]
  >> `bp_ptr_from_op bp (Var s') = NONE` by metis_tac[le_bp_empty_ptr_from_op]
  >> gvs[bp_segment_from_ops_def]
QED

Theorem le_retained_absolute_disjoint:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key space k /\ le_absolute_key space wk /\
  k IN FDOM (load_invalidate aliases bp space ll wk) /\
  le_key_address space k s = SOME a /\ le_key_address space wk s = SOME b ==>
  regions_disjoint (a,addr_space_word_scale space) (b,addr_space_word_scale space) /\
  a < dimword (:256) /\ b < dimword (:256)
Proof
  strip_tac >> drule le_invalidate_retained_locations >> strip_tac
  >> `(load_key_to_memloc bp space k).ml_alloca = NONE /\
      (load_key_to_memloc bp space k).ml_size = SOME (addr_space_word_scale space)`
       by metis_tac[le_empty_absolute_key_location]
  >> `(load_key_to_memloc bp space wk).ml_alloca = NONE /\
      (load_key_to_memloc bp space wk).ml_size = SOME (addr_space_word_scale space)`
       by metis_tac[le_empty_absolute_key_location]
  >> drule ma_may_alias_iff >> strip_tac >> fs[]
  >> `addr_space_word_scale space <> 0` by
       (Cases_on `space` >> simp[addr_space_word_scale_def])
  >> `IS_SOME (load_key_to_memloc bp space k).ml_offset /\
      IS_SOME (load_key_to_memloc bp space wk).ml_offset` by
       (Cases_on `(load_key_to_memloc bp space k).ml_offset` >>
        Cases_on `(load_key_to_memloc bp space wk).ml_offset` >> gvs[may_overlap_def])
  >> `(load_key_to_memloc bp space k).ml_offset = SOME a /\ a < dimword (:256)`
       by metis_tac[le_empty_absolute_key_fixed_address]
  >> `(load_key_to_memloc bp space wk).ml_offset = SOME b /\ b < dimword (:256)`
       by metis_tac[le_empty_absolute_key_fixed_address]
  >> gvs[may_overlap_def, regions_disjoint_def]
QED

Theorem le_retained_memory_content:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key AddrSp_Memory k /\ le_absolute_key AddrSp_Memory wk /\
  k IN FDOM (load_invalidate aliases bp AddrSp_Memory ll wk) /\
  le_key_address AddrSp_Memory k s = SOME a /\
  le_key_address AddrSp_Memory wk s = SOME b ==>
  le_read_address AddrSp_Memory a (mstore b value s) = le_read_address AddrSp_Memory a s
Proof
  strip_tac >> drule_all le_retained_absolute_disjoint
  >> simp[regions_disjoint_def, addr_space_word_scale_def] >> strip_tac
  >> simp[] >> irule mem2varBlockSimHelpersTheory.mload_mstore_disjoint >> simp[]
QED

Theorem le_retained_storage_content:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key AddrSp_Storage k /\ le_absolute_key AddrSp_Storage wk /\
  k IN FDOM (load_invalidate aliases bp AddrSp_Storage ll wk) /\
  le_key_address AddrSp_Storage k s = SOME a /\
  le_key_address AddrSp_Storage wk s = SOME b ==>
  le_read_address AddrSp_Storage a (sstore (n2w b) value s) = le_read_address AddrSp_Storage a s
Proof
  strip_tac >> drule_all le_retained_absolute_disjoint
  >> simp[regions_disjoint_def, addr_space_word_scale_def] >> strip_tac
  >> simp[] >> irule deadStoreElimProofsTheory.sload_sstore_disjoint
  >> simp[n2w_11] >> decide_tac
QED

Theorem le_retained_transient_content:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key AddrSp_Transient k /\ le_absolute_key AddrSp_Transient wk /\
  k IN FDOM (load_invalidate aliases bp AddrSp_Transient ll wk) /\
  le_key_address AddrSp_Transient k s = SOME a /\
  le_key_address AddrSp_Transient wk s = SOME b ==>
  le_read_address AddrSp_Transient a (tstore (n2w b) value s) = le_read_address AddrSp_Transient a s
Proof
  strip_tac >> drule_all le_retained_absolute_disjoint
  >> simp[regions_disjoint_def, addr_space_word_scale_def] >> strip_tac
  >> simp[] >> irule deadStoreElimProofsTheory.tload_tstore_disjoint
  >> simp[n2w_11] >> decide_tac
QED

Theorem le_retained_memory_key_read:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key AddrSp_Memory k /\ le_absolute_key AddrSp_Memory wk /\
  k IN FDOM (load_invalidate aliases bp AddrSp_Memory ll wk) /\
  le_key_address AddrSp_Memory wk s = SOME b /\
  le_key_address AddrSp_Memory k (mstore b value s) = le_key_address AddrSp_Memory k s ==>
  le_key_read AddrSp_Memory k (mstore b value s) = le_key_read AddrSp_Memory k s
Proof
  strip_tac >> irule le_key_read_transport >> simp[]
  >> rpt strip_tac >> drule_all le_retained_memory_content >> simp[]
QED

Theorem le_retained_storage_key_read:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key AddrSp_Storage k /\ le_absolute_key AddrSp_Storage wk /\
  k IN FDOM (load_invalidate aliases bp AddrSp_Storage ll wk) /\
  le_key_address AddrSp_Storage wk s = SOME b /\
  le_key_address AddrSp_Storage k (sstore (n2w b) value s) = le_key_address AddrSp_Storage k s ==>
  le_key_read AddrSp_Storage k (sstore (n2w b) value s) = le_key_read AddrSp_Storage k s
Proof
  strip_tac >> irule le_key_read_transport >> simp[]
  >> rpt strip_tac >> drule_all le_retained_storage_content >> simp[]
QED

Theorem le_retained_transient_key_read:
  wf_alias_sets aliases /\ (!v. bp_get_ptrs bp v = []) /\
  le_absolute_key AddrSp_Transient k /\ le_absolute_key AddrSp_Transient wk /\
  k IN FDOM (load_invalidate aliases bp AddrSp_Transient ll wk) /\
  le_key_address AddrSp_Transient wk s = SOME b /\
  le_key_address AddrSp_Transient k (tstore (n2w b) value s) = le_key_address AddrSp_Transient k s ==>
  le_key_read AddrSp_Transient k (tstore (n2w b) value s) = le_key_read AddrSp_Transient k s
Proof
  strip_tac >> irule le_key_read_transport >> simp[]
  >> rpt strip_tac >> drule_all le_retained_transient_content >> simp[]
QED
