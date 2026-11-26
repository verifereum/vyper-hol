(* The storage taint bound at the actual endpoint of a sparse slot copy. *)
Theory bodySlotCopyTaintMods
Ancestors
  keyUpdateFold[qualified,ignore_grammar]
  bodyFullShadowBodyInv bodyFullStoreSlotsStatic placeStoreStorage bodyPtrDefs
  accountsRelProps stateRelProj stateRelProjStorage loweringStateRelDefs
  bodyMemoryDefs vyperStorageFootprint vyperStorageBackend vyperState
  venomState ptrDiscipline vyperTyping words list pred_set
  vyperEncodeDecode[qualified,ignore_grammar]
  vyperStorageAccessFrame[qualified,ignore_grammar]
  placeStoreSlots[qualified,ignore_grammar]
  representationCleanPtr[qualified,ignore_grammar]
  sourceUnitExecution[qualified,ignore_grammar]
  valueEncodingDefs[qualified,ignore_grammar]
  valueEncodingProofs[qualified,ignore_grammar]
  valueEncodingProps[qualified,ignore_grammar]
  venomMemProofs[qualified,ignore_grammar]

Theorem slot_copy_robust_byte_clean[local]:
  b < 32 /\
  (!mem. mem_agree_outside M s.vs_memory mem ==>
     EL b (mem_bytes_at a 32 mem) = value) ==>
  a+b NOTIN M
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!x. mem_agree_outside M s.vs_memory
       (write_memory_with_expansion (a+b) [x] s).vs_memory` by
    (rpt gen_tac >> irule representationCleanPtrTheory.mem_agree_outside_write_byte >> simp[]) >>
  `!x. EL b (mem_bytes_at a 32
    (write_memory_with_expansion (a+b) [x] s).vs_memory) = x` by
    (gen_tac >>
     qspecl_then [`a+b`, `[x]`, `s`]
       (mp_tac o Q.AP_TERM `EL 0`) valueEncodingPropsTheory.write_memory_mem_bytes_at_same >>
     qpat_assum `b < 32` (fn th => simp[NoAsms, th, valueEncodingProofsTheory.EL_mem_bytes_at])) >>
  `value = 0w /\ value = 1w` by metis_tac[] >> fs[]
QED

Theorem slot_copy_written_byte_dead[local]:
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory tv v off mem) /\
  start + type_slot_size tv <= dimword (:256) /\ i < type_slot_size tv /\
  MEM i (MAP FST writes) /\ b IN mem_word_taint M (off+32*i) ==>
  dead_bytes (apply_writes (n2w start) writes st) start tv (start+i) b
Proof
  simp[mem_word_taint_def] >> strip_tac >> spose_not_then assume_tac >>
  `start < dimword (:256)` by decide_tac >>
  `off+32*i+b NOTIN M` suffices_by simp[] >>
  irule slot_copy_robust_byte_clean >> simp[] >>
  qexistsl_tac [`s`, `EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes st)) T)`] >>
  rpt strip_tac >> sym_tac >>
  `word_to_bytes (mload (off + 32*i) (s with vs_memory := mem)) T =
    mem_bytes_at (off + 32*i) 32 mem` by
    (simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload, valueEncodingDefsTheory.mem_word_at_def] >>
     simp[GSYM valueEncodingDefsTheory.mem_bytes_at_def] >>
     irule venomMemProofsTheory.word_bytes_roundtrip_proof >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def, dividesTheory.divides_def]) >>
  `EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes st)) T) =
    EL b (word_to_bytes (mload (off+32*i) (s with vs_memory := mem)) T)`
    suffices_by simp[] >>
  irule place_store_memory_live_at >>
  `val_in_memory tv v off mem` by metis_tac[] >>
  simp[] >> qexistsl_tac [`tv`,`v`] >> simp[]
QED

Theorem slot_copy_sparse_taint_at:
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ start + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory tv v off mem) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  X SUBSET {(k,b) | storage_dead H tr st (w2n k) b} ==>
  FOLDL (\Z i. key_update Z (n2w (start+i):bytes32) (mem_word_taint M (off+32*i))) X ks
    SUBSET {(k,b) | storage_dead H tr (apply_writes (n2w start) writes st) (w2n k) b}
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!i. MEM i (MAP FST writes) ==> i < type_slot_size tv` by
    metis_tac[cj 1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
  `!i. i < type_slot_size tv ==> w2n (n2w (start+i):bytes32) = start+i` by
    (rpt strip_tac >> `start+i < dimword (:256)` by decide_tac >> simp[wordsTheory.w2n_n2w]) >>
  simp_tac (srw_ss()) [SUBSET_DEF, pairTheory.FORALL_PROD, cardinalTheory.IN_ELIM_PAIR_THM] >>
  qx_gen_tac `k` >> qx_gen_tac `b` >> disch_tac >>
  qspecl_then [`\i. n2w (start+i):bytes32`, `\i. mem_word_taint M (off+32*i)`]
    (drule o BETA_RULE) keyUpdateFoldTheory.key_update_fold_cases >>
  disch_then (DISJ_CASES_THEN STRIP_ASSUME_TAC)
  >- suspend "unwritten" >> suspend "written"
QED

Resume slot_copy_sparse_taint_at[unwritten]:
  `storage_dead H tr st (w2n k) b` by
    (qpat_assum `X SUBSET _` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[cardinalTheory.IN_ELIM_PAIR_THM]) >>
  Cases_on `start <= w2n k /\ w2n k < start + type_slot_size tv`
  >- suspend "inside" >> suspend "outside"
QED

Resume slot_copy_sparse_taint_at[inside]:
  `?i. w2n k = start+i /\ i < type_slot_size tv` by
    (qexists_tac `w2n k - start` >> decide_tac) >>
  `~MEM i (MAP FST writes)` by
    (strip_tac >> `MEM i ks` by metis_tac[] >>
     `n2w (start+i) = k` by metis_tac[wordsTheory.n2w_w2n] >>
     qpat_x_assum `!j. MEM j ks ==> k <> _` (qspec_then `i` mp_tac) >>
     simp[]) >>
  `b < 32 /\ dead_bytes st start tv (start+i) b` by
    (`dead_bytes st start tv (w2n k) b` by metis_tac[store_slots_subregion_dead_iff] >>
     drule (cj 1 dead_bytes_range) >> simp[] >>
     gvs[store_slots_subregion_dead_iff, cj 1 dead_bytes_range]) >>
  `dead_bytes (apply_writes (n2w start) writes st) start tv (start+i) b` by
    metis_tac[placeStoreSlotsTheory.place_store_unwritten_live_preserved] >>
  metis_tac[store_slots_subregion_dead_iff]
QED

Resume slot_copy_sparse_taint_at[outside]:
  `!q:bytes32. ~(start <= w2n q /\ w2n q < start + type_slot_size tv) ==>
     lookup_storage q (apply_writes (n2w start) writes st) = lookup_storage q st` by
    (qx_gen_tac `q` >> disch_tac >>
     irule vyperStorageAccessFrameTheory.apply_writes_word_frame >>
     qx_gen_tac `i` >> disch_tac >>
     `i < type_slot_size tv` by metis_tac[] >>
     strip_tac >>
     `w2n q = start+i` by metis_tac[wordsTheory.word_add_n2w] >> decide_tac) >>
  irule place_store_storage_dead_subregion_frame >>
  qexistsl_tac [`delta`,`tv`,`path`,`root`,`rootk`,`st`] >>
  qpat_assum `start = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  asm_rewrite_tac[]
QED

Resume slot_copy_sparse_taint_at[written]:
  `MEM j (MAP FST writes) /\ j < type_slot_size tv` by metis_tac[] >>
  `dead_bytes (apply_writes (n2w start) writes st) start tv (start+j) b` by
    (irule slot_copy_written_byte_dead >> metis_tac[]) >>
  `w2n k = start+j` by metis_tac[] >>
  `start <= w2n k /\ w2n k < start + type_slot_size tv` by decide_tac >>
  metis_tac[store_slots_subregion_dead_iff]
QED

Finalise slot_copy_sparse_taint_at[local]

Theorem slot_copy_sparse_taint:
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\ storage_subregion root path delta tv /\
  w2n k = w2n rootk + delta /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory tv v off mem) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  X SUBSET {(q,b) | storage_dead H tr st (w2n q) b} ==>
  FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (off+32*i))) X ks
    SUBSET {(q,b) | storage_dead H tr (apply_writes k writes st) (w2n q) b}
Proof
  strip_tac >> qabbrev_tac `start = w2n k` >>
  `!i. k + n2w i = n2w (start+i)` by
    simp[Abbr `start`, GSYM wordsTheory.word_add_n2w] >>
  qpat_assum `!i. k + n2w i = _` (fn th => pure_rewrite_tac[th]) >>
  `n2w start = k` by simp[Abbr `start`] >>
  pop_assum (fn th => pure_once_rewrite_tac[GSYM th]) >>
  irule slot_copy_sparse_taint_at >> asm_rewrite_tac[] >>
  qexistsl_tac [`delta`,`path`,`root`,`rootk`,`s`,`tv`,`v`] >> asm_rewrite_tac[] >>
  decide_tac
QED

Theorem slot_copy_state_dead_mask[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  s.vs_call_ctx.cc_address = cx.txn.target ==>
  storage_dead H tr (if tr then contract_transient s else contract_storage s) =
  storage_dead H tr (get_storage cx ee tr)
Proof
  strip_tac >> drule stmt_state_rel_state_rel >> strip_tac >>
  Cases_on `tr`
  >- (drule state_rel_transient_rel >>
      simp[transient_rel_def, get_storage_def] >>
      metis_tac[storage_agree_storage_dead]) >>
  drule state_rel_storage_rel >>
  simp[storage_rel_def, get_storage_def, vfmStateTheory.lookup_account_def] >>
  metis_tac[storage_agree_storage_dead]
QED

Theorem slot_copy_bank_taint_frame[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx ee s /\
  stmt_state_rel H ctx func cenv cx ef t /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
  dead_lo_ok_mods H D lo cenv cx /\ stor_taint_ok_at D tn s /\
  tnf.t_imm = tn.t_imm /\
  (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
  get_storage cx ef (~tr) = get_storage cx ee (~tr) /\
  ((if tr then tn.t_trans else tn.t_stor) SUBSET
       {(k,b) | storage_dead H tr (get_storage cx ee tr) (w2n k) b} ==>
   (if tr then tnf.t_trans else tnf.t_stor) SUBSET
       {(k,b) | storage_dead H tr (get_storage cx ef tr) (w2n k) b}) ==>
  stor_taint_ok_at D tnf t
Proof
  strip_tac >>
  `!b. storage_dead H b (if b then contract_transient s else contract_storage s) =
       storage_dead H b (get_storage cx ee b)` by metis_tac[slot_copy_state_dead_mask] >>
  `!b. storage_dead H b (if b then contract_transient t else contract_storage t) =
       storage_dead H b (get_storage cx ef b)` by metis_tac[slot_copy_state_dead_mask] >>
  rpt (qpat_x_assum `!b. storage_dead H b _ = _`
    (fn th => map_every (fn b => qspec_then b assume_tac th) [`T`,`F`])) >>
  Cases_on `tr` >>
  gvs[dead_lo_ok_mods_def, stor_taint_ok_at_def, sourceUnitExecutionTheory.cx_dead_def,
      contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def]
QED

Theorem slot_copy_post_stor_taint_mods:
  stmt_state_rel H ctx func cenv cx ee s /\
  stmt_state_rel H ctx func cenv cx ef t /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
  dead_lo_ok_mods H D lo cenv cx /\ stor_taint_ok_at D tn s /\
  tnf.t_imm = tn.t_imm /\
  (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
  ef = set_storage cx ee tr (apply_writes k writes (get_storage cx ee tr)) /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\ storage_subregion root path delta tv /\
  w2n k = w2n rootk + delta /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v off mem) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  (if tr then tnf.t_trans else tnf.t_stor) SUBSET
    FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint tn.t_mem (off+32*i)))
      (if tr then tn.t_trans else tn.t_stor) ks ==>
  stor_taint_ok_at D tnf t
Proof
  strip_tac >>
  irule slot_copy_bank_taint_frame >>
  qexistsl_tac [`H`,`cenv`,`ctx`,`cx`,`ee`,`ef`,`func`,`lo`,`s`,`tn`,`tr`] >>
  asm_rewrite_tac[] >> simp[get_storage_after_set] >>
  conj_tac >- (irule get_storage_after_set_other >> Cases_on `tr` >> simp[]) >>
  disch_tac >>
  irule SUBSET_TRANS >>
  qexists `FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint tn.t_mem (off+32*i)))
    (if tr then tn.t_trans else tn.t_stor) ks` >>
  asm_rewrite_tac[] >> irule slot_copy_sparse_taint >> asm_rewrite_tac[] >>
  qexistsl_tac [`delta`,`path`,`root`,`rootk`,`s`,`tv`,`v`] >> asm_rewrite_tac[] >>
  decide_tac
QED
