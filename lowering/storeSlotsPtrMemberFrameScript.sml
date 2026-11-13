(* Algebraic boundaries for sparse member stores. *)
Theory storeSlotsPtrMemberFrame
Ancestors
  storeSlotsPtrInterface stmtSimStoreCopy assignBasePtrStorageSemantic
  stateFrame venomState words list rich_list arithmetic

Theorem store_slots_ptr_frame_shift:
  w2n sw + 32 * so < dimword (:256) /\
  store_slots_ptr_frame tr (sw + n2w (32 * so)) (dw + n2w so) s tn ks u tf ==>
  store_slots_ptr_frame tr sw dw s tn (MAP ((+) so) ks) u tf
Proof
  strip_tac >>
  `w2n (sw + n2w (32 * so)) = w2n sw + 32 * so` by
    (simp[w2n_add_2] >> decide_tac) >>
  fs[store_slots_ptr_frame_def, store_slots_taint_def] >>
  pure_rewrite_tac[FOLDL_MAP, GSYM word_add_n2w, LEFT_ADD_DISTRIB,
    ADD_ASSOC, GSYM WORD_ADD_ASSOC] >>
  simp_tac bool_ss [GSYM word_add_n2w, LEFT_ADD_DISTRIB,
    GSYM WORD_ADD_ASSOC, AC ADD_ASSOC ADD_COMM] >>
  conj_tac >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp_tac bool_ss [FUN_EQ_THM] >> rpt gen_tac >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Theorem store_slots_ptr_frame_pure_prefix:
  execution_frame p = execution_frame s /\
  tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\
  tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
  store_slots_ptr_frame tr sw dw p tp ks u tf ==>
  store_slots_ptr_frame tr sw dw s tn ks u tf
Proof
  simp[store_slots_ptr_frame_def, store_slots_taint_def] >> strip_tac >>
  `store_copy_normalize s p = s` by
    simp[store_copy_normalize_def, venom_state_component_equality] >>
  qpat_x_assum `store_copy_normalize p u = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[placeStoreSlotsTheory.store_slots_normalize_fold, mload_def,
    store_copy_normalize_def, venom_state_component_equality]
QED
