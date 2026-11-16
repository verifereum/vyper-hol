(* Live-slot frame algebra, independent of execution judgments. *)
Theory fullStoreSlotsMemberFrame
Ancestors
  fullStoreSlotsProbe placeStoreSlots stmtSimStoreCopy stateFrame
  venomState ptrDiscipline words list rich_list arithmetic

Theorem store_slots_frame_nil:
  store_copy_normalize s s =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s [] /\
  s.vs_memory = s.vs_memory /\
  tn.t_mem = tn.t_mem /\ tn.t_imm = tn.t_imm /\
  (if tr then tn.t_trans else tn.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) [] /\
  (if tr then tn.t_stor else tn.t_trans) =
    (if tr then tn.t_stor else tn.t_trans)
Proof
  simp[store_copy_normalize_def, venom_state_component_equality]
QED

Theorem store_slots_frame_shift:
  w2n (sw:bytes32) + 32*so < dimword (:256) /\
  store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) ((dw + n2w so) + n2w j)
      (mload (w2n (sw + n2w (32*so)) + 32*j) s) q) s ks /\
  u.vs_memory = s.vs_memory /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta j. key_update ta ((dw + n2w so) + n2w j)
      (mem_word_taint tn.t_mem (w2n (sw + n2w (32*so)) + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans) ==>
  store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s (MAP ((+) so) ks) /\
  u.vs_memory = s.vs_memory /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) (MAP ((+) so) ks) /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans)
Proof
  strip_tac >>
  `w2n (sw + n2w (32*so)) = w2n sw + 32*so` by
    (simp[w2n_add_2] >> decide_tac) >>
  fs[] >>
  pure_rewrite_tac[FOLDL_MAP, GSYM word_add_n2w, LEFT_ADD_DISTRIB,
    ADD_ASSOC, GSYM WORD_ADD_ASSOC] >>
  simp_tac bool_ss [GSYM word_add_n2w, LEFT_ADD_DISTRIB,
    GSYM WORD_ADD_ASSOC, AC ADD_ASSOC ADD_COMM] >>
  conj_tac >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp_tac bool_ss [FUN_EQ_THM] >> rpt gen_tac >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Theorem store_slots_frame_pure_prefix:
  execution_frame p = execution_frame s /\
  tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\
  tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
  store_copy_normalize p u =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) p) q) p ks /\
  u.vs_memory = p.vs_memory /\
  tf.t_mem = tp.t_mem /\ tf.t_imm = tp.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tp.t_mem (w2n sw + 32*j)))
      (if tr then tp.t_trans else tp.t_stor) ks /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tp.t_stor else tp.t_trans) ==>
  store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s ks /\
  u.vs_memory = s.vs_memory /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans)
Proof
  strip_tac >>
  qpat_x_assum `execution_frame p = execution_frame s` mp_tac >>
  simp[execution_frame_def, venom_state_component_equality] >> strip_tac >>
  `store_copy_normalize s p = s` by
    simp[store_copy_normalize_def, venom_state_component_equality] >>
  qpat_x_assum `store_copy_normalize p u = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[store_slots_normalize_fold, mload_def,
    store_copy_normalize_def, venom_state_component_equality]
QED

Theorem store_slots_frame_append:
  store_copy_normalize s u =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s xs /\
  u.vs_memory = s.vs_memory /\
  tu.t_mem = tn.t_mem /\ tu.t_imm = tn.t_imm /\
  (if tr then tu.t_trans else tu.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) xs /\
  (if tr then tu.t_stor else tu.t_trans) =
    (if tr then tn.t_stor else tn.t_trans) /\
  store_copy_normalize u v =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) u) q) u ys /\
  v.vs_memory = u.vs_memory /\
  tf.t_mem = tu.t_mem /\ tf.t_imm = tu.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tu.t_mem (w2n sw + 32*j)))
      (if tr then tu.t_trans else tu.t_stor) ys /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tu.t_stor else tu.t_trans) ==>
  store_copy_normalize s v =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s (xs ++ ys) /\
  v.vs_memory = s.vs_memory /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta j. key_update ta (dw + n2w j)
      (mem_word_taint tn.t_mem (w2n sw + 32*j)))
      (if tr then tn.t_trans else tn.t_stor) (xs ++ ys) /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans)
Proof
  strip_tac >> conj_tac >- (irule store_slots_fold_compose >> metis_tac[]) >>
  simp[FOLDL_APPEND]
QED
