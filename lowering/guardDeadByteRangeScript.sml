Theory guardDeadByteRange
Ancestors
  accountsRelProps vyperLookupStorage loweringStateRelDefs vyperValue
  vyperStorage

Theorem slots_in_range_live_bytes_mutual:
  (!s off tv t.
    (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
       ~dead_bytes s off tv j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) s) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) t) T)) ==>
    (slots_in_range s off tv <=> slots_in_range t off tv)) /\
  (!s off tvs t.
    (!j b. off <= j /\ j < off + type_slot_size_list tvs /\ b < 32 /\
       ~dead_bytes_list s off tvs j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) s) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) t) T)) ==>
    (tuple_slots_in_range s off tvs <=> tuple_slots_in_range t off tvs)) /\
  (!s off fields t.
    (!j b. off <= j /\ j < off + type_slot_size_fields fields /\ b < 32 /\
       ~dead_bytes_fields s off fields j b ==>
       EL b (word_to_bytes (lookup_storage (n2w j) s) T) =
       EL b (word_to_bytes (lookup_storage (n2w j) t) T)) ==>
    (struct_slots_in_range s off fields <=> struct_slots_in_range t off fields))
Proof
  qsuff_tac
   `(!s off tv (j:num) (b:num) t.
      (!i c. off <= i /\ i < off + type_slot_size tv /\ c < 32 /\
         ~dead_bytes s off tv i c ==>
         EL c (word_to_bytes (lookup_storage (n2w i) s) T) =
         EL c (word_to_bytes (lookup_storage (n2w i) t) T)) ==>
      (slots_in_range s off tv <=> slots_in_range t off tv)) /\
    (!s off tvs (j:num) (b:num) t.
      (!i c. off <= i /\ i < off + type_slot_size_list tvs /\ c < 32 /\
         ~dead_bytes_list s off tvs i c ==>
         EL c (word_to_bytes (lookup_storage (n2w i) s) T) =
         EL c (word_to_bytes (lookup_storage (n2w i) t) T)) ==>
      (tuple_slots_in_range s off tvs <=> tuple_slots_in_range t off tvs)) /\
    (!s off fields (j:num) (b:num) t.
      (!i c. off <= i /\ i < off + type_slot_size_fields fields /\ c < 32 /\
         ~dead_bytes_fields s off fields i c ==>
         EL c (word_to_bytes (lookup_storage (n2w i) s) T) =
         EL c (word_to_bytes (lookup_storage (n2w i) t) T)) ==>
      (struct_slots_in_range s off fields <=> struct_slots_in_range t off fields))`
  >- metis_tac[] >>
  ho_match_mp_tac dead_bytes_ind >> rpt strip_tac
  >~ [`slots_in_range _ _ NoneTV`]
  >- simp[slots_in_range_def]
  >~ [`tuple_slots_in_range _ _ []`]
  >- simp[slots_in_range_def]
  >~ [`struct_slots_in_range _ _ []`]
  >- simp[slots_in_range_def]
  >~ [`slots_in_range _ _ (TupleTV _)`]
  >- (ONCE_REWRITE_TAC [slots_in_range_def] >> first_x_assum irule >>
      fs[dead_bytes_def, type_slot_size_def])
  >~ [`slots_in_range _ _ (StructTV _)`]
  >- (ONCE_REWRITE_TAC [slots_in_range_def] >> first_x_assum irule >>
      fs[dead_bytes_def, type_slot_size_def])
  >~ [`slots_in_range _ _ (ArrayTV _ (Fixed _))`]
  >- (PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
      REWRITE_TAC [cj 1 array_slots_in_range_indexed] >>
      `!k. k < n ==>
        (slots_in_range s (off + k * type_slot_size tv) tv <=>
         slots_in_range t (off + k * type_slot_size tv) tv)`
        suffices_by metis_tac[] >>
      rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
      first_x_assum irule >>
      qpat_assum `k < n` (mp_tac o MATCH_MP array_element_slot_bound) >>
      disch_then (qspecl_then [`type_slot_size tv`, `off`] assume_tac) >>
      rpt conj_tac
      >~ [`~dead_bytes _ _ _ _ _`]
      >- (strip_tac >> drule_all fixed_array_elem_dead >> fs[]) >>
      PURE_REWRITE_TAC [type_slot_size_def] >> decide_tac)
  >~ [`slots_in_range _ _ (ArrayTV _ (Dynamic _))`]
  >- (qpat_assum `!i c. _`
        (assume_tac o ONCE_REWRITE_RULE [EQ_SYM_EQ]) >>
      drule dead_bytes_head_eq >>
      impl_tac >- simp[type_slot_size_def] >> disch_then assume_tac >>
      reverse (Cases_on `w2n (lookup_storage (n2w off) s) <= n`)
      >- (PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
          simp[read_slot_def, LET_THM]) >>
      `MIN (w2n (lookup_storage (n2w off) s)) n =
       w2n (lookup_storage (n2w off) s)` by simp[arithmeticTheory.MIN_DEF] >>
      `!k. k < w2n (lookup_storage (n2w off) s) ==>
        (slots_in_range s (off + 1 + k * type_slot_size tv) tv <=>
         slots_in_range t (off + 1 + k * type_slot_size tv) tv)`
        suffices_by
        (PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
         simp[read_slot_def, LET_THM,
              cj 2 array_slots_in_range_indexed] >> metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!i. i < w2n _ ==> _` (qspec_then `k` mp_tac) >>
      asm_rewrite_tac[] >> disch_then (qspec_then `t` irule) >>
      rpt strip_tac >> first_x_assum irule >>
      `k < n` by decide_tac >>
      qpat_assum `k < n` (mp_tac o MATCH_MP array_element_slot_bound) >>
      disch_then (qspecl_then [`type_slot_size tv`, `off + 1`] assume_tac) >>
      rpt conj_tac
      >~ [`~dead_bytes _ _ _ _ _`]
      >- (strip_tac >> drule_all dyn_array_elem_dead >> fs[]) >>
      PURE_REWRITE_TAC [type_slot_size_def] >> decide_tac)
  >~ [`tuple_slots_in_range _ _ (_ :: _)`]
  >- (rename1 `tuple_slots_in_range _ off (tv :: tvs)` >>
      ONCE_REWRITE_TAC [slots_in_range_def] >> BINOP_TAC
      >- (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >>
          rpt conj_tac
          >~ [`~dead_bytes_list _ _ _ _ _`]
          >- (PURE_ONCE_REWRITE_TAC [dead_bytes_def] >> strip_tac >>
              imp_res_tac dead_bytes_range >> fs[]) >>
          PURE_REWRITE_TAC [type_slot_size_def] >> decide_tac) >>
      first_x_assum irule >> rpt strip_tac >> first_x_assum irule >>
      rpt conj_tac
      >~ [`~dead_bytes_list _ _ _ _ _`]
      >- (PURE_ONCE_REWRITE_TAC [dead_bytes_def] >> strip_tac >>
          imp_res_tac dead_bytes_range >> fs[]) >>
      PURE_REWRITE_TAC [type_slot_size_def] >> decide_tac)
  >~ [`struct_slots_in_range _ _ (_ :: _)`]
  >- (ONCE_REWRITE_TAC [slots_in_range_def] >> BINOP_TAC
      >- (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >>
          rpt conj_tac
          >~ [`~dead_bytes_fields _ _ _ _ _`]
          >- (PURE_ONCE_REWRITE_TAC [dead_bytes_def] >> strip_tac >>
              imp_res_tac dead_bytes_range >> fs[]) >>
          PURE_REWRITE_TAC [type_slot_size_def] >> decide_tac) >>
      first_x_assum irule >> rpt strip_tac >> first_x_assum irule >>
      rpt conj_tac
      >~ [`~dead_bytes_fields _ _ _ _ _`]
      >- (PURE_ONCE_REWRITE_TAC [dead_bytes_def] >> strip_tac >>
          imp_res_tac dead_bytes_range >> fs[]) >>
      PURE_REWRITE_TAC [type_slot_size_def] >> decide_tac) >>
  qpat_assum `!i c. _` (assume_tac o ONCE_REWRITE_RULE [EQ_SYM_EQ]) >>
  (drule dead_bytes_head_eq >> impl_tac >- simp[type_slot_size_def] >>
   disch_then (fn th => simp[slots_in_range_def, read_slot_def, th]))
QED
