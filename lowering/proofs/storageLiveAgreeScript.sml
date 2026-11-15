(*
 * A storage region decodes from its live bytes alone.
 *)
Theory storageLiveAgree
Ancestors
  arithmetic words list byte vyperValue vyperStorage vyperLookupStorage loweringStateRelDefs accountsRelProps

(* ===== Live-byte restriction to consecutive members ===== *)

Theorem dead_bytes_list_head_live[local]:
  !st base tv tvs j b.
  (j:num) < base + type_slot_size tv /\
  ~dead_bytes st base tv j b ==>
  ~dead_bytes_list st base (tv::tvs) j b
Proof
  rw[Once dead_bytes_def] >> strip_tac >>
  drule (cj 2 dead_bytes_range) >> decide_tac
QED

Theorem dead_bytes_list_tail_live[local]:
  !st base tv tvs j b.
  base + type_slot_size tv <= (j:num) /\
  ~dead_bytes_list st (base + type_slot_size tv) tvs j b ==>
  ~dead_bytes_list st base (tv::tvs) j b
Proof
  rw[Once dead_bytes_def] >> strip_tac >>
  drule (cj 1 dead_bytes_range) >> decide_tac
QED

Theorem dead_bytes_fields_head_live[local]:
  !st base nm tv fields j b.
  (j:num) < base + type_slot_size tv /\
  ~dead_bytes st base tv j b ==>
  ~dead_bytes_fields st base ((nm,tv)::fields) j b
Proof
  rw[Once dead_bytes_def] >> strip_tac >>
  drule (cj 3 dead_bytes_range) >> decide_tac
QED

Theorem dead_bytes_fields_tail_live[local]:
  !st base nm tv fields j b.
  base + type_slot_size tv <= (j:num) /\
  ~dead_bytes_fields st (base + type_slot_size tv) fields j b ==>
  ~dead_bytes_fields st base ((nm,tv)::fields) j b
Proof
  rw[Once dead_bytes_def] >> strip_tac >>
  drule (cj 1 dead_bytes_range) >> decide_tac
QED

(* Storage that agrees with s1 on every byte of the region s1 does not leave
   dead (dead_bytes) decodes there whenever s1 does. Intuition: every slot
   slots_in_range reads lies in the region; the length slot of a bytestring
   or DynArray is never dead (dyn_bytes_dead needs off < j), so both
   storages see the same length; DynArray elements below the length are
   dead only where the element type leaves them dead; all 32 bytes equal
   make the words equal (the agreement is stated at the same n2w j that
   read_slot reads). dead_bytes_range bounds every dead byte to its region. *)
Theorem slots_in_range_live_agree:
  slots_in_range s1 off tv /\
  (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
         ~dead_bytes s1 off tv j b ==>
         EL b (word_to_bytes (lookup_storage (n2w j) s1) T) =
         EL b (word_to_bytes (lookup_storage (n2w j) s2) T)) ==>
  slots_in_range s2 off tv
Proof
  qid_spec_tac `off` >> qid_spec_tac `s2` >> qid_spec_tac `s1` >>
  qid_spec_tac `tv` >> ho_match_mp_tac type_value_induction >>
  conj_tac >- suspend "base" >>
  conj_tac >- suspend "tuple" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "struct" >>
  conj_tac >- suspend "flag" >>
  simp[slots_in_range_def]
QED

Resume slots_in_range_live_agree[base]:
  rpt gen_tac >> strip_tac >>
  `lookup_storage (n2w off) s2 = lookup_storage (n2w off) s1` by
    (irule dead_bytes_head_eq >> qexists_tac `BaseTV b` >>
     simp[] >> Cases_on `b` >> simp[type_slot_size_def] >>
     rename1 `BytesT bt` >> Cases_on `bt` >> simp[type_slot_size_def]) >>
  Cases_on `b` >> gvs[slots_in_range_def, read_slot_def] >>
  rename1 `BytesT bt` >> Cases_on `bt` >>
  gvs[slots_in_range_def, read_slot_def]
QED

Resume slots_in_range_live_agree[flag]:
  rpt gen_tac >> strip_tac >> rename1 `FlagTV n` >>
  `lookup_storage (n2w off) s2 = lookup_storage (n2w off) s1` by
    (irule dead_bytes_head_eq >> qexists_tac `FlagTV n` >>
     simp[type_slot_size_def]) >>
  gvs[slots_in_range_def, read_slot_def]
QED

Resume slots_in_range_live_agree[tuple]:
  Induct >> simp[slots_in_range_def, type_slot_size_def, dead_bytes_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `slots_in_range s1 off h` >>
  conj_tac
  >- (first_x_assum (qspec_then `h` mp_tac) >> simp[] >>
      disch_then irule >> qexists_tac `s1` >> simp[] >> rpt strip_tac >>
      first_x_assum irule >>
      simp[] >> strip_tac >> drule (cj 2 dead_bytes_range) >> decide_tac) >>
  qpat_x_assum `(_ ==> !s1 s2 off. _)` mp_tac >>
  simp[slots_in_range_def, type_slot_size_def, dead_bytes_def] >>
  disch_then irule >> conj_tac
  >- metis_tac[] >>
  qexists_tac `s1` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac
QED

Resume slots_in_range_live_agree[array]:
  gen_tac >> strip_tac >> Cases >> rpt gen_tac >> strip_tac
  >- (rename1 `ArrayTV tv (Fixed n)` >>
      gvs[slots_in_range_def, array_slots_in_range_indexed] >>
      rpt strip_tac >> rename1 `k < n` >> first_x_assum irule >> qexists_tac `s1` >>
      simp[] >> rpt strip_tac >> first_x_assum irule >>
      simp[type_slot_size_def] >>
      reverse conj_tac
      >- (qpat_x_assum `k < n` mp_tac >>
          disch_then (mp_tac o MATCH_MP array_element_slot_bound) >>
          disch_then (qspecl_then [`type_slot_size tv`, `off`] mp_tac) >>
          decide_tac) >>
      strip_tac >>
      `j < off + k * type_slot_size tv + type_slot_size tv` by decide_tac >>
      drule_all fixed_array_elem_dead >> simp[]) >>
  rename1 `ArrayTV tv (Dynamic cap)` >>
  `lookup_storage (n2w off) s2 = lookup_storage (n2w off) s1` by
    (irule dead_bytes_head_eq >> qexists_tac `ArrayTV tv (Dynamic cap)` >>
     simp[type_slot_size_def]) >>
  gvs[slots_in_range_def, read_slot_def, array_slots_in_range_indexed] >>
  rpt strip_tac >> rename1 `k < cap` >> first_x_assum irule >> qexists_tac `s1` >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[type_slot_size_def] >>
  reverse conj_tac
  >- (qpat_x_assum `k < cap` mp_tac >>
      disch_then (mp_tac o MATCH_MP array_element_slot_bound) >>
      disch_then (qspecl_then [`type_slot_size tv`, `off + 1`] mp_tac) >>
      decide_tac) >>
  strip_tac >>
  `off + 1 + k * type_slot_size tv <= j` by decide_tac >>
  `j < off + 1 + k * type_slot_size tv + type_slot_size tv` by decide_tac >>
  drule_all dyn_array_elem_dead >>
  simp[]
QED

Resume slots_in_range_live_agree[struct]:
  Induct >> simp[slots_in_range_def, type_slot_size_def, dead_bytes_def] >>
  qx_gen_tac `fld` >> PairCases_on `fld` >>
  rename1 `(nm,tv)::fields` >>
  simp[slots_in_range_def, type_slot_size_def, dead_bytes_def, pairTheory.setSND_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `!p. p = (nm,tv) \/ MEM p fields ==> _`
        (qspec_then `(nm,tv)` mp_tac) >> simp[] >>
      disch_then irule >>
      qexists_tac `s1` >> simp[] >> rpt strip_tac >>
      first_x_assum irule >>
      simp[] >> strip_tac >> drule (cj 3 dead_bytes_range) >> decide_tac) >>
  qpat_x_assum `(_ ==> !s1 s2 off. _)` mp_tac >>
  simp[slots_in_range_def, type_slot_size_def, dead_bytes_def] >>
  disch_then irule >> conj_tac
  >- (simp[pairTheory.setSND_def] >> rpt strip_tac >>
      rename1 `MEM p fields` >> first_x_assum irule >> conj_tac
      >- simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `s1` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac
QED

Finalise slots_in_range_live_agree
