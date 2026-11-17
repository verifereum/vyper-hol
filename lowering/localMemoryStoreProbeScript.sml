(* Isolated probe: robust replacement allows copied dead-byte taint. *)
Theory localMemoryStoreProbe
Ancestors
  placeMemoryPathRebuild
  bodyPtrDefs loweringPosts valueEncoding valueEncodingProofs
  compileEnv vyperState venomState list arithmetic

Theorem robust_memory_replace_entry:
  mem_path_offset entry.type path = SOME (k,tv) /\
  value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ value_has_type tv v /\
  replace_memory_entry entry path v = INL entry' /\
  (!m. mem_agree_outside tm mem m ==>
    val_in_memory entry.type entry.value b m) /\
  (!m. mem_agree_outside tm' mem' m ==>
    val_in_memory tv v (b+k) m) /\
  (!q. q < b+k \/ b+k+type_memory_size tv <= q ==>
    mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') /\
  (!q. (q < b+k \/ b+k+type_memory_size tv <= q) /\ q IN tm' ==>
    q IN tm) ==>
  entry'.type = entry.type /\
  (!m. mem_agree_outside tm' mem' m ==>
    val_in_memory entry'.type entry'.value b m)
Proof
  strip_tac >>
  conj_tac
  >- (gvs[replace_memory_entry_def, AllCaseEqs()]) >>
  gen_tac >> strip_tac >>
  qabbrev_tac `hybrid = GENLIST
    (\q. HD (mem_bytes_at q 1
      (if b+k <= q /\ q < b+k+type_memory_size tv then mem else m)))
    (MAX (LENGTH mem) (LENGTH m))` >>
  `!q. mem_bytes_at q 1 hybrid = mem_bytes_at q 1
    (if b+k <= q /\ q < b+k+type_memory_size tv then mem else m)` by
    (gen_tac >> irule LIST_EQ >>
     simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at, Abbr `hybrid`,
          EL_GENLIST, GSYM EL] >>
     Cases_on `b+k <= q /\ q < b+k+type_memory_size tv` >>
     simp[] >> Cases_on `q < LENGTH mem` >>
     Cases_on `q < LENGTH m` >> simp[]) >>
  `mem_agree_outside tm mem hybrid` by
    (rw[mem_agree_outside_def] >>
     Cases_on `b+k <= i /\ i < b+k+type_memory_size tv`
     >- simp[] >>
     `i < b+k \/ b+k+type_memory_size tv <= i` by decide_tac >>
     `i NOTIN tm'` by metis_tac[] >>
     fs[mem_agree_outside_def] >> metis_tac[]) >>
  `val_in_memory entry.type entry.value b hybrid` by metis_tac[] >>
  irule typed_memory_replace_entry_frame >>
  goal_assum (drule_at (Pat `replace_memory_entry _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  qexists_tac `hybrid` >> simp[] >>
  rpt strip_tac >>
  irule LIST_EQ >> simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >> rename1 `j < n` >>
  `~(b+k <= b'+j /\ b'+j < b+k+type_memory_size tv)` by decide_tac >>
  `mem_bytes_at (b'+j) 1 hybrid = mem_bytes_at (b'+j) 1 m` by simp[] >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED
