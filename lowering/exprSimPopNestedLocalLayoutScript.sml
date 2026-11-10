Theory exprSimPopNestedLocalLayout
Ancestors
  compileEnv exprSimAggregateEncoding exprSimPop valueEncodingProps valueEncodingProofs
  loweringPosts vyperArray vyperTyping vyperTypeInvariants venomState arithmetic vyperValueOperation vyperState valueEncoding valueEncodingDefs valueEncodingTyping abiStaticSparseProps alist vyperAssignPreservesType

(* A word store inside slot i cannot alter a distinct slot j. *)
Theorem val_in_memory_mstore_other_index:
  !tv v locbase i j q w s.
    val_in_memory tv v (locbase + j * type_memory_size tv) s.vs_memory /\
    val_wf tv v /\ j <> i /\ i * type_memory_size tv <= q /\
    q + 32 <= (i + 1) * type_memory_size tv ==>
    val_in_memory tv v (locbase + j * type_memory_size tv)
      (mstore (locbase + q) w s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `mstore (locbase + q) w s =
     mstore (locbase + q) w (s with vs_memory := s.vs_memory)` by
    simp[mstore_def] >>
  pop_assum SUBST1_TAC >>
  irule (cj 1 mstore_preserves_val_in_memory) >> simp[] >>
  Cases_on `j < i`
  >- (disj2_tac >>
      `(j + 1) * type_memory_size tv <= i * type_memory_size tv` by
        simp[LE_MULT_RCANCEL] >>
      qpat_x_assum `(j + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  disj1_tac >>
  `(i + 1) * type_memory_size tv <= j * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >> decide_tac
QED

(* Pointwise reconstruction keeps the selected slot and frames every sibling. *)
Theorem elems_in_memory_LUPDATE_mstore:
  !vs tv locbase i v q w s.
    elems_in_memory vs locbase tv s.vs_memory /\ elems_val_wf vs tv /\
    i < LENGTH vs /\ i * type_memory_size tv <= q /\
    q + 32 <= (i + 1) * type_memory_size tv /\
    val_in_memory tv v (locbase + i * type_memory_size tv)
      (mstore (locbase + q) w s).vs_memory ==>
    elems_in_memory (LUPDATE v i vs) locbase tv (mstore (locbase + q) w s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `elems_in_memory vs locbase tv s.vs_memory` >>
  irule elems_in_memory_intro >> simp[] >>
  qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = i` >- gvs[listTheory.EL_LUPDATE] >>
  simp[listTheory.EL_LUPDATE] >>
  `val_in_memory tv (EL j vs) (locbase + j * type_memory_size tv) s.vs_memory` by
    (irule elems_in_memory_EL >> simp[]) >>
  `val_wf tv (EL j vs)` by (irule elems_val_wf_EL >> simp[]) >>
  irule val_in_memory_mstore_other_index >> simp[] >> qexists_tac `i` >> simp[]
QED

Theorem array_child_memory:
  !ct bd a locbase i d child s.
    value_has_type (ArrayTV ct bd) a /\
    well_formed_type_value (ArrayTV ct bd) /\
    val_wf (ArrayTV ct bd) a /\
    val_in_memory (ArrayTV ct bd) a locbase s.vs_memory /\
    mem_step_offset (ArrayTV ct bd) (ValueSubscript (IntV i)) = SOME (d,ct) /\
    evaluate_subscripts (ArrayTV ct bd) a [ValueSubscript (IntV i)] = INL child ==>
    val_wf ct child /\ val_in_memory ct child (locbase + d) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  Cases_on `bd` >> gvs[value_has_type_def] >>
  gvs[mem_step_offset_def, evaluate_subscripts_def, array_index_def,
      val_in_memory_def, val_wf_def, AllCaseEqs()]
  >~ [`oEL _ _ = SOME _`]
  >- (gvs[listTheory.oEL_THM] >> conj_tac
      >- (irule elems_val_wf_EL >> simp[]) >>
      drule elems_in_memory_EL >>
      disch_then (qspec_then `Num i` mp_tac) >>
      simp[AC ADD_ASSOC ADD_COMM])
  >~ [`val_wf _ (default_value _)`]
  >- simp[cj 1 val_wf_default_value_proof] >>
  conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >>
      drule_all sparse_has_type_lookup >> simp[]) >>
  irule kvs_in_memory_lookup >> goal_assum drule >> simp[]
QED

Theorem dynarray_memory_LUPDATE_mstore:
  !vs tv n locbase i v q w s.
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) locbase s.vs_memory /\
    elems_val_wf vs tv /\ i < LENGTH vs /\
    32 + i * type_memory_size tv <= q /\
    q + 32 <= 32 + (i + 1) * type_memory_size tv /\
    val_in_memory tv v (locbase + 32 + i * type_memory_size tv)
      (mstore (locbase + q) w s).vs_memory ==>
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV (LUPDATE v i vs)))
      locbase (mstore (locbase + q) w s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  gvs[val_in_memory_def] >> conj_tac
  >- (`locbase + 32 <= locbase + q` by decide_tac >>
      simp[mstore_mem_word_at_disjoint]) >>
  `32 <= q` by decide_tac >>
  `q = 32 + (q - 32)` by decide_tac >>
  qpat_x_assum `q = _` SUBST1_TAC >>
  pure_rewrite_tac[ADD_ASSOC] >>
  irule elems_in_memory_LUPDATE_mstore >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

(* Pointwise sparse encoding includes the absent/default slots. *)
Theorem sarray_memory_index:
  !al tv n locbase mem.
    SORTED $< (MAP FST al) /\ (!j v. MEM (j,v) al ==> j < n) ==>
    (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) locbase mem <=>
     !j. j < n ==>
       val_in_memory tv (case ALOOKUP al j of NONE => default_value tv | SOME v => v)
         (locbase + j * type_memory_size tv) mem)
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- (simp[val_in_memory_def] >> strip_tac >>
      qx_gen_tac `j` >> strip_tac >> Cases_on `ALOOKUP al j` >> simp[] >>
      irule kvs_in_memory_lookup >> goal_assum drule >> simp[]) >>
  strip_tac >> simp[val_in_memory_def] >> conj_tac
  >- (rewrite_tac[kvs_in_memory_every, listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
      rpt gen_tac >> strip_tac >>
      PairCases_on `e` >> gvs[] >>
      drule_all sorted_sparse_ALOOKUP >> strip_tac >>
      first_x_assum (qspec_then `e0` mp_tac) >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem sarray_set_index_layout:
  !al tv n i v al'.
    SORTED $< (MAP FST al) /\ sparse_has_type tv n al /\
    array_set_index (ArrayTV tv (Fixed n)) (SArrayV al) i v =
      INL (ArrayV (SArrayV al')) ==>
    SORTED $< (MAP FST al') /\ (!j x. MEM (j,x) al' ==> j < n)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[array_set_index_def, AllCaseEqs()]
  >~ [`SORTED _ (MAP FST (ADELKEY _ _))`]
  >- (conj_tac >- (irule ADELKEY_SORTED >> simp[]) >>
      rpt strip_tac >>
      gvs[ADELKEY_def, listTheory.MEM_FILTER] >>
      drule_all typed_sparse_key_bound >> simp[]) >>
  conj_tac >- (irule insert_sarray_SORTED >> simp[]) >>
  rpt strip_tac >>
  `MEM j (MAP FST (insert_sarray (Num i) v al))` by
    (simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  gvs[MEM_MAP_FST_insert_sarray, listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  drule_all typed_sparse_key_bound >> simp[]
QED

Theorem sarray_memory_set_index_mstore:
  !al tv n locbase i v al' q w s.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) /\
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) locbase s.vs_memory /\
    i < n /\ i * type_memory_size tv <= q /\
    q + 32 <= (i + 1) * type_memory_size tv /\
    array_set_index (ArrayTV tv (Fixed n)) (SArrayV al) (&i) v =
      INL (ArrayV (SArrayV al')) /\
    val_in_memory tv v (locbase + i * type_memory_size tv)
      (mstore (locbase + q) w s).vs_memory ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al'))
      locbase (mstore (locbase + q) w s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `SORTED $< (MAP FST al') /\ (!j x. MEM (j,x) al' ==> j < n)` by
    (irule sarray_set_index_layout >> goal_assum (drule_at Any) >>
     gvs[value_has_type_def]) >>
  drule_all sarray_memory_index >> disch_then (fn th => rewrite_tac[th]) >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j = i`
  >- (gvs[] >> drule array_index_after_set_same >>
      simp[array_index_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `array_index (ArrayTV tv (Fixed n)) (SArrayV al') (&j) =
   array_index (ArrayTV tv (Fixed n)) (SArrayV al) (&j)` by
    (irule array_index_after_set_other >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[array_index_def] >>
  `(case ALOOKUP al' j of NONE => default_value tv | SOME v => v) =
   (case ALOOKUP al j of NONE => default_value tv | SOME v => v)` by
    (Cases_on `ALOOKUP al j` >> Cases_on `ALOOKUP al' j` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `val_wf tv (case ALOOKUP al j of NONE => default_value tv | SOME v => v)` by
    (Cases_on `ALOOKUP al j` >> simp[cj 1 val_wf_default_value_proof] >>
     irule (cj 1 value_has_type_val_wf) >>
     gvs[value_has_type_def] >> drule_all sparse_has_type_lookup >> simp[]) >>
  irule val_in_memory_mstore_other_index >> simp[] >> conj_tac
  >- (qexists_tac `i` >> simp[]) >>
  Cases_on `ALOOKUP al j` >> gvs[val_in_memory_def] >>
  irule kvs_in_memory_lookup >> goal_assum (drule_at Any) >> simp[]
QED

Theorem array_child_memory_store:
  !ct bd a locbase i d child child' a' q w s.
    value_has_type (ArrayTV ct bd) a /\
    well_formed_type_value (ArrayTV ct bd) /\
    val_wf (ArrayTV ct bd) a /\
    val_in_memory (ArrayTV ct bd) a locbase s.vs_memory /\
    mem_step_offset (ArrayTV ct bd) (ValueSubscript (IntV i)) = SOME (d,ct) /\
    evaluate_subscripts (ArrayTV ct bd) a [ValueSubscript (IntV i)] = INL child /\
    assign_subscripts (ArrayTV ct bd) a [ValueSubscript (IntV i)] (Replace child') = INL a' /\
    d <= q /\ q + 32 <= d + type_memory_size ct /\
    val_in_memory ct child' (locbase + d) (mstore (locbase + q) w s).vs_memory ==>
    val_in_memory (ArrayTV ct bd) a' locbase (mstore (locbase + q) w s).vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  Cases_on `bd` >> gvs[value_has_type_def] >>
  gvs[mem_step_offset_def, evaluate_subscripts_def, assign_subscripts_def,
      array_index_def, AllCaseEqs()]
  >>~- ([`array_set_index _ (SArrayV _) _ _ = _`],
      drule integerTheory.NUM_POSINT_EXISTS >> strip_tac >> gvs[] >>
      gvs[array_set_index_def, AllCaseEqs()] >>
      irule sarray_memory_set_index_mstore >>
      goal_assum (drule_at Any) >>
      simp[value_has_type_def, array_set_index_def, RIGHT_ADD_DISTRIB] >>
      qexists_tac `l` >> simp[]) >>
  gvs[array_set_index_def, listTheory.oEL_THM, AllCaseEqs()] >>
  `TAKE (Num i) l ++ [child'] ++ DROP (SUC (Num i)) l =
   LUPDATE child' (Num i) l` by
    (irule listTheory.LIST_EQ >>
     simp[listTheory.LENGTH_TAKE_EQ, listTheory.EL_APPEND_EQN,
          listTheory.EL_LUPDATE, listTheory.EL_TAKE, listTheory.EL_DROP] >>
     rpt strip_tac >> Cases_on `x < Num i` >> simp[] >>
     Cases_on `x = Num i` >> gvs[ADD1]) >>
  pop_assum SUBST1_TAC >>
  irule dynarray_memory_LUPDATE_mstore >>
  gvs[val_wf_def] >> simp[AC ADD_ASSOC ADD_COMM, RIGHT_ADD_DISTRIB]
QED

Theorem fields_memory_child:
  !vals fs id d ct child locbase mem.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    fields_in_memory vals fs locbase mem /\
    mem_field_offset fs id = SOME (d,ct) /\ ALOOKUP vals id = SOME child ==>
    val_wf ct child /\ val_in_memory ct child (locbase + d) mem
Proof
  Induct >> simp[] >> PairCases >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_wf_def, val_in_memory_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem struct_child_memory:
  !fs a locbase id d ct child s.
    value_has_type (StructTV fs) a /\
    well_formed_type_value (StructTV fs) /\ val_wf (StructTV fs) a /\
    val_in_memory (StructTV fs) a locbase s.vs_memory /\
    mem_step_offset (StructTV fs) (AttrSubscript id) = SOME (d,ct) /\
    evaluate_subscripts (StructTV fs) a [AttrSubscript id] = INL child ==>
    val_wf ct child /\ val_in_memory ct child (locbase + d) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >>
  gvs[value_has_type_def, val_wf_def, val_in_memory_def, mem_step_offset_def,
      evaluate_subscripts_def, AllCaseEqs()] >>
  drule_all fields_memory_child >> simp[]
QED

Theorem fields_memory_child_store:
  !vals fs id d ct child' locbase q w s.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    fields_in_memory vals fs locbase s.vs_memory /\
    mem_field_offset fs id = SOME (d,ct) /\
    d <= q /\ q + 32 <= d + type_memory_size ct /\
    val_in_memory ct child' (locbase + d) (mstore (locbase + q) w s).vs_memory ==>
    fields_in_memory (AFUPDKEY id (K child') vals) fs locbase
      (mstore (locbase + q) w s).vs_memory
Proof
  Induct >- simp[AFUPDKEY_def, val_in_memory_def] >>
  PairCases >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_wf_def, val_in_memory_def,
       mem_field_offset_def, AFUPDKEY_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[AllCaseEqs()]
  >- (simp[val_in_memory_def] >>
      `mstore (locbase + q) w s =
       mstore (locbase + q) w (s with vs_memory := s.vs_memory)` by simp[mstore_def] >>
      pop_assum SUBST1_TAC >>
      irule (cj 2 mstore_preserves_val_in_memory) >> simp[]) >>
  PairCases_on `z` >> gvs[] >>
  simp[val_in_memory_def] >> conj_tac
  >- (`mstore (locbase + q) w s =
       mstore (locbase + q) w (s with vs_memory := s.vs_memory)` by simp[mstore_def] >>
      pop_assum SUBST1_TAC >>
      irule (cj 1 mstore_preserves_val_in_memory) >> simp[] >> decide_tac) >>
  `type_memory_size h1' <= q` by decide_tac >>
  `q = type_memory_size h1' + (q - type_memory_size h1')` by decide_tac >>
  qpat_x_assum `q = _` SUBST1_TAC >>
  pure_rewrite_tac[ADD_ASSOC] >> first_x_assum irule >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem struct_child_memory_store:
  !fs a locbase id d ct child child' a' q w s.
    value_has_type (StructTV fs) a /\
    well_formed_type_value (StructTV fs) /\ val_wf (StructTV fs) a /\
    val_in_memory (StructTV fs) a locbase s.vs_memory /\
    mem_step_offset (StructTV fs) (AttrSubscript id) = SOME (d,ct) /\
    evaluate_subscripts (StructTV fs) a [AttrSubscript id] = INL child /\
    assign_subscripts (StructTV fs) a [AttrSubscript id] (Replace child') = INL a' /\
    d <= q /\ q + 32 <= d + type_memory_size ct /\
    val_in_memory ct child' (locbase + d) (mstore (locbase + q) w s).vs_memory ==>
    val_in_memory (StructTV fs) a' locbase (mstore (locbase + q) w s).vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >>
  gvs[value_has_type_def, val_wf_def, val_in_memory_def, mem_step_offset_def,
      evaluate_subscripts_def, assign_subscripts_def, AllCaseEqs()] >>
  irule fields_memory_child_store >> goal_assum (drule_at Any) >> simp[]
QED
