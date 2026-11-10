(* Context reconstruction uses padded byte observations, the same lookup as
   EL_mem_bytes_at. No ownership or history invariant is defined here. *)
Theory bodyPtrSubscriptMemoryRebuild
Ancestors
  bodyPtrSubscriptCurrentMemory valueEncodingProps valueEncodingProofs
  valueTypingMemoryProps valueEncoding valueEncodingDefs exprSimAggregateEncoding vyperTyping
  list arithmetic tupleMemoryLayout typedCopyTuplePtr vyperTypeDefaults
  loweringPosts alist vyperArray vyperAssignPreservesType vyperValueOperation pair vyperState

Theorem mem_bytes_at_pointwise:
  !mem mem' off len.
    (!addr. off <= addr /\ addr < off + len ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    mem_bytes_at off len mem' = mem_bytes_at off len mem
Proof
  rpt strip_tac >> irule LIST_EQ >>
  simp[LENGTH_mem_bytes_at_proof] >> rpt strip_tac >>
  simp[EL_mem_bytes_at] >> first_x_assum irule >> decide_tac
QED

Theorem val_in_memory_outside_frame:
  !tv v off mem mem' cut size.
    val_in_memory tv v off mem /\ value_has_type tv v /\
    (cut + size <= off \/ off + type_memory_size tv <= cut) /\
    (!addr. addr < cut \/ cut + size <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    val_in_memory tv v off mem'
Proof
  rpt gen_tac >> strip_tac >>
  drule value_has_type_memory_wf >> strip_tac >>
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
  sym_tac >> irule mem_bytes_at_pointwise >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem elems_in_memory_replace:
  !vs tv off mem mem' j new.
    elems_in_memory vs off tv mem /\ all_have_type tv vs /\
    j < LENGTH vs /\
    val_in_memory tv new (off + j * type_memory_size tv) mem' /\
    (!addr. addr < off + j * type_memory_size tv \/
            off + j * type_memory_size tv + type_memory_size tv <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    elems_in_memory (LUPDATE new j vs) off tv mem'
Proof
  rpt gen_tac >> strip_tac >> irule elems_in_memory_intro >>
  simp[LENGTH_LUPDATE] >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `i = j` >- simp[EL_LUPDATE] >>
  simp[EL_LUPDATE] >> irule val_in_memory_outside_frame >>
  conj_tac >- gvs[all_have_type_EVERY, EVERY_EL] >>
  qexistsl_tac [`off + j * type_memory_size tv`, `mem`, `type_memory_size tv`] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  reverse conj_tac
  >- (drule_all elems_in_memory_EL >> simp[]) >>
  `i < j \/ j < i` by decide_tac
  >- (disj2_tac >>
      `(i + 1) * type_memory_size tv <= j * type_memory_size tv` by
        simp[LE_MULT_RCANCEL] >>
      pop_assum mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
      decide_tac) >>
  disj1_tac >>
  `(j + 1) * type_memory_size tv <= i * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  pop_assum mp_tac >>
  pure_rewrite_tac[RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  decide_tac
QED

Theorem dynarray_in_memory_replace:
  !vs tv cap off mem mem' j new.
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem /\
    all_have_type tv vs /\ j < LENGTH vs /\
    val_in_memory tv new (off + 32 + j * type_memory_size tv) mem' /\
    (!addr. addr < off + 32 + j * type_memory_size tv \/
      off + 32 + j * type_memory_size tv + type_memory_size tv <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (LUPDATE new j vs))) off mem'
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at off 32 mem' = mem_bytes_at off 32 mem` by
    (irule mem_bytes_at_pointwise >> rpt strip_tac >>
     first_x_assum irule >> disj1_tac >> decide_tac) >>
  `mem_word_at off mem' = mem_word_at off mem` by
    gvs[mem_word_at_def, mem_bytes_at_def] >>
  gvs[val_in_memory_dynarray, LENGTH_LUPDATE] >>
  irule elems_in_memory_replace >>
  asm_simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM] >>
  qexists_tac `mem` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem sum_take_element_before:
  !xs f i j. i < j /\ j <= LENGTH xs ==>
    SUM (MAP f (TAKE i xs)) + f (EL i xs) <= SUM (MAP f (TAKE j xs))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem tuple_in_memory_replace:
  !vs tvs off mem mem' j new.
    tuple_in_memory vs tvs off mem /\ values_have_types tvs vs /\
    j < LENGTH tvs /\
    val_in_memory (EL j tvs) new
      (off + SUM (MAP type_memory_size (TAKE j tvs))) mem' /\
    (!addr. addr < off + SUM (MAP type_memory_size (TAKE j tvs)) \/
      off + SUM (MAP type_memory_size (TAKE j tvs)) +
        type_memory_size (EL j tvs) <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    tuple_in_memory (LUPDATE new j vs) tvs off mem'
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  irule tuple_in_memory_from_elements >> simp[LENGTH_LUPDATE] >>
  qx_gen_tac `i` >> strip_tac >>
  Cases_on `i = j` >- simp[EL_LUPDATE] >>
  simp[EL_LUPDATE] >> irule val_in_memory_outside_frame >>
  conj_tac >- gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  qexistsl_tac [`off + SUM (MAP type_memory_size (TAKE j tvs))`,
    `mem`, `type_memory_size (EL j tvs)`] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  reverse conj_tac >- metis_tac[tuple_in_memory_element] >>
  `i < j \/ j < i` by decide_tac
  >- (disj2_tac >> simp[GSYM ADD_ASSOC] >>
      irule sum_take_element_before >> simp[]) >>
  disj1_tac >> simp[GSYM ADD_ASSOC] >>
  irule sum_take_element_before >> simp[]
QED

Theorem fields_in_memory_outside_frame:
  !fs vals off mem mem' cut size.
    fields_in_memory vals fs off mem /\ struct_has_type fs vals /\
    (cut + size <= off \/ off + type_memory_size_fields fs <= cut) /\
    (!addr. addr < cut \/ cut + size <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    fields_in_memory vals fs off mem'
Proof
  rpt strip_tac >>
  `val_in_memory (StructTV fs) (StructV vals) off mem'` suffices_by
    simp[val_in_memory_def] >>
  irule val_in_memory_outside_frame >>
  simp[value_has_type_def, type_memory_size_def, val_in_memory_def] >>
  metis_tac[]
QED

Theorem fields_in_memory_replace:
  !fs vals off mem mem' fld d ftv new.
    struct_has_type fs vals /\ fields_in_memory vals fs off mem /\
    mem_field_offset fs fld = SOME (d,ftv) /\
    val_in_memory ftv new (off+d) mem' /\
    (!addr. addr < off+d \/ off+d+type_memory_size ftv <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    fields_in_memory (AFUPDKEY fld (K new) vals) fs off mem'
Proof
  Induct >> Cases_on `vals` >> simp[value_has_type_def, mem_field_offset_def] >>
  PairCases_on `h` >> gen_tac >> PairCases_on `h'` >>
  simp[value_has_type_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h0 = fld`
  >- (gvs[val_in_memory_def, AFUPDKEY_def] >>
      irule fields_in_memory_outside_frame >> simp[] >>
      qexistsl_tac [`off`, `mem`, `type_memory_size ftv`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[CaseEq "option", pairTheory.EXISTS_PROD, val_in_memory_def, AFUPDKEY_def] >>
  conj_tac
  >- (irule val_in_memory_outside_frame >> simp[] >>
      qexistsl_tac [`off + (p_1 + type_memory_size h'1)`, `mem`,
        `type_memory_size ftv`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  first_x_assum irule >> simp[] >>
  qexists_tac `mem` >>
  asm_simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem sparse_has_type_index_bound[local]:
  !tv n kvs i v. sparse_has_type tv n kvs /\ MEM (i,v) kvs ==> i < n
Proof
  Induct_on `kvs` >> simp[value_has_type_def] >>
  gen_tac >> PairCases_on `h` >> simp[value_has_type_def] >> metis_tac[]
QED

Theorem sarray_in_memory_elements:
  !tv n kvs off mem.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) ==>
    (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem <=>
     elems_in_memory (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))
       off tv mem)
Proof
  rpt gen_tac >> strip_tac >>
  eq_tac
  >- (strip_tac >> irule elems_in_memory_intro >>
      simp[array_elements_def] >> rpt strip_tac >>
      Cases_on `ALOOKUP kvs i` >>
      gvs[val_in_memory_sarray] >> drule_all kvs_in_memory_lookup >> simp[]) >>
  strip_tac >> simp[val_in_memory_sarray] >> conj_tac
  >- (simp[kvs_in_memory_every, EVERY_MEM, FORALL_PROD] >>
      rpt strip_tac >>
      `ALOOKUP kvs p_1 = SOME p_2` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >>
         gvs[value_has_type_def] >> metis_tac[SORTED_lt_ALL_DISTINCT]) >>
      `p_1 < n` by
        (gvs[value_has_type_def] >> drule_all sparse_has_type_index_bound >> simp[]) >>
      drule elems_in_memory_EL >>
      disch_then (qspec_then `p_1` mp_tac) >> simp[array_elements_def]) >>
  rpt strip_tac >> drule elems_in_memory_EL >>
  disch_then (qspec_then `i` mp_tac) >> simp[array_elements_def]
QED

Theorem sarray_elements_have_type:
  !tv n kvs.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
    well_formed_type_value tv ==>
    all_have_type tv (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))
Proof
  rpt strip_tac >> simp[all_have_type_EVERY, EVERY_EL, array_elements_def] >>
  rpt strip_tac >> Cases_on `ALOOKUP kvs n'` >> gvs[value_has_type_def]
  >- metis_tac[default_value_well_typed] >>
  drule_all sparse_has_type_lookup >> simp[]
QED

(* vyperArray's corresponding splice equation is local, not exported. *)
Theorem list_splice_eq_update:
  !xs j new. j < LENGTH xs ==>
    TAKE j xs ++ [new] ++ DROP (SUC j) xs = LUPDATE new j xs
Proof
  Induct >> simp[] >> gen_tac >> Cases >> simp[LUPDATE_DEF]
QED

Theorem sarray_in_memory_replace:
  !tv n kvs kvs' off mem mem' i new.
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
    well_formed_type_value tv /\ value_has_type tv new /\
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem /\
    array_set_index (ArrayTV tv (Fixed n)) (SArrayV kvs) i new =
      INL (ArrayV (SArrayV kvs')) /\
    val_in_memory tv new (off + Num i * type_memory_size tv) mem' /\
    (!addr. addr < off + Num i * type_memory_size tv \/
      off + Num i * type_memory_size tv + type_memory_size tv <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) off mem'
Proof
  rpt gen_tac >> strip_tac >>
  `value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs'))` by
    (drule array_set_index_preserves_type >> simp[]) >>
  `Num i < n` by gvs[array_set_index_def, AllCaseEqs()] >>
  drule array_elements_after_set >> strip_tac >>
  gvs[sarray_in_memory_elements, list_splice_eq_update,
      array_elements_length_sarray, array_length_def] >>
  irule elems_in_memory_replace >>
  conj_tac >- simp[array_elements_def] >>
  conj_tac >- (irule sarray_elements_have_type >> metis_tac[]) >>
  reverse conj_tac >- simp[] >>
  qexists_tac `mem` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem mem_step_replace_in_memory:
  !tv a sb old a' new off mem mem' d etv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\ mem_step_offset tv sb = SOME (d,etv) /\
    evaluate_subscripts tv a [sb] = INL old /\
    assign_subscripts tv a [sb] (Replace new) = INL a' /\
    value_has_type etv new /\ val_in_memory etv new (off+d) mem' /\
    (!addr. addr < off+d \/ off+d+type_memory_size etv <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    val_in_memory tv a' off mem'
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[mem_step_offset_def] >> Cases_on `tv` >>
      simp[mem_step_offset_def]
      >- (Cases_on `a` >> simp[value_has_type_def] >>
          rename1 `ArrayV av` >> Cases_on `av` >>
          simp[value_has_type_def, assign_subscripts_def, array_set_index_def,
               CaseEq "option"] >> rpt strip_tac >> gvs[]) >>
      Cases_on `b` >> Cases_on `a` >> simp[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def] >>
      rpt strip_tac >>
      gvs[mem_step_offset_def, assign_subscripts_def, CaseEq "option"]
      >- (`?kvs'. a' = ArrayV (SArrayV kvs')` by
            (Cases_on `new = default_value etv` >> gvs[array_set_index_def]) >>
          gvs[] >> irule sarray_in_memory_replace >>
          simp[value_has_type_def, well_formed_type_value_def] >>
          conj_tac >- gvs[well_formed_type_value_def] >>
          qexistsl_tac [`i`, `l`, `mem`, `new`] >> simp[] >>
          rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      gvs[array_set_index_def] >>
      gvs[list_splice_eq_update] >> irule dynarray_in_memory_replace >>
      asm_simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM] >>
      qexists_tac `mem` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  Cases_on `tv` >> Cases_on `a` >>
  simp[mem_step_offset_def, value_has_type_def, assign_subscripts_def,
       val_in_memory_def, evaluate_subscripts_def, CaseEq "option"] >>
  rpt strip_tac >> gvs[] >>
  simp[val_in_memory_def] >> irule fields_in_memory_replace >>
  asm_simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM] >>
  qexists_tac `mem` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
