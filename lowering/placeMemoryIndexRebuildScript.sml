Theory placeMemoryIndexRebuild
Ancestors
  exprSimAggregateEncoding exprSimPop valueEncodingProps valueEncoding vyperTyping
  vyperValueOperation loweringPosts list rich_list arithmetic
  valueEncodingTyping vyperTypeDefaults placeMemoryTypedBase vyperArray
  vyperAssignPreservesType

(* Pointwise reconstruction of a homogeneous list after one live update. *)
Theorem elems_in_memory_update:
  i < LENGTH vs /\
  val_in_memory tv z (off + i * type_memory_size tv) mem /\
  (!j. j < LENGTH vs /\ j <> i ==>
    val_in_memory tv (EL j vs) (off + j * type_memory_size tv) mem) ==>
  elems_in_memory (LUPDATE z i vs) off tv mem
Proof
  strip_tac >> irule elems_in_memory_intro >> simp[LENGTH_LUPDATE] >>
  rpt strip_tac >> Cases_on `i = i'` >> simp[EL_LUPDATE] >>
  metis_tac[]
QED

Theorem elems_in_memory_update_frame:
  i < LENGTH vs /\ elems_val_wf vs tv /\
  elems_in_memory vs off tv mem /\
  val_in_memory tv z (off + i * type_memory_size tv) mem' /\
  (!j. j < LENGTH vs /\ j <> i ==>
    mem_bytes_at (off + j * type_memory_size tv) (type_memory_size tv) mem' =
    mem_bytes_at (off + j * type_memory_size tv) (type_memory_size tv) mem) ==>
  elems_in_memory (LUPDATE z i vs) off tv mem'
Proof
  strip_tac >> irule elems_in_memory_update >> simp[] >>
  rpt strip_tac >> irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[elems_val_wf_EL] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
  metis_tac[elems_in_memory_EL]
QED

(* A homogeneous cell is a contained sibling slice, with an optional header. *)
Theorem uniform_memory_cell_frame:
  !hdr off j sz cap i mem mem'.
  j < cap /\ j <> i /\
  (!a n. off <= a /\ a + n <= off + hdr + cap * sz /\
    (a + n <= off + hdr + i * sz \/ off + hdr + (i + 1) * sz <= a) ==>
    mem_bytes_at a n mem' = mem_bytes_at a n mem) ==>
  mem_bytes_at (off + (j * sz + hdr)) sz mem' =
  mem_bytes_at (off + (j * sz + hdr)) sz mem
Proof
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  `j + 1 <= cap` by decide_tac >>
  `(j + 1) * sz <= cap * sz` by simp[LE_MULT_RCANCEL] >>
  Cases_on `j < i`
  >- (`j + 1 <= i` by decide_tac >>
      `(j + 1) * sz <= i * sz` by simp[LE_MULT_RCANCEL] >>
      rule_assum_tac (PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
      decide_tac) >>
  `i + 1 <= j` by decide_tac >>
  `(i + 1) * sz <= j * sz` by simp[LE_MULT_RCANCEL] >>
  rule_assum_tac (PURE_REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
  rewrite_tac[LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem dynamic_array_update_frame:
  i < LENGTH vs /\ LENGTH vs <= cap /\ elems_val_wf vs tv /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem /\
  val_in_memory tv z (off + 32 + i * type_memory_size tv) mem' /\
  (!a n. off <= a /\ a + n <= off + 32 + cap * type_memory_size tv /\
    (a + n <= off + 32 + i * type_memory_size tv \/
     off + 32 + (i + 1) * type_memory_size tv <= a) ==>
    mem_bytes_at a n mem' = mem_bytes_at a n mem) ==>
  val_in_memory (ArrayTV tv (Dynamic cap))
    (ArrayV (DynArrayV (LUPDATE z i vs))) off mem'
Proof
  simp[Once val_in_memory_def] >> strip_tac >>
  simp[Once val_in_memory_def, LENGTH_LUPDATE] >> conj_tac
  >- ( `mem_bytes_at off 32 mem' = mem_bytes_at off 32 mem` by
         (first_x_assum irule >> simp[]) >>
       gvs[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  irule elems_in_memory_update_frame >> simp[] >>
  qexists_tac `mem` >> simp[] >>
  rpt strip_tac >>
  qspec_then `32` irule uniform_memory_cell_frame >>
  qexistsl_tac [`cap`, `i`] >> reverse conj_tac >- decide_tac >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem tuple_in_memory_iff_EL:
  !vs tvs off mem. LENGTH vs = LENGTH tvs ==>
  (tuple_in_memory vs tvs off mem <=>
   !j. j < LENGTH vs ==>
     val_in_memory (EL j tvs) (EL j vs)
       (off + type_memory_size_list (TAKE j tvs)) mem)
Proof
  Induct >> Cases_on `tvs` >> simp[val_in_memory_def] >>
  rpt gen_tac >> strip_tac >> simp[val_in_memory_def] >>
  eq_tac
  >- (strip_tac >> Cases_on `j`
      >- (simp_tac bool_ss [TAKE_0, EL, HD, type_memory_size_def,
                            ADD_0, prim_recTheory.LESS_0] >> first_assum ACCEPT_TAC) >>
      `SUC n <> 0` by decide_tac >>
      asm_simp_tac std_ss [TAKE_def, EL, TL, HD, type_memory_size_def,
                        prim_recTheory.LESS_MONO_EQ] >>
      first_assum MATCH_ACCEPT_TAC) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >>
      simp_tac bool_ss [TAKE_0, EL, HD, type_memory_size_def,
                        ADD_0, prim_recTheory.LESS_0]) >>
  gen_tac >> strip_tac >>
  `SUC j <> 0` by decide_tac >>
  qpat_x_assum `!j. j < SUC _ ==> _` (qspec_then `SUC j` mp_tac) >>
  asm_simp_tac std_ss [TAKE_def, EL, TL, HD, type_memory_size_def,
                    prim_recTheory.LESS_MONO_EQ] >>
  simp_tac bool_ss [type_memory_size_def]
QED

Theorem tuple_in_memory_update_frame:
  values_have_types tvs vs /\ i < LENGTH vs /\
  tuple_in_memory vs tvs off mem /\
  val_in_memory (EL i tvs) z
    (off + type_memory_size_list (TAKE i tvs)) mem' /\
  (!j. j < LENGTH vs /\ j <> i ==>
    mem_bytes_at (off + type_memory_size_list (TAKE j tvs))
      (type_memory_size (EL j tvs)) mem' =
    mem_bytes_at (off + type_memory_size_list (TAKE j tvs))
      (type_memory_size (EL j tvs)) mem) ==>
  tuple_in_memory (LUPDATE z i vs) tvs off mem'
Proof
  simp[values_have_types_LIST_REL, LIST_REL_EL_EQN] >> strip_tac >>
  irule (iffRL tuple_in_memory_iff_EL) >>
  simp[LENGTH_LUPDATE] >> rpt strip_tac >>
  Cases_on `j = i` >- simp[EL_LUPDATE] >>
  simp[EL_LUPDATE] >> irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[cj 1 value_has_type_val_wf] >>
  qexistsl_tac [`type_memory_size (EL j tvs)`, `mem`] >> simp[] >>
  metis_tac[tuple_in_memory_iff_EL]
QED

Theorem tuple_memory_cells_ordered:
  !tvs i j. i < j /\ j <= LENGTH tvs ==>
    type_memory_size_list (TAKE i tvs) + type_memory_size (EL i tvs) <=
    type_memory_size_list (TAKE j tvs)
Proof
  Induct >> simp[] >> Cases_on `i` >> Cases_on `j` >>
  simp[] >> rpt strip_tac >>
  simp_tac std_ss [TAKE_def, EL, HD, TL, type_memory_size_def] >>
  first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[] >> decide_tac
QED

Theorem tuple_update_bounded_frame:
  values_have_types tvs vs /\ i < LENGTH vs /\
  tuple_in_memory vs tvs off mem /\
  val_in_memory (EL i tvs) z
    (off + type_memory_size_list (TAKE i tvs)) mem' /\
  (!a n. off <= a /\ a + n <= off + type_memory_size_list tvs /\
    (a + n <= off + type_memory_size_list (TAKE i tvs) \/
     off + type_memory_size_list (TAKE i tvs) + type_memory_size (EL i tvs) <= a) ==>
    mem_bytes_at a n mem' = mem_bytes_at a n mem) ==>
  tuple_in_memory (LUPDATE z i vs) tvs off mem'
Proof
  strip_tac >> irule tuple_in_memory_update_frame >> simp[] >>
  qexists_tac `mem` >> simp[] >> rpt strip_tac >>
  `LENGTH tvs = LENGTH vs` by
    gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `type_memory_size_list (TAKE j tvs) + type_memory_size (EL j tvs) <=
     type_memory_size_list tvs` by
    (qspecl_then [`tvs`, `j`, `LENGTH (tvs:type_value list)`] mp_tac
       tuple_memory_cells_ordered >> simp[]) >>
  first_x_assum irule >> simp[] >>
  Cases_on `j < i`
  >- (disj1_tac >>
      qspecl_then [`tvs`, `j`, `i`] mp_tac tuple_memory_cells_ordered >>
      simp[] >> decide_tac) >>
  disj2_tac >>
  qspecl_then [`tvs`, `i`, `j`] mp_tac tuple_memory_cells_ordered >>
  simp[] >> decide_tac
QED

Theorem sparse_array_update_frame:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  value_has_type tv z /\
  array_set_index (ArrayTV tv (Fixed n)) (SArrayV kvs) (&i) z =
    INL (ArrayV (SArrayV kvs')) /\
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem /\
  val_in_memory tv z (off + i * type_memory_size tv) mem' /\
  (!j. j < n /\ j <> i ==>
    mem_bytes_at (off + j * type_memory_size tv) (type_memory_size tv) mem' =
    mem_bytes_at (off + j * type_memory_size tv) (type_memory_size tv) mem) ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) off mem'
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs'))` by
    (drule array_set_index_preserves_type >> simp[]) >>
  irule typed_memory_sarray_intro >> simp[] >>
  rpt strip_tac >> Cases_on `i' = i`
  >- (gvs[] >> drule array_index_after_set_same >>
      simp[array_index_def] >>
      Cases_on `ALOOKUP kvs' i` >> simp[]) >>
  `array_index (ArrayTV tv (Fixed n)) (SArrayV kvs') (&i') =
   array_index (ArrayTV tv (Fixed n)) (SArrayV kvs) (&i')` by
    (irule array_index_after_set_other >> qexistsl_tac [`&i`, `z`] >> simp[]) >>
  ` (case ALOOKUP kvs' i' of NONE => default_value tv | SOME v => v) =
    (case ALOOKUP kvs i' of NONE => default_value tv | SOME v => v)` by
    (gvs[array_index_def] >> Cases_on `ALOOKUP kvs' i'` >>
     Cases_on `ALOOKUP kvs i'` >> gvs[]) >>
  asm_rewrite_tac[] >> irule val_in_memory_mem_agree >>
  conj_tac
  >- (irule typed_memory_sparse_lookup_wf >> qexists_tac `n` >>
      qpat_assum `value_has_type _ (ArrayV (SArrayV kvs))`
        (mp_then Any mp_tac (cj 1 value_has_type_val_wf)) >> simp[val_wf_def]) >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
  metis_tac[typed_memory_sarray_element]
QED

Theorem sparse_array_update_bounded_frame:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  value_has_type tv z /\
  array_set_index (ArrayTV tv (Fixed n)) (SArrayV kvs) (&i) z =
    INL (ArrayV (SArrayV kvs')) /\
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem /\
  val_in_memory tv z (off + i * type_memory_size tv) mem' /\
  (!a len. off <= a /\ a + len <= off + n * type_memory_size tv /\
    (a + len <= off + i * type_memory_size tv \/
     off + (i + 1) * type_memory_size tv <= a) ==>
    mem_bytes_at a len mem' = mem_bytes_at a len mem) ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs')) off mem'
Proof
  strip_tac >> irule sparse_array_update_frame >>
  qexistsl_tac [`i`, `kvs`, `mem`, `z`] >> simp[] >>
  rpt strip_tac >>
  irule (SRULE [] (Q.SPEC `0` uniform_memory_cell_frame)) >>
  qexistsl_tac [`n`, `i`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[MULT_COMM]
QED
