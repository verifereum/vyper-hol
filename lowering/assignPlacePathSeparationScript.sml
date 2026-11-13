Theory assignPlacePathSeparation
Ancestors
  assignPlaceLayoutHeight exprSimProps loweringPosts compileEnv valueEncoding
  list arithmetic integer pair

(* A selected field is either the same selected window, or a disjoint one. *)
Theorem mem_field_offset_windows:
  !fs id1 id2 i a j b.
    mem_field_offset fs id1 = SOME (i,a) /\
    mem_field_offset fs id2 = SOME (j,b) ==>
    (i = j /\ a = b) \/
    i + type_memory_size a <= j \/ j + type_memory_size b <= i
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  rpt gen_tac >> simp[mem_field_offset_def] >>
  rw[optionTheory.OPTION_MAP_EQ_SOME, EXISTS_PROD] >> gvs[] >>
  first_x_assum (qspecl_then [`id1`, `id2`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem array_size_windows[local]:
  !i j s c. c + i * s = c + j * s \/
    c + i * s + s <= c + j * s \/ c + j * s + s <= c + i * s
Proof
  rpt gen_tac >> Cases_on `i = j` >- simp[] >>
  `i < j \/ j < i` by decide_tac >>
  drule vyperLookupStorageTheory.array_index_element_end_bound >>
  disch_then (qspec_then `s` assume_tac) >> decide_tac
QED

Theorem tuple_size_windows[local]:
  !xs i j. i < LENGTH xs /\ j < LENGTH xs ==>
    (type_memory_size_list (TAKE i xs) = type_memory_size_list (TAKE j xs) /\
     EL i xs = EL j xs) \/
    type_memory_size_list (TAKE i xs) + type_memory_size (EL i xs) <= type_memory_size_list (TAKE j xs) \/
    type_memory_size_list (TAKE j xs) + type_memory_size (EL j xs) <= type_memory_size_list (TAKE i xs)
Proof
  `!(ys:type_value list) a b. a < b /\ b <= LENGTH ys ==>
     type_memory_size_list (TAKE a ys) + type_memory_size (EL a ys) <=
     type_memory_size_list (TAKE b ys)` by
    (Induct >> simp[] >> rpt gen_tac >> Cases_on `a` >> Cases_on `b` >>
     simp[type_memory_size_def] >> strip_tac >>
     first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[]) >>
  rpt strip_tac >> Cases_on `i = j` >- simp[] >>
  `i < j \/ j < i` by decide_tac >>
  metis_tac[LESS_IMP_LESS_OR_EQ]
QED

Theorem mem_step_offset_windows:
  mem_step_offset root p = SOME (i,a) /\
  mem_step_offset root q = SOME (j,b) ==>
  (i = j /\ a = b) \/
  i + type_memory_size a <= j \/ j + type_memory_size b <= i
Proof
  rpt strip_tac >>
  qpat_x_assum `mem_step_offset _ p = _` (strip_assume_tac o MATCH_MP mem_step_offset_shape) >>
  qpat_x_assum `mem_step_offset _ q = _` (strip_assume_tac o MATCH_MP mem_step_offset_shape) >>
  gvs[]
  >~ [`mem_field_offset`] >- metis_tac[mem_field_offset_windows]
  >~ [`TAKE`] >- metis_tac[tuple_size_windows, ADD_SYM] >>
  qspecl_then [`Num i'`, `Num i''`, `type_memory_size a`, `0`] mp_tac array_size_windows >>
  simp[ADD_SYM]
QED

Theorem mem_path_equal_height_windows:
  !p root q i a j b.
    mem_path_offset root p = SOME (i,a) /\
    mem_path_offset root q = SOME (j,b) /\
    layout_height a = layout_height b ==>
    a = b \/ i + type_memory_size a <= j \/ j + type_memory_size b <= i
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (Cases_on `q`
      >- gvs[mem_path_offset_def] >>
      qpat_x_assum `mem_path_offset _ (_::_) = _`
        (mp_tac o MATCH_MP mem_path_offset_layout_height) >>
      gvs[mem_path_offset_def]) >>
  Cases_on `q`
  >- (qpat_x_assum `mem_path_offset _ (_::_) = _`
        (mp_tac o MATCH_MP mem_path_offset_layout_height) >>
      gvs[mem_path_offset_def]) >>
  gvs[mem_path_offset_def, optionTheory.OPTION_MAP_EQ_SOME, EXISTS_PROD, AllCaseEqs()] >>
  qpat_assum `mem_step_offset root h = _` mp_tac >>
  qpat_assum `mem_step_offset root h' = _` mp_tac >>
  rename1 `mem_step_offset root h = SOME (k,child)` >>
  rename1 `mem_step_offset root h' = SOME (l,other)` >>
  rpt strip_tac >>
  `((k = l /\ child = other) \/
    k + type_memory_size child <= l \/ l + type_memory_size other <= k)` by
    metis_tac[mem_step_offset_windows] >> gvs[]
  >- (first_x_assum (qspecl_then [`child`, `t`] mp_tac) >>
      simp[] >> rpt strip_tac >> gvs[] >> decide_tac)
  >- (qpat_x_assum `mem_path_offset child p = _`
        (strip_assume_tac o MATCH_MP mem_path_offset_sound) >> simp[]) >>
  qpat_x_assum `mem_path_offset other t = _`
    (strip_assume_tac o MATCH_MP mem_path_offset_sound) >> simp[]
QED
