(*
 * Source-side facts about where a target's place lies: its indices
 * (target_indices), and, for a target whose indices are all pure, that
 * evaluating it changes no state and returns a storage place the storage
 * relation reads live.  Below the target judgment's steps so that both
 * the subscript step (targetSubscriptCase) and the nested pop
 * (exprSimPopNestedBase) can use them.
 *)

Theory targetPlaceLive
Ancestors
  compileEnv accountsRelProps exprSimPopStorage
  vyperAST vyperValue vyperState vyperInterpreter vyperLookupStorage
  vyperPlaceFrames vyperPureExpr vyperStatePreservation
  vyperStorageLayoutSafety vyperStoragePlaceRegion vyperStoragePlaceProvenance
  list finite_map

(* The indices of a target, in order. *)
Definition target_indices_def:
  target_indices (NameTarget id) = [] /\
  target_indices (TopLevelNameTarget nsid) = [] /\
  target_indices (AttributeTarget t fld) = target_indices t /\
  target_indices (SubscriptTarget t e) = target_indices t ++ [e]
End

Theorem nested_pop_lookup_frame:
  off + sz <= dimword (:256) /\
  (w2n slot < off \/ off + sz <= w2n slot) ==>
  !i. off <= i /\ i < off + sz ==>
    lookup_storage (n2w i) (update_storage slot u st) =
    lookup_storage (n2w i) st
Proof
  rpt strip_tac >>
  `i < dimword (:256) /\ i <> w2n slot` by decide_tac >>
  `(n2w i:bytes32) <> slot` by
    (strip_tac >> `w2n (n2w i:bytes32) = w2n slot` by simp[] >>
     gvs[wordsTheory.w2n_n2w]) >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED


Theorem nested_pop_array_offset_frame:
  !(a:num) (k:num) (base:num) (sz:num) (slot:bytes32).
  a <> k /\ base + k * sz <= w2n slot /\
  w2n slot < base + (k + 1) * sz ==>
  w2n slot < base + a * sz \/ base + (a + 1) * sz <= w2n slot
Proof
  rpt strip_tac >> Cases_on `a < k`
  >- (`(a + 1) * sz <= k * sz` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >> decide_tac) >>
  `(k + 1) * sz <= a * sz` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >> decide_tac
QED

Theorem nested_pop_dead_list:
  !tvs i elem off slot u st.
    oEL i tvs = SOME elem /\
    off + type_slot_size_list tvs <= dimword (:256) /\
    off + tuple_prefix_slot_size i tvs <= w2n slot /\
    w2n slot < off + tuple_prefix_slot_size i tvs + type_slot_size elem /\
    (!j b. dead_bytes st (off + tuple_prefix_slot_size i tvs) elem j b ==>
      dead_bytes (update_storage slot u st)
        (off + tuple_prefix_slot_size i tvs) elem j b) ==>
    !j b. dead_bytes_list st off tvs j b ==>
      dead_bytes_list (update_storage slot u st) off tvs j b
Proof
  Induct_on `tvs` >- simp[oEL_def] >>
  Cases_on `i`
  >- (simp[oEL_def, tuple_prefix_slot_size_def,
            vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac
      >- metis_tac[] >>
      disj2_tac >>
      `dead_bytes_list (update_storage slot u st)
         (off + type_slot_size h) tvs j b =
       dead_bytes_list st (off + type_slot_size h) tvs j b` by
        (irule (cj 2 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >> decide_tac) >> simp[])
  >> simp[oEL_def, tuple_prefix_slot_size_def,
          vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac
  >- (disj1_tac >>
      `dead_bytes (update_storage slot u st) off h j b =
       dead_bytes st off h j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >> decide_tac) >> simp[]) >>
  disj2_tac >> first_x_assum irule >> simp[] >>
  qexistsl [`elem`, `n`] >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem nested_pop_dead_fields:
  !fields id delta elem off slot u st.
    struct_field_slot fields id = SOME (delta,elem) /\
    off + type_slot_size (StructTV fields) <= dimword (:256) /\
    off + delta <= w2n slot /\
    w2n slot < off + delta + type_slot_size elem /\
    (!j b. dead_bytes st (off + delta) elem j b ==>
      dead_bytes (update_storage slot u st) (off + delta) elem j b) ==>
    !j b. dead_bytes_fields st off fields j b ==>
      dead_bytes_fields (update_storage slot u st) off fields j b
Proof
  Induct_on `fields` >- simp[struct_field_slot_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC
  >- (simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac >- (gvs[] >> metis_tac[]) >> gvs[] >> disj2_tac >>
      `dead_bytes_fields (update_storage slot u st)
         (off + type_slot_size elem) fields j b =
       dead_bytes_fields st (off + type_slot_size elem) fields j b` by
        (irule (cj 3 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >>
         gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >> simp[]) >>
  Cases_on `struct_field_slot fields id` >> simp[] >>
  Cases_on `x` >>
  simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac
  >- (disj1_tac >>
      `dead_bytes (update_storage slot u st) off h1 j b =
       dead_bytes st off h1 j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >> decide_tac) >> simp[]) >>
  disj2_tac >> first_x_assum irule >>
  simp[vyperValueTheory.type_slot_size_def] >>
  qexistsl [`q`, `r`, `id`] >>
  gvs[] >> pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem nested_pop_dead_bytes_subregion:
  !path root delta etv n off slot st j b.
    storage_subregion root path delta (ArrayTV etv (Dynamic n)) /\
    off + type_slot_size root <= dimword (:256) /\
    w2n slot = off + delta /\
    dead_bytes st off root j b ==>
    dead_bytes (update_storage slot
      (n2w (w2n (lookup_storage slot st) - 1)) st) off root j b
Proof
  Induct_on `path`
  >- (simp[storage_subregion_def] >> rpt strip_tac >> gvs[] >>
      irule dead_bytes_pop_header >> simp[])
  >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `h`)
  >- (Cases_on `root` >> gvs[storage_subregion_def] >>
      drule storage_subregion_bounds >> strip_tac >>
      drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >> strip_tac >>
      `rest < type_slot_size elem` by
        (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
      gvs[Once dead_bytes_def] >>
      pure_once_rewrite_tac[compileEnvTheory.dead_bytes_def] >>
      irule nested_pop_dead_fields >> simp[] >>
      qexistsl [`delta'`, `elem`, `s`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
  Cases_on `v` >> Cases_on `root` >> gvs[storage_subregion_def]
  >~ [`dead_bytes _ _ (TupleTV _) _ _`]
  >- (drule storage_subregion_bounds >> strip_tac >>
      drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >>
      strip_tac >>
      `rest < type_slot_size elem` by
        (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
      gvs[dead_bytes_def, vyperValueTheory.type_slot_size_def] >>
      irule nested_pop_dead_list >> simp[] >>
      qexistsl [`elem`, `Num i`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
  rename1 `ArrayTV child bd` >> Cases_on `bd` >> gvs[storage_subregion_def]
  >- (drule storage_subregion_bounds >> strip_tac >>
      gvs[Once dead_bytes_def] >>
      rename1 `a < n'` >> pure_once_rewrite_tac[compileEnvTheory.dead_bytes_def] >>
      qexists `a` >> simp[] >>
      Cases_on `a = Num i`
      >- (gvs[] >> first_x_assum irule >>
          goal_assum (drule_at Any) >>
          simp[] >> conj_tac
          >- (gvs[vyperValueTheory.type_slot_size_def] >>
              `Num i * type_slot_size child + type_slot_size child <=
               n' * type_slot_size child` by
                (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
              decide_tac) >>
          qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
      `w2n slot < off + a * type_slot_size child \/
       off + (a + 1) * type_slot_size child <= w2n slot` by
        (irule nested_pop_array_offset_frame >>
         qexists `Num i` >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.ADD_CLAUSES, arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
      `dead_bytes (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
         (off + a * type_slot_size child) child j b =
       dead_bytes st (off + a * type_slot_size child) child j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >>
         `a * type_slot_size child + type_slot_size child <=
          n' * type_slot_size child` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> simp[])
  >- (drule storage_subregion_bounds >> strip_tac >>
      `off < w2n slot /\ off + 1 <= dimword (:256)` by
        gvs[vyperValueTheory.type_slot_size_def] >>
      `!q. off <= q /\ q < off + 1 ==>
        lookup_storage (n2w q)
          (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) =
        lookup_storage (n2w q) st` by
        (match_mp_tac nested_pop_lookup_frame >> decide_tac) >>
      `lookup_storage (n2w off)
          (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) =
        lookup_storage (n2w off) st` by (first_x_assum irule >> decide_tac) >>
      qpat_x_assum `!q. _` kall_tac >>
      gvs[Once dead_bytes_def] >>
      rename1 `a < n'` >> pure_once_rewrite_tac[compileEnvTheory.dead_bytes_def] >>
      qexists `a` >> simp[] >>
      Cases_on `a < w2n (lookup_storage (n2w off) st)` >> gvs[] >>
      Cases_on `a = Num i`
      >- (gvs[] >> first_x_assum irule >>
          goal_assum (drule_at Any) >> simp[] >> conj_tac
          >- (gvs[vyperValueTheory.type_slot_size_def] >>
              `Num i * type_slot_size child + type_slot_size child <=
               n' * type_slot_size child` by
                (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
              decide_tac) >>
          qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
      `w2n slot < off + 1 + a * type_slot_size child \/
       off + 1 + (a + 1) * type_slot_size child <= w2n slot` by
        (irule nested_pop_array_offset_frame >> qexists `Num i` >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
      `dead_bytes (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
         (off + 1 + a * type_slot_size child) child j b =
       dead_bytes st (off + 1 + a * type_slot_size child) child j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >>
         `a * type_slot_size child + type_slot_size child <=
          n' * type_slot_size child` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[])

QED

Theorem nested_pop_eval_base_pure_state:
  !bt cx st res st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (res,st') ==> st' = st
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >>
      metis_tac[lookup_global_state]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[eval_expr_preserves_state, read_result_state, extend_place_state]
QED

Theorem nested_pop_eval_target_pure_state:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (res,st') ==> st' = st
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def]
QED

Theorem nested_pop_dead_tuple_selected:
  !tvs k elem st off j b.
    oEL k tvs = SOME elem /\ dead_bytes_list st off tvs j b /\
    off + tuple_prefix_slot_size k tvs <= j /\
    j < off + tuple_prefix_slot_size k tvs + type_slot_size elem ==>
    dead_bytes st (off + tuple_prefix_slot_size k tvs) elem j b
Proof
  Induct_on `tvs` >- simp[oEL_def] >>
  Cases_on `k`
  >- (simp[oEL_def, tuple_prefix_slot_size_def] >> rpt strip_tac >>
      gvs[Once dead_bytes_def] >>
      drule (cj 2 accountsRelPropsTheory.dead_bytes_range) >> simp[]) >>
  simp[oEL_def, tuple_prefix_slot_size_def] >> rpt strip_tac >>
  qpat_x_assum `dead_bytes_list _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac
  >- (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> simp[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`st`, `off + type_slot_size h`, `j`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem nested_pop_live_fixed_element:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Fixed n)) /\ k < n ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem)) elem
Proof
  rpt gen_tac >> strip_tac >>
  `k * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def, wordsTheory.WORD_ADD_0] >> rpt strip_tac >>
      qspec_then `w` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[vyperValueTheory.type_slot_size_def] >> strip_tac >>
  `w2n w + k * type_slot_size elem < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (k * type_slot_size elem)) = w2n w + k * type_slot_size elem` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes st (w2n w) (ArrayTV elem (Fixed n)) j b` by
    (first_x_assum irule >> decide_tac) >>
  gvs[Once dead_bytes_def] >>
  `i = k` suffices_by (strip_tac >> gvs[]) >>
  drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> strip_tac >>
  Cases_on `i < k`
  >- (`(i + 1) * type_slot_size elem <= k * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
  Cases_on `k < i`
  >- (`(k + 1) * type_slot_size elem <= i * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> decide_tac
QED

Theorem nested_pop_live_dynamic_element:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Dynamic n)) /\
    k < n /\ k < w2n (lookup_storage w st) ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem + 1)) elem
Proof
  rpt gen_tac >> strip_tac >>
  `k * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + 1w` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[vyperValueTheory.type_slot_size_def] >> strip_tac >>
  `w2n w + (k * type_slot_size elem + 1) < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (k * type_slot_size elem + 1)) =
   w2n w + (k * type_slot_size elem + 1)` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes st (w2n w) (ArrayTV elem (Dynamic n)) j b` by
    (first_x_assum irule >> decide_tac) >>
  gvs[Once dead_bytes_def] >>
  `w2n w + (i * type_slot_size elem + 1) <= j /\
   j < w2n w + ((i + 1) * type_slot_size elem + 1)` by
    (Cases_on `i < w2n (lookup_storage w st)` >> gvs[]
     >- (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >>
         simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
     gvs[arithmeticTheory.MULT_COMM]) >>
  `i = k` suffices_by (strip_tac >> gvs[]) >>
  Cases_on `i < k`
  >- (`(i + 1) * type_slot_size elem <= k * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >> decide_tac) >>
  Cases_on `k < i`
  >- (`(k + 1) * type_slot_size elem <= i * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> decide_tac
QED

Theorem nested_pop_live_tuple_element:
  !cx tr st w tvs k elem.
    storage_read_live cx tr st w (TupleTV tvs) /\ oEL k tvs = SOME elem ==>
    storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size k tvs)) elem
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >> strip_tac >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + n2w (tuple_prefix_slot_size k tvs)` mp_tac wordsTheory.w2n_lt >>
      decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + tuple_prefix_slot_size k tvs < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (tuple_prefix_slot_size k tvs)) =
   w2n w + tuple_prefix_slot_size k tvs` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) tvs j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def] >> decide_tac) >>
  irule nested_pop_dead_tuple_selected >> simp[] >>
  qexists `k` >> simp[]
QED

Theorem nested_pop_extend_storage_live:
  get_storage_backend cx tr st = (INL raw,st) /\
  storage_read_live cx tr raw slot tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ storage_read_live cx tr raw slot' tv'
Proof
  reverse (Cases_on `sb`)
  >- (Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def] >>
      irule accountsRelPropsTheory.storage_read_live_field >> metis_tac[]) >>
  Cases_on `v` >> Cases_on `tv` >> simp[extend_storage_place_def, raise_def]
  >~ [`storage_read_live _ _ _ _ (TupleTV _)`]
  >- (simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      irule nested_pop_live_tuple_element >> metis_tac[]) >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >>
  simp[resolve_array_element_def, bind_def, ignore_bind_def,
       lift_option_type_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperStoragePlaceProvenanceTheory.resolve_array_element_empty, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, return_def, raise_def, AllCaseEqs()]
  >- (irule nested_pop_live_fixed_element >> metis_tac[]) >>
  irule nested_pop_live_dynamic_element >> metis_tac[]
QED

Definition nested_pop_result_live_def:
  nested_pop_result_live cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       storage_read_live cx tr raw slot tv) /\
  nested_pop_result_live cx st (PlaceR _) = T /\
  nested_pop_result_live cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  nested_pop_result_live cx st (Value _) = T
End

Theorem nested_pop_mapping_leaf_live:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  storage_read_live cx tr raw slot tv
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  asm_simp_tac bool_ss [vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def,
                       optionTheory.option_case_def, APPEND_NIL] >>
  strip_tac >> drule accountsRelPropsTheory.declared_storage_region_read_live >> simp[]
QED

Theorem nested_pop_lookup_global_live:
  lookup_global cx mid var_name st = (INL pv,st') ==>
  nested_pop_result_live cx st pv
Proof
  Cases_on `pv` >> simp[nested_pop_result_live_def]
  >- (Cases_on `p` >> simp[nested_pop_result_live_def] >> rpt strip_tac >>
      drule lookup_global_storage_region >> strip_tac >>
      drule accountsRelPropsTheory.declared_storage_region_read_live >> simp[]) >>
  strip_tac >> drule lookup_global_mapping_region >> simp[]
QED

Theorem nested_pop_extend_result_live:
  nested_pop_result_live cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  nested_pop_result_live cx st pv'
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def, nested_pop_result_live_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`extend_storage_place _ _ _ _ _ _`]
      >- (drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
          simp[nested_pop_result_live_def] >> rpt strip_tac >>
          gvs[nested_pop_result_live_def] >>
          drule_all nested_pop_extend_storage_live >> simp[]) >>
      simp[extend_memory_place_def, nested_pop_result_live_def]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `v` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[nested_pop_result_live_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v'` assume_tac) >>
  simp[] >> rpt strip_tac >>
  irule nested_pop_mapping_leaf_live >> goal_assum (drule_at Any) >> simp[]
QED

Theorem nested_pop_eval_base_live:
  !bt cx st pv st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    nested_pop_result_live cx st pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      simp[nested_pop_result_live_def] >>
      metis_tac[nested_pop_lookup_global_live]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  simp[nested_pop_result_live_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[]
  >~ [`pure_expr e`]
  >- (drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule_all nested_pop_extend_result_live >> simp[]) >>
  drule_all nested_pop_extend_result_live >> simp[]
QED

Theorem nested_pop_eval_target_live:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  storage_read_live cx tr raw slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_live >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def,
                       nested_pop_result_live_def]
QED

Theorem nested_pop_eval_target_live_post:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st' = (INL raw,st') ==>
  storage_read_live cx tr raw slot tv
Proof
  rpt strip_tac >>
  drule_all nested_pop_eval_target_pure_state >> strip_tac >> gvs[] >>
  drule_all nested_pop_eval_target_live >> simp[]
QED
