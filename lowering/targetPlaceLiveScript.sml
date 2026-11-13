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
  compileEnv loweringStateRelDefs accountsRelProps exprSimPopStorage allocLimits allocLimitsProps
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

Theorem alloc_limits_target_indices_not_extcode:
  alloc_limits_target cenv t ==>
  EVERY (\e. ~is_extcode e) (target_indices t)
Proof
  `(!e:expr. T) /\ (!t. alloc_limits_target cenv t ==>
      EVERY (\e. ~is_extcode e) (target_indices t))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_indices_def, alloc_limits_expr_def] >>
  metis_tac[alloc_limits_expr_not_extcode]
QED

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
      pure_once_rewrite_tac[loweringStateRelDefsTheory.dead_bytes_def] >>
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
      rename1 `a < n'` >> pure_once_rewrite_tac[loweringStateRelDefsTheory.dead_bytes_def] >>
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
      rename1 `a < n'` >> pure_once_rewrite_tac[loweringStateRelDefsTheory.dead_bytes_def] >>
      qexists `a` >> simp[] >>
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
    eval_base_place cx bt st = (res,st') ==>
    st' = st with storage_trace := st'.storage_trace
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
  rpt strip_tac >> gvs[evaluation_state_component_equality] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  imp_res_tac eval_expr_preserves_state >> imp_res_tac read_result_state >>
  imp_res_tac extend_place_state >> gvs[] >>
  fs[evaluation_state_component_equality]
QED

Theorem nested_pop_eval_target_pure_state:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (res,st') ==>
  st' = st with storage_trace := st'.storage_trace
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac nested_pop_eval_base_pure_state >> gvs[] >>
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
  !H tr st w elem n k.
    storage_read_live H tr st w (ArrayTV elem (Fixed n)) /\ k < n ==>
    storage_read_live H tr st (w + n2w (k * type_slot_size elem)) elem
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
  !H tr st w elem n k.
    storage_read_live H tr st w (ArrayTV elem (Dynamic n)) /\
    k < n /\ k < w2n (lookup_storage w st) ==>
    storage_read_live H tr st (w + n2w (k * type_slot_size elem + 1)) elem
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
    (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >>
     simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
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
  !H tr st w tvs k elem.
    storage_read_live H tr st w (TupleTV tvs) /\ oEL k tvs = SOME elem ==>
    storage_read_live H tr st (w + n2w (tuple_prefix_slot_size k tvs)) elem
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
  storage_read_live H tr raw slot tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ storage_read_live H tr raw slot' tv'
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

(* A storage place's slots are read live by the horizon H.  Only a storage
   place carries a fact: a mapping's leaf becomes a storage place by
   recording its root in the trace (extend_place), so its liveness comes
   from the horizon of the trace that records it. *)
Definition nested_pop_result_live_def:
  nested_pop_result_live H cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       storage_read_live H tr raw slot tv) /\
  nested_pop_result_live H cx st (PlaceR _) = T /\
  nested_pop_result_live H cx st (HashMapRef tr slot kt vt) = T /\
  nested_pop_result_live H cx st (Value _) = T
End

Theorem nested_pop_result_live_trace[simp]:
  nested_pop_result_live H cx (st with storage_trace := obs) pv =
  nested_pop_result_live H cx st pv
Proof
  Cases_on `pv` >> simp[nested_pop_result_live_def] >>
  Cases_on `p` >>
  simp[nested_pop_result_live_def,
       vyperStorageBackendTheory.get_storage_backend_eq]
QED

(* A root recorded in a trace the horizon covers is read live. *)
Theorem nested_pop_root_live[local]:
  valid_horizon cx st0 H (obs ++ [StorageRoot tr slot tv]) ==>
  storage_read_live H tr raw (n2w slot) tv
Proof
  strip_tac >>
  irule accountsRelPropsTheory.observed_storage_region_read_live >>
  gvs[vyperStorageFootprintTheory.valid_horizon_def,
      vyperStorageFootprintTheory.storage_observations_ok_def,
      vyperStorageFootprintTheory.storage_trace_regions_def]
QED

Theorem nested_pop_lookup_global_live:
  lookup_global cx mid var_name st = (INL pv,st') /\
  valid_horizon cx st0 H st'.storage_trace ==>
  nested_pop_result_live H cx st pv
Proof
  Cases_on `pv` >> simp[nested_pop_result_live_def] >>
  Cases_on `p` >> simp[nested_pop_result_live_def] >>
  simp[lookup_global_def, ignore_bind_def, record_storage_event_def,
       bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def,
      record_storage_event_def, ignore_bind_def,
      return_def, raise_def, AllCaseEqs()] >>
  metis_tac[nested_pop_root_live]
QED

Theorem nested_pop_extend_result_live:
  nested_pop_result_live H cx st pv /\
  extend_place cx pv sb st = (INL pv',st') /\
  valid_horizon cx st0 H st'.storage_trace ==>
  nested_pop_result_live H cx st pv'
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
  simp[value_type_CASE_rator, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[record_storage_event_def, return_def, AllCaseEqs(),
      nested_pop_result_live_def] >>
  metis_tac[nested_pop_root_live, wordsTheory.n2w_w2n]
QED

Theorem nested_pop_eval_base_live:
  !bt cx st pv st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') /\
    valid_horizon cx st0 H st'.storage_trace ==>
    nested_pop_result_live H cx st pv
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
  rename1 `eval_base_place cx b st = (INL bpv,s1)` >>
  `valid_horizon cx st0 H s1.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.valid_horizon_frame,
              vyperStorageTraceTheory.storage_trace_frame_extend_place,
              vyperStorageTraceTheory.storage_trace_frame_read_result,
              cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >>
  qmatch_assum_rename_tac `extend_place _ _ _ s3 = (INL pv,st')` >>
  `s3 = st with storage_trace := s3.storage_trace` by
    (imp_res_tac eval_expr_preserves_state >> imp_res_tac read_result_state >>
     gvs[] >> fs[evaluation_state_component_equality]) >>
  `nested_pop_result_live H cx s3 bpv` by
    (pop_assum SUBST1_TAC >> metis_tac[nested_pop_result_live_trace]) >>
  drule_all nested_pop_extend_result_live >>
  qpat_x_assum `s3 = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem nested_pop_eval_target_live:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  valid_horizon cx st0 H st'.storage_trace /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  storage_read_live H tr raw slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all nested_pop_eval_base_live >> strip_tac >>
  gvs[nested_pop_result_live_def]
QED

Theorem nested_pop_eval_target_live_post:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  valid_horizon cx st0 H st'.storage_trace /\
  get_storage_backend cx tr st' = (INL raw,st') ==>
  storage_read_live H tr raw slot tv
Proof
  rpt strip_tac >>
  drule_all nested_pop_eval_target_pure_state >> strip_tac >>
  `get_storage_backend cx tr st = (INL raw,st)` by
    (qpat_x_assum `get_storage_backend _ _ st' = _` mp_tac >>
     qpat_x_assum `st' = _` (fn th => once_rewrite_tac[th]) >>
     simp[vyperStorageBackendTheory.get_storage_backend_eq]) >>
  metis_tac[nested_pop_eval_target_live]
QED
