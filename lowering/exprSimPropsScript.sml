(* Value-layout, local-frame and leaf-evaluation facts for simulations. *)
Theory exprSimProps
Ancestors
  exprSimDefs
  loweringPosts
  words list rich_list finite_map pred_set pair
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  valueEncoding valueEncodingDefs valueEncodingProofs vyperTypeSystem vyperTyping
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend vyperEvalPreservesScopes
  vyperPlaceStatePreservation vyperStoragePlaceProvenance
Libs
  pairLib

Definition val_store_size_def:
  val_store_size tv v =
    case v of
      BytesV bs =>
        (case tv of
           BaseTV (BytesT (Dynamic _)) => 32 + 32 * word_size (LENGTH bs)
         | _ => type_memory_size tv)
    | StringV str =>
        (case tv of
           BaseTV (StringT _) => 32 + 32 * word_size (LENGTH str)
         | _ => type_memory_size tv)
    | _ => type_memory_size tv
End

Theorem mem_path_offset_snoc:
  !path tv k ptv sb k2 etv.
    mem_path_offset tv path = SOME (k,ptv) /\
    mem_step_offset ptv sb = SOME (k2,etv) ==>
    mem_path_offset tv (path ++ [sb]) = SOME (k + k2,etv)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  first_x_assum drule_all >> simp[]
QED

Theorem mem_field_offset_sound:
  !fs fld k ftv.
    mem_field_offset fs fld = SOME (k,ftv) ==>
    ALOOKUP fs fld = SOME ftv /\
    k + type_memory_size ftv <= type_memory_size_fields fs
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  simp[mem_field_offset_def, type_memory_size_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[PULL_EXISTS, FORALL_PROD] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem type_memory_size_list_take_el[local]:
  !tvs n. n < LENGTH tvs ==>
    type_memory_size_list (TAKE n tvs) + type_memory_size (EL n tvs) <=
    type_memory_size_list tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `n` >>
  simp[type_memory_size_def] >> strip_tac >> res_tac >> simp[]
QED

Theorem mul_succ_le[local]:
  !i n. i < n ==> !s. i * s + s <= n * s
Proof
  rpt strip_tac >> REWRITE_TAC [GSYM arithmeticTheory.MULT] >>
  irule arithmeticTheory.LESS_MONO_MULT >> simp[]
QED

Theorem mem_step_offset_sound[local]:
  !tv sb k etv.
    mem_step_offset tv sb = SOME (k,etv) ==>
    subscript_type tv sb = SOME etv /\
    k + type_memory_size etv <= type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd`) >>
  simp[mem_step_offset_def, subscript_type_def, type_memory_size_def] >>
  rw[] >> gvs[] >>
  TRY (drule mem_field_offset_sound >> simp[] >> NO_TAC) >>
  TRY (drule type_memory_size_list_take_el >> simp[] >> NO_TAC) >>
  qpat_x_assum `Num _ < _` (mp_tac o MATCH_MP mul_succ_le) >>
  disch_then (qspec_then `type_memory_size etv` mp_tac) >> simp[]
QED

(* A path's offset is where the source's subscripts_type puts the path, and
   the place's bytes lie inside the type's. *)
Theorem mem_path_offset_sound:
  !path tv k ptv.
    mem_path_offset tv path = SOME (k,ptv) ==>
    subscripts_type tv path = SOME ptv /\
    k + type_memory_size ptv <= type_memory_size tv
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, subscripts_type_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  drule mem_step_offset_sound >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[subscripts_type_def]
QED

Theorem dynarray_len_at_root:
  !cenv n et m.
    cenv.ce_var_type n = SOME (ArrayT et (Dynamic m)) ==>
    dynarray_len_at cenv n 0
Proof
  rw[dynarray_len_at_def] >> qexists_tac `[]` >>
  simp[type_path_offset_def]
QED

Theorem local_path_at_root:
  !cenv cx n t0 tv0.
    cenv.ce_var_type n = SOME t0 /\
    evaluate_type (get_tenv cx) t0 = SOME tv0 ==>
    local_path_at cenv cx n 0 tv0
Proof
  rw[local_path_at_def] >> qexists_tac `[]` >> simp[mem_path_offset_def]
QED

(* A step from where a value sits gives where its part sits. *)
Theorem local_path_at_step:
  !cenv cx n k tv sb k2 etv.
    local_path_at cenv cx n k tv /\ mem_step_offset tv sb = SOME (k2,etv) ==>
    local_path_at cenv cx n (k + k2) etv
Proof
  rw[local_path_at_def] >> drule_all mem_path_offset_snoc >> metis_tac[]
QED

(* A local's own place sits at its root. *)
Theorem local_place_at_root:
  !cenv cx n t0 tv0.
    cenv.ce_var_type n = SOME t0 /\
    evaluate_type (get_tenv cx) t0 = SOME tv0 ==>
    local_place_at cenv cx n 0 tv0 (PlaceR (MemoryPlace n []))
Proof
  rw[local_place_at_def, mem_path_offset_def]
QED

(* A step from where a local's place sits gives where its extension sits,
   when the result is a memory place exactly as the step's extension. *)
Theorem local_place_at_step:
  !cenv cx n k tv tv0 sb k2 etv tv'.
    local_place_at cenv cx n k tv tv0 /\
    mem_step_offset tv sb = SOME (k2,etv) /\
    (!id path'. tv' = PlaceR (MemoryPlace id path') <=>
       ?path. path' = path ++ [sb] /\ tv0 = PlaceR (MemoryPlace id path)) ==>
    local_place_at cenv cx n (k + k2) etv tv'
Proof
  rpt gen_tac >> simp[local_place_at_def] >> strip_tac >>
  qx_genl_tac [`i`, `q`] >> disch_tac >>
  `?p. q = p ++ [sb] /\ tv0 = PlaceR (MemoryPlace i p)` by metis_tac[] >>
  gvs[] >> metis_tac[mem_path_offset_snoc]
QED

(* A selection's result is a memory place exactly when it extends one. *)
Theorem select_result_memory_place:
  !cx ty tv sb st tv' st'.
    select_result cx ty tv sb st = (INL tv', st') ==>
    !id path'. tv' = PlaceR (MemoryPlace id path') <=>
      ?path. path' = path ++ [sb] /\ tv = PlaceR (MemoryPlace id path)
Proof
  rpt gen_tac >> strip_tac >>
  `!id path. tv = PlaceR (MemoryPlace id path) ==>
     tv' = PlaceR (MemoryPlace id (path ++ [sb]))` by
    (rpt strip_tac >>
     gvs[select_result_def, extend_place_def, bind_def, return_def,
         lift_sum_def, raise_def, ignore_bind_def, AllCaseEqs(),
         extend_memory_place_def]) >>
  `!id path'. tv' = PlaceR (MemoryPlace id path') ==>
     ?path. tv = PlaceR (MemoryPlace id path)` by
    (rpt strip_tac >> gvs[] >> Cases_on `tv`
     >- gvs[select_result_def, bind_def, return_def, lift_option_type_def,
            lift_sum_def, raise_def, AllCaseEqs()]
     >- (rename1 `PlaceR pl` >> Cases_on `pl` >>
         gvs[select_result_def, extend_place_def, bind_def, return_def,
             lift_sum_def, raise_def, ignore_bind_def, AllCaseEqs(),
             extend_memory_place_def] >>
         drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
         simp[]) >>
     rename1 `HashMapRef _ _ _ vt` >> Cases_on `sb` >> Cases_on `vt` >>
     gvs[select_result_def, extend_place_def, bind_def, return_def,
         lift_option_type_def, raise_def, AllCaseEqs(), LET_THM]) >>
  rpt gen_tac >> eq_tac >> rw[] >> res_tac >> gvs[]
QED

(* A value of a base type is no place, so nothing pins it. *)
Theorem local_place_at_value[simp]:
  !cenv cx n k ptv v. local_place_at cenv cx n k ptv (Value v)
Proof
  simp[local_place_at_def]
QED

(* A located memory value is where expr_val_at says, dropping the pin. *)
Theorem vv_at_memory_val_at:
  !cenv cx t sa sb es tv t' p s v.
    vv_at cenv cx t sa sb es tv (LocatedValue t' p) s /\
    p.ptr_location = LocMemory /\ read_result cx tv es = (INL v, es) ==>
    expr_val_at cenv cx t sa sb es v p.ptr_operand s
Proof
  rw[vv_at_def, expr_val_at_def] >> first_x_assum drule_all >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem dynarray_free_step[local]:
  !tv sb k etv. dynarray_free tv /\ mem_step_offset tv sb = SOME (k,etv) ==>
                dynarray_free etv
Proof
  rw[dynarray_free_def] >> strip_tac >>
  first_x_assum (qspec_then `sb::path` mp_tac) >>
  simp[mem_path_offset_def]
QED

Theorem mem_field_offset_apart[local]:
  !fs id1 id2 k1 tv1 k2 tv2.
    mem_field_offset fs id1 = SOME (k1,tv1) /\
    mem_field_offset fs id2 = SOME (k2,tv2) /\ id1 <> id2 ==>
    k1 + type_memory_size tv1 <= k2 \/ k2 + type_memory_size tv2 <= k1
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  rpt gen_tac >> simp[mem_field_offset_def] >>
  rw[optionTheory.OPTION_MAP_EQ_SOME, EXISTS_PROD] >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem take_succ_sum_le[local]:
  !tvs i j. i < j /\ j <= LENGTH tvs ==>
    type_memory_size_list (TAKE i tvs) + type_memory_size (EL i tvs) <=
    type_memory_size_list (TAKE j tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `i` >> Cases_on `j` >>
  simp[type_memory_size_def] >> strip_tac >>
  first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[]
QED

Theorem num_lt_cases[local]:
  !i j. i <> j /\ 0 <= i /\ 0 <= j ==> Num i < Num j \/ Num j < Num i
Proof
  rpt strip_tac >> `Num i <> Num j` by metis_tac[integerTheory.INT_OF_NUM] >>
  decide_tac
QED

Theorem elems_apart[local]:
  !i j s c. i <> j /\ 0 <= i /\ 0 <= j ==>
    c + Num i * s + s <= c + Num j * s \/ c + Num j * s + s <= c + Num i * s
Proof
  rpt strip_tac >> drule_all num_lt_cases >> strip_tac
  >- (disj1_tac >> `Num i * s + s <= Num j * s` by metis_tac[mul_succ_le] >>
      decide_tac) >>
  disj2_tac >> `Num j * s + s <= Num i * s` by metis_tac[mul_succ_le] >>
  decide_tac
QED

Theorem fixed_elems_apart[local]:
  !i j s. i <> j /\ 0 <= i /\ 0 <= j ==>
    Num i * s + s <= Num j * s \/ Num j * s + s <= Num i * s
Proof
  rpt strip_tac >> drule_all elems_apart >>
  disch_then (qspecl_then [`s`, `0`] mp_tac) >> simp[]
QED

Theorem tuple_elems_apart[local]:
  !tvs i j. i <> j /\ 0 <= i /\ 0 <= j /\
            Num i < LENGTH tvs /\ Num j < LENGTH tvs ==>
    type_memory_size_list (TAKE (Num i) tvs) + type_memory_size (EL (Num i) tvs) <=
      type_memory_size_list (TAKE (Num j) tvs) \/
    type_memory_size_list (TAKE (Num j) tvs) + type_memory_size (EL (Num j) tvs) <=
      type_memory_size_list (TAKE (Num i) tvs)
Proof
  rpt strip_tac >> drule_all num_lt_cases >> strip_tac
  >- (disj1_tac >> irule take_succ_sum_le >> simp[]) >>
  disj2_tac >> irule take_succ_sum_le >> simp[]
QED

(* The shape of a step: a field of a struct, or an element of an array or
   a tuple. *)
Theorem mem_step_offset_shape:
  !tv sb k etv.
    mem_step_offset tv sb = SOME (k,etv) ==>
    (?fs id. tv = StructTV fs /\ sb = AttrSubscript id /\
             mem_field_offset fs id = SOME (k,etv)) \/
    (?i n. tv = ArrayTV etv (Fixed n) /\ sb = ValueSubscript (IntV i) /\
           0 <= i /\ Num i < n /\ k = Num i * type_memory_size etv) \/
    (?i n. tv = ArrayTV etv (Dynamic n) /\ sb = ValueSubscript (IntV i) /\
           0 <= i /\ Num i < n /\ k = 32 + Num i * type_memory_size etv) \/
    (?tvs i. tv = TupleTV tvs /\ sb = ValueSubscript (IntV i) /\
             0 <= i /\ Num i < LENGTH tvs /\
             k = type_memory_size_list (TAKE (Num i) tvs) /\
             etv = EL (Num i) tvs)
Proof
  rpt gen_tac >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript vv` >> Cases_on `vv`) >>
  Cases_on `tv` >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd`) >>
  simp[mem_step_offset_def] >> rw[] >> simp[]
QED

(* Two different steps from one type reach parts whose bytes are apart. *)
Theorem mem_step_offset_apart[local]:
  !tv sb1 sb2 k1 tv1 k2 tv2.
    mem_step_offset tv sb1 = SOME (k1,tv1) /\
    mem_step_offset tv sb2 = SOME (k2,tv2) /\ sb1 <> sb2 ==>
    k1 + type_memory_size tv1 <= k2 \/ k2 + type_memory_size tv2 <= k1
Proof
  rpt strip_tac >>
  qpat_x_assum `mem_step_offset _ sb1 = _`
    (strip_assume_tac o MATCH_MP mem_step_offset_shape) >>
  qpat_x_assum `mem_step_offset _ sb2 = _`
    (strip_assume_tac o MATCH_MP mem_step_offset_shape) >>
  rpt BasicProvers.VAR_EQ_TAC >> full_simp_tac (srw_ss()) [] >>
  rpt BasicProvers.VAR_EQ_TAC
  >~ [`mem_field_offset`] >- metis_tac[mem_field_offset_apart]
  >~ [`TAKE`] >- metis_tac[tuple_elems_apart]
  >~ [`32 + _`] >- metis_tac[elems_apart] >>
  metis_tac[fixed_elems_apart]
QED

Theorem mem_step_offset_dynarray_ge[local]:
  !etv m sb k tv.
    mem_step_offset (ArrayTV etv (Dynamic m)) sb = SOME (k,tv) ==> 32 <= k
Proof
  rpt strip_tac >> drule mem_step_offset_shape >> strip_tac >> gvs[]
QED

Theorem dynarray_free_base:
  !bt. dynarray_free (BaseTV bt)
Proof
  rw[dynarray_free_def] >> Cases_on `path` >>
  simp[mem_path_offset_def, AllCaseEqs(), optionTheory.OPTION_MAP_EQ_SOME,
       EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> drule mem_step_offset_shape >> simp[]
QED

Theorem dynarray_free_fixed:
  !etv n. dynarray_free etv ==> dynarray_free (ArrayTV etv (Fixed n))
Proof
  rw[dynarray_free_def] >> Cases_on `path` >>
  simp[mem_path_offset_def, AllCaseEqs(), optionTheory.OPTION_MAP_EQ_SOME,
       EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> drule mem_step_offset_shape >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* A value of a type free of dynamic arrays, on one path through tv0, is
   apart from the length word of any dynamic array on another. *)
Theorem mem_path_offset_dynarray_apart:
  !p1 tv0 p2 k1 tv k2 etv m.
    mem_path_offset tv0 p1 = SOME (k1,tv) /\ dynarray_free tv /\
    mem_path_offset tv0 p2 = SOME (k2, ArrayTV etv (Dynamic m)) ==>
    k1 + type_memory_size tv <= k2 \/ k2 + 32 <= k1
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[mem_path_offset_def, dynarray_free_def] >> metis_tac[]) >>
  rename1 `mem_path_offset tv0 (sb1::p1) = _` >>
  qpat_x_assum `mem_path_offset _ (sb1::_) = _` mp_tac >>
  simp[Once mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `mem_step_offset tv0 sb1 = SOME (j1,ptv1)` >>
  rename1 `mem_path_offset ptv1 p1 = SOME (j1',_)` >>
  Cases_on `p2`
  >- (gvs[mem_path_offset_def] >> drule mem_step_offset_dynarray_ge >> simp[]) >>
  rename1 `mem_path_offset tv0 (sb2::p2) = _` >>
  qpat_x_assum `mem_path_offset _ (sb2::_) = _` mp_tac >>
  simp[Once mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `mem_step_offset tv0 sb2 = SOME (j2,ptv2)` >>
  rename1 `mem_path_offset ptv2 p2 = SOME (j2',_)` >>
  Cases_on `sb1 = sb2`
  >- (gvs[] >> first_x_assum drule_all >> simp[]) >>
  qspecl_then [`p1`, `ptv1`, `j1'`, `tv`] mp_tac mem_path_offset_sound >>
  qspecl_then [`p2`, `ptv2`, `j2'`, `ArrayTV etv (Dynamic m)`] mp_tac
    mem_path_offset_sound >>
  qspecl_then [`tv0`, `sb1`, `sb2`, `j1`, `ptv1`, `j2`, `ptv2`] mp_tac
    mem_step_offset_apart >>
  simp[type_memory_size_def] >> rpt strip_tac >> decide_tac
QED

(* The bytes of a path dead in a value miss the length word of every
   dynamic array live in it: a dead path runs past the end of some array
   on the way, into slots no live path reaches. *)
Theorem mem_path_offset_dead_apart:
  !p1 tv0 v p2 k1 tv k2 etv m e w.
    evaluate_subscripts tv0 v p1 = INR e /\
    evaluate_subscripts tv0 v p2 = INL w /\
    mem_path_offset tv0 p1 = SOME (k1,tv) /\
    mem_path_offset tv0 p2 = SOME (k2, ArrayTV etv (Dynamic m)) ==>
    k1 + type_memory_size tv <= k2 \/ k2 + 32 <= k1
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[evaluate_subscripts_def] >>
  rename1 `mem_path_offset tv0 (sb1::p1) = _` >>
  qpat_x_assum `mem_path_offset _ (sb1::_) = _` mp_tac >>
  simp[Once mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `mem_step_offset tv0 sb1 = SOME (j1,ptv1)` >>
  rename1 `mem_path_offset ptv1 p1 = SOME (j1',_)` >>
  Cases_on `p2`
  >- (gvs[mem_path_offset_def] >> drule mem_step_offset_dynarray_ge >> simp[]) >>
  rename1 `mem_path_offset tv0 (sb2::p2) = _` >>
  qpat_x_assum `mem_path_offset _ (sb2::_) = _` mp_tac >>
  simp[Once mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `mem_step_offset tv0 sb2 = SOME (j2,ptv2)` >>
  rename1 `mem_path_offset ptv2 p2 = SOME (j2',_)` >>
  Cases_on `sb1 = sb2`
  >- (gvs[] >>
      `subscript_type tv0 sb1 = SOME ptv1` by
        (drule mem_step_offset_sound >> simp[]) >>
      drule vyperPlaceStatePreservationTheory.evaluate_subscripts_cons_typed >>
      disch_then (fn th => qspecl_then [`p1`, `v`] assume_tac th >>
                           qspecl_then [`p2`, `v`] assume_tac th) >>
      Cases_on `evaluate_subscripts tv0 v [sb1]` >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  qspecl_then [`p1`, `ptv1`, `j1'`, `tv`] mp_tac mem_path_offset_sound >>
  qspecl_then [`p2`, `ptv2`, `j2'`, `ArrayTV etv (Dynamic m)`] mp_tac
    mem_path_offset_sound >>
  qspecl_then [`tv0`, `sb1`, `sb2`, `j1`, `ptv1`, `j2`, `ptv2`] mp_tac
    mem_step_offset_apart >>
  simp[type_memory_size_def] >> rpt strip_tac >> decide_tac
QED

Theorem snapshot_in_mem_agree:
  !tv b sz h m m'.
    snapshot_in tv b sz h m /\ mem_bytes_at b sz m' = mem_bytes_at b sz m ==>
    snapshot_in tv b sz h m'
Proof
  rpt gen_tac >> PairCases_on `h` >> rw[snapshot_in_def] >>
  qexistsl_tac [`k`, `ptv`] >> simp[] >>
  irule (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
  simp[] >> qexists_tac `m` >> simp[] >>
  drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`b + k`, `type_memory_size ptv`] mp_tac) >>
  simp[]
QED

Theorem locals_kept_mem_tail:
  !cenv es es' s0 t u.
    locals_kept cenv es es' s0 t /\ u.vs_memory = t.vs_memory ==>
    locals_kept cenv es es' s0 u
Proof
  rw[locals_kept_def, popped_kept_def] >> metis_tac[]
QED

Theorem popped_kept_refl[simp]:
  !cenv es es' s. es'.scopes = es.scopes ==> popped_kept cenv es es' s s
Proof
  rw[popped_kept_def] >> gvs[] >> metis_tac[]
QED

Theorem locals_kept_refl[simp]:
  !cenv es es' s. es'.scopes = es.scopes ==> locals_kept cenv es es' s s
Proof
  rw[locals_kept_def, popped_kept_def] >> gvs[]
QED

Theorem locals_kept_mem:
  !cenv es es' s0 s.
    es'.scopes = es.scopes /\ s.vs_memory = s0.vs_memory ==>
    locals_kept cenv es es' s0 s
Proof
  metis_tac[locals_kept_mem_tail, locals_kept_refl]
QED

Theorem locals_kept_inst_idx[simp]:
  !cenv es es' s0 s k.
    locals_kept cenv es es' s0 (s with vs_inst_idx := k) <=>
    locals_kept cenv es es' s0 s
Proof
  simp[locals_kept_def, popped_kept_def]
QED

Theorem locals_kept_regions_tail:
  !cenv es es' s0 s t.
    locals_kept cenv es es' s0 s /\
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
    locals_kept cenv es es' s0 t
Proof
  rpt gen_tac >> simp[locals_kept_def] >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz. local_region _ _ _ n b sz ==> _` drule >>
      strip_tac >>
      drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
      disch_then (qspecl_then [`off`, `len`] mp_tac) >>
      impl_tac >- decide_tac >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >- (rpt strip_tac >> metis_tac[]) >>
  fs[popped_kept_def] >> rpt strip_tac >>
  irule snapshot_in_mem_agree >> metis_tac[]
QED

Theorem locals_kept_regions:
  !cenv es s0 s.
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
    locals_kept cenv es es s0 s
Proof
  metis_tac[locals_kept_regions_tail, locals_kept_refl]
QED

Theorem expr_val_at_start_mono:
  sa.cs_next_id <= s1.cs_next_id /\
  expr_val_at cenv cx ty s1 sm es v p s ==>
  expr_val_at cenv cx ty sa sm es v p s
Proof
  simp[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem expr_val_own_start_mono:
  sa.cs_next_id <= s1.cs_next_id /\
  expr_val_own cenv cx ty s1 sm es v p s ==>
  expr_val_own cenv cx ty sa sm es v p s
Proof
  simp[expr_val_own_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> qexists_tac `w` >> simp[] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem expr_val_rel_mem_agree:
  !cx t v op s s' w tv.
    expr_val_rel cx t v op s /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ val_wf tv v /\
    mem_bytes_at (w2n w) (type_memory_size tv) s.vs_memory =
      mem_bytes_at (w2n w) (type_memory_size tv) s'.vs_memory ==>
    expr_val_rel cx t v op s'
Proof
  rw[expr_val_rel_def] >> gvs[] >>
  qspecl_then [`tv`, `v`, `w2n w`, `type_memory_size tv`, `s.vs_memory`,
               `s'.vs_memory`] mp_tac
    valueEncodingPropsTheory.val_in_memory_mem_agree >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem le_word_size_mul:
  !n. n <= 32 * word_size n
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  `(n + 31) MOD 32 < 32` by simp[] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >> decide_tac
QED

Theorem buffer_round_mask:
  !w:bytes32. w && i2w (- &32) = (w >>> 5) << 5
Proof
  `i2w (- &32):bytes32 = (-1w:bytes32) << 5` by
    (simp[integer_wordTheory.i2w_def] >> CONV_TAC wordsLib.WORD_EVAL_CONV) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp_tac (bool_ss ++ fcpLib.FCP_ss)
    [wordsTheory.word_and_def, wordsTheory.word_lsl_def,
     wordsTheory.word_lsr_def, wordsTheory.WORD_NEG_1, wordsTheory.word_T] >>
  rpt strip_tac >> Cases_on `5 <= i` >>
  asm_simp_tac (arith_ss ++ fcpLib.FCP_ss) [wordsTheory.WORD_NEG_1, wordsTheory.word_T]
QED

Theorem word_size_le_of_le_mul[local]:
  !len k. len <= 32 * k ==> word_size len <= k
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  `(32 * k + 31) DIV 32 = k` by
    (once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  `(len + 31) DIV 32 <= (32 * k + 31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  gvs[]
QED

Theorem val_size_cases[local]:
  !tv v.
    (?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
    (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
    (val_footprint tv v = type_memory_size tv /\
     val_store_size tv v = type_memory_size tv)
Proof
  rpt gen_tac >> Cases_on `v` >> simp[val_footprint_def, val_store_size_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[]
QED

Theorem val_footprint_le:
  !tv v. val_wf tv v ==> val_footprint tv v <= type_memory_size tv
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    metis_tac[val_size_cases]
  >- (gvs[val_footprint_def, valueEncodingDefsTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      qspec_then `n` mp_tac le_word_size_mul >> decide_tac)
  >- (gvs[val_footprint_def, valueEncodingDefsTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      qspec_then `n` mp_tac le_word_size_mul >> decide_tac) >>
  simp[]
QED

(* A value sits where local_path_at puts its type. *)
Theorem local_path_at_val_at:
  !cenv cx n k tv v.
    local_path_at cenv cx n k tv ==> local_val_at cenv cx n k tv v
Proof
  simp[local_val_at_def]
QED

(* A base value no bigger than one where local_val_at puts it sits there
   too: a bytestring convert keeps the pointer. *)
Theorem local_val_at_base:
  !cenv cx n k bt1 v bt2 v2.
    local_val_at cenv cx n k (BaseTV bt1) v /\ val_wf (BaseTV bt1) v /\
    val_footprint (BaseTV bt2) v2 <= val_footprint (BaseTV bt1) v ==>
    local_val_at cenv cx n k (BaseTV bt2) v2
Proof
  rw[local_val_at_def] >> disj2_tac
  >- (qexists_tac `bt1` >> drule val_footprint_le >> simp[]) >>
  qexists_tac `bt0` >> simp[]
QED

Theorem immutable_holds_memory_cong:
  s'.vs_memory = s.vs_memory ==>
  (immutable_holds cenv cx t tv w es s' <=> immutable_holds cenv cx t tv w es s)
Proof
  simp[immutable_holds_def]
QED

(* A value inside the value w points to, j bytes further on (sub_layout),
   is at w + j. *)
Theorem immutable_holds_sub:
  !cenv cx t tv w es s stv sv j ft ftv fv tv'.
    immutable_holds cenv cx t tv w es s /\
    read_result cx tv es = (INL sv, es) /\
    evaluate_type (get_tenv cx) t = SOME stv /\
    sub_layout stv sv j ftv fv /\
    evaluate_type (get_tenv cx) ft = SOME ftv /\ value_has_type ftv fv /\
    read_result cx tv' es = (INL fv, es) ==>
    immutable_holds cenv cx ft tv' (w + n2w j) es s
Proof
  rpt strip_tac >> fs[immutable_holds_def] >> gvs[] >>
  qexistsl [`name`, `off`, `itv`, `iv`, `k + j`] >>
  simp[wordsTheory.word_add_n2w]
  >~ [`sub_layout itv iv k stv sv`]
  >- (disj1_tac >> fs[sub_layout_def] >> rpt strip_tac >> TRY decide_tac >>
      res_tac >> res_tac >> fs[]) >>
  disj2_tac >> fs[sub_layout_def] >>
  first_x_assum drule >> strip_tac >> fs[] >> decide_tac
QED

Theorem val_footprint_le_store_size:
  !tv v. val_footprint tv v <= val_store_size tv v
Proof
  rpt gen_tac >>
  qspecl_then [`tv`, `v`] strip_assume_tac val_size_cases >>
  gvs[val_footprint_def, val_store_size_def, le_word_size_mul]
QED

Theorem val_store_size_le:
  !tv v. val_wf tv v ==> val_store_size tv v <= type_memory_size tv
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_store_size tv v = type_memory_size tv` by
    metis_tac[val_size_cases]
  >- (gvs[val_store_size_def, valueEncodingDefsTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      irule word_size_le_of_le_mul >> simp[])
  >- (gvs[val_store_size_def, valueEncodingDefsTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      irule word_size_le_of_le_mul >> simp[]) >>
  simp[]
QED

Theorem val_in_memory_footprint_agree:
  !tv v off mem mem'.
    val_in_memory tv v off mem /\ val_wf tv v /\
    mem_bytes_at off (val_footprint tv v) mem =
      mem_bytes_at off (val_footprint tv v) mem' ==>
    val_in_memory tv v off mem'
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    metis_tac[val_size_cases]
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH bs) mem' =
       mem_bytes_at (off + 32) (LENGTH bs) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >>
      simp[])
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH str) mem' =
       mem_bytes_at (off + 32) (LENGTH str) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >>
      simp[]) >>
  qpat_x_assum `val_footprint _ _ = _` (fn th => fs[th]) >>
  qspecl_then [`tv`, `v`, `off`, `type_memory_size tv`, `mem`, `mem'`]
    mp_tac valueEncodingPropsTheory.val_in_memory_mem_agree >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem expr_val_rel_footprint_agree:
  !cx t v op s s' w tv.
    expr_val_rel cx t v op s /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ val_wf tv v /\
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory ==>
    expr_val_rel cx t v op s'
Proof
  rw[expr_val_rel_def] >> gvs[] >>
  irule val_in_memory_footprint_agree >> simp[] >>
  qexists_tac `s.vs_memory` >> simp[]
QED

Theorem stmt_state_rel_vars_frame:
  !func cenv cx es s V ctx.
    stmt_state_rel ctx func cenv cx es s /\
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p (s with vs_vars := V) = lookup_var p s) /\
    (!p. cenv.ce_imm_alloca = SOME (Var p) ==>
       lookup_var p (s with vs_vars := V) = lookup_var p s) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  rpt strip_tac >>
  `immutable_base_zero cenv (s with vs_vars := V)` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def]) >>
  `local_ptrs_rel func cenv es.scopes (s with vs_vars := V)` by
    (irule local_ptrs_rel_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >> conj_tac
     >- metis_tac[] >>
     rpt strip_tac >> gvs[]) >>
  `alloca_inv (s with vs_vars := V)` by
    (irule alloca_inv_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `alloca_room ctx func (s with vs_vars := V)` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `fmp_room ctx func (s with vs_vars := V)` by
    (irule fmp_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `immutable_alloca_sep func cenv cx es (s with vs_vars := V)` by
    (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     fs[stmt_state_rel_def] >>
     rpt strip_tac >> qexists_tac `id` >>
     fs[local_region_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, state_rel_def,
     storage_rel_def, transient_rel_def,
     immutables_rel_def, logs_rel_def, contract_storage_def,
     contract_transient_def] >>
  metis_tac[]
QED

Theorem stmt_state_rel_vars_ext:
  !func cenv cx es t t' ctx.
    stmt_state_rel ctx func cenv cx es t /\ vars_ext t t' ==>
    stmt_state_rel ctx func cenv cx es t'
Proof
  rw[vars_ext_def] >>
  qpat_x_assum `t' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac
  >~ [`cenv.ce_imm_alloca = SOME (Var p)`]
  >- (fs[stmt_state_rel_def, immutable_base_zero_def, eval_operand_def,
         lookup_var_def] >>
      metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[lookup_var_def] >> metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem stmt_state_rel_drop_fresh:
  !func cenv cx es st s ctx.
    local_ptrs_reserved cenv st ==>
    (stmt_state_rel ctx func cenv cx es (drop_fresh st s) <=>
     stmt_state_rel ctx func cenv cx es s)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (irule stmt_state_rel_vars_ext >> qexists_tac `drop_fresh st s` >>
      simp[vars_ext_drop_fresh]) >>
  simp[drop_fresh_def] >> irule stmt_state_rel_vars_frame >> simp[] >>
  rpt strip_tac >> simp[GSYM drop_fresh_def] >>
  irule lookup_var_drop_fresh >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem typed_val_to_w256_word_value:
  !tv v. word_value v ==> typed_val_to_w256 tv v = val_to_w256 v
Proof
  rw[word_value_def] >> Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

(* Word memory representation is independent of entry decoding. *)
Theorem val_in_memory_word:
  !tenv ty tv v off mem.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v ==>
    (val_in_memory tv v off mem <=>
     mem_word_at off mem = typed_val_to_w256 tv v)
Proof
  rpt strip_tac >>
  `(?n. ty = BaseT (UintT n)) \/ (?n. ty = BaseT (IntT n)) \/
   ty = BaseT BoolT \/ ty = BaseT AddressT \/ ty = BaseT DecimalT \/
   (?m. ty = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. ty = FlagT n)` by
    (Cases_on `ty` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
      typed_val_to_w256_def]
QED

Theorem val_in_memory_word_type:
  !tenv t tvt v off mem.
    is_word_type t /\ evaluate_type tenv t = SOME tvt /\
    value_has_type tvt v /\ val_in_memory tvt v off mem ==>
    mem_word_at off mem = typed_val_to_w256 tvt v
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
      typed_val_to_w256_def]
QED

Theorem eval_expr_env:
  !cx ann item es res es'.
    (do result <- eval_expr cx (Builtin ann (Env item) []); read_result cx result od) es = (res, es') /\
    expr_res_ok res /\ item <> PrevHash /\ item <> MsgGas ==>
    es' = es /\
    ?v. res = INL v /\
        evaluate_builtin cx es.accounts ann (Env item) [] [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `item` >> fs[evaluate_builtin_def, return_def, raise_def] >>
  rw[] >> gvs[expr_res_ok_def, read_result_def, return_def]
QED

Theorem lower_value_env:
  !cenv ty ann item sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Env item) []) sa =
      (op, sb) ==>
    compile_env_var item sa = (op, sb)
Proof
  rpt gen_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def] >>
  Cases_on `compile_env_var item sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

Theorem eval_expr_flag_member:
  !cx ann src fid mid es res es'.
    (do result <- eval_expr cx (FlagMember ann (src, fid) mid); read_result cx result od) es = (res, es') /\
    expr_res_ok res ==>
    es' = es /\
    ?ts ls i. get_module_code cx src = SOME ts /\
              lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i /\
              res = INL (FlagV (2 ** i))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, lookup_flag_mem_def] >>
  Cases_on `get_module_code cx src` >>
  gvs[bind_def, raise_def, return_def, expr_res_ok_def] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `lookup_flag fid ts` >>
  gvs[bind_def, raise_def, return_def, expr_res_ok_def] >>
  rename1 `lookup_flag fid ts = SOME ls` >>
  Cases_on `INDEX_OF mid ls` >>
  gvs[bind_def, read_result_def, raise_def, return_def, expr_res_ok_def]
QED

Theorem eval_expr_flag_member_gas:
  gas_admissible
    (bind (eval_expr cx (FlagMember ann (src,fid) mid)) (read_result cx))
    expr_res_ok es ==>
  ?ts ls i. get_module_code cx src = SOME ts /\
    lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i /\
    (!tail. bind (eval_expr cx (FlagMember ann (src,fid) mid))
       (read_result cx) (es with gas_obs := tail) =
       (INL (FlagV (2 ** i)), es with gas_obs := tail))
Proof
  strip_tac >>
  Cases_on `bind (eval_expr cx (FlagMember ann (src,fid) mid))
    (read_result cx) (es with gas_obs := [])` >>
  drule_all gasContextTheory.gas_admissible_result >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] eval_expr_flag_member) >>
  strip_tac >>
  qexistsl [`ts`, `ls`, `i`] >> simp[] >>
  simp[Once evaluate_def, lookup_flag_mem_def, bind_def,
       read_result_def, return_def]
QED

(* Pointer variables and scope domains determine live local regions. *)
Theorem local_region_frame:
  !func cenv scopes0 s0 sa scopes t n b sz.
    local_ptrs_rel func cenv scopes0 s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM scopes0 = MAP FDOM scopes /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    local_region cenv scopes t n b sz ==>
    local_region cenv scopes0 s0 n b sz
Proof
  rw[local_region_def] >>
  `lookup_scopes n scopes0 <> NONE` by
    metis_tac[lookup_scopes_none_map_fdom, optionTheory.NOT_SOME_NONE] >>
  Cases_on `lookup_scopes n scopes0` >> fs[] >>
  rename1 `lookup_scopes n scopes0 = SOME e0` >>
  `?w0. lookup_var p s0 = SOME w0` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p t = SOME w0` by metis_tac[] >> gvs[]
QED

(* The converse needs only preservation of pointers already present. *)
Theorem local_region_frame_fwd:
  !cenv scopes0 sa scopes s0 t n b sz.
    local_ptrs_reserved cenv sa /\ MAP FDOM scopes0 = MAP FDOM scopes /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    local_region cenv scopes0 s0 n b sz ==>
    local_region cenv scopes t n b sz
Proof
  rw[local_region_def] >>
  `lookup_scopes n scopes <> NONE` by
    metis_tac[lookup_scopes_none_map_fdom, optionTheory.NOT_SOME_NONE] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `lookup_scopes n scopes` >> gvs[]
QED

Theorem vv_post_initial_gas:
  vv_post ctx func cenv cx e (es with gas_obs := gs) sa sb s0 ee tv vv t <=>
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv t
Proof
  simp[vv_post_def, locals_kept_def, popped_kept_def]
QED

Theorem eval_expr_literal_value:
  !cx ann l es tv es'.
    eval_expr cx (Literal ann l) es = (INL tv, es') ==> ?v. tv = Value v
Proof
  simp[Once evaluate_def, return_def]
QED


Theorem word_tv_memory_size:
  !tenv t tv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    type_memory_size tv = 32
Proof
  Cases_on `t` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_word_type_def]) >>
      simp[evaluate_type_def, type_memory_size_def]) >>
  simp[evaluate_type_def, AllCaseEqs()] >> rw[] >>
  simp[type_memory_size_def]
QED

(* Original proof before making the word bound explicit in this owner.
Proof
  rpt strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (w + n2w off) = w2n w + w2n ((n2w off):bytes32)`
    suffices_by simp[] >>
  irule wordsTheory.w2n_add_2 >> simp[] >> decide_tac
QED
*)
Theorem buffer_offset_no_wrap:
  !w:bytes32. !off sz.
    w2n w + sz < dimword (:256) /\ off <= sz ==>
    w2n (w + n2w off) = w2n w + off

Proof
  rpt strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (w + n2w off) = w2n w + w2n ((n2w off):bytes32)`
    suffices_by simp[] >>
  irule wordsTheory.w2n_add_2 >> gvs[wordsTheory.dimword_def] >> decide_tac
QED

Theorem stmt_state_rel_region_lt:
  !func cenv cx es s ctx.
    stmt_state_rel ctx func cenv cx es s ==>
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
                b + sz < dimword (:256)) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
              b + sz < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  conj_tac
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  rw[local_region_def] >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  res_tac >> gvs[] >> DECIDE_TAC
QED
