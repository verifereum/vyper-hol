(* Append extends the initialized memory prefix at the element stride. *)
Theory appendMemoryRel
Ancestors
  abiDecoderArrayPrefix abiDecodeStaticProps valueEncodingProps valueEncodingProofs valueEncodingDefs
  placeStore valueEncodingTyping venomState words list arithmetic
  bodySimAugPlaceLoad supportedTypes memoryValueEncoding loweringStateRelDefs
  exprLoweringProps exprSimHypsDefs exprSimProps loweringPosts
  vyperTypeInvariants vyperPlaceStatePreservation bodySim exprSimHyps

Theorem append_memory_representation_general:
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    off s.vs_memory /\
  elems_val_wf vs tv /\ val_wf tv v /\
  val_in_memory tv v (off + 32 + LENGTH vs * type_memory_size tv)
    data.vs_memory /\
  (!q. q < off + 32 + LENGTH vs * type_memory_size tv \/
       off + 32 + (LENGTH vs + 1) * type_memory_size tv <= q ==>
       mem_bytes_at q 1 data.vs_memory = mem_bytes_at q 1 s.vs_memory) ==>
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (vs ++ [v])))
    off (mstore off (n2w (LENGTH vs + 1)) data).vs_memory
Proof
  strip_tac >>
  `elems_in_memory vs (off + 32) tv data.vs_memory` by
    (irule (cj 3 val_in_memory_mem_agree_proof) >> simp[] >>
     qexists_tac `s.vs_memory` >> gvs[val_in_memory_def] >>
     sym_tac >> irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `elems_in_memory vs (off + 32) tv
    (mstore off (n2w (LENGTH vs + 1)) data).vs_memory` by
    (`mstore off (n2w (LENGTH vs + 1)) data =
      mstore off (n2w (LENGTH vs + 1))
        (data with vs_memory := data.vs_memory)` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule (cj 3 mstore_preserves_val_in_memory) >> simp[]) >>
  `val_in_memory tv v (off + 32 + LENGTH vs * type_memory_size tv)
    (mstore off (n2w (LENGTH vs + 1)) data).vs_memory` by
    (`mstore off (n2w (LENGTH vs + 1)) data =
      mstore off (n2w (LENGTH vs + 1))
        (data with vs_memory := data.vs_memory)` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule (cj 1 mstore_preserves_val_in_memory) >> simp[]) >>
  simp_tac std_ss [Once val_in_memory_def, LENGTH_APPEND, LENGTH] >>
  conj_tac >- simp[mstore_mem_word_at_same] >>
  asm_simp_tac std_ss [elems_in_memory_append, val_in_memory_def,
                      vyperValueTheory.type_value_case_def]
QED

Theorem append_memory_word_representation:
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    off s.vs_memory /\
  elems_val_wf vs tv /\ val_wf tv v /\ type_memory_size tv = 32 /\
  val_in_memory tv v (off + 32 * (1 + LENGTH vs))
    (mstore (off + 32 * (1 + LENGTH vs)) w s).vs_memory ==>
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (vs ++ [v])))
    off (mstore off (n2w (LENGTH vs + 1))
      (mstore (off + 32 * (1 + LENGTH vs)) w s)).vs_memory
Proof
  strip_tac >> irule append_memory_representation_general >>
  gvs[LEFT_ADD_DISTRIB] >> qexists_tac `s` >> simp[LEFT_ADD_DISTRIB] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem append_memory_state_general:
  stmt_state_rel H ctx func cenv cx es s /\
  expr_sim_inv cenv cx env es /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp
    (SOME LocMemory) (Type dty) /\
  (!entry t0. lookup_scopes id es.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) dty = SOME (ArrayTV tv (Dynamic cap)) /\
  write_place cx (MemoryPlace id path)
    (ArrayV (DynArrayV (vs ++ [v]))) es = (INL (),ff) /\
  value_has_type (ArrayTV tv (Dynamic cap))
    (ArrayV (DynArrayV (vs ++ [v]))) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    (w2n bp) s.vs_memory /\ LENGTH vs < cap /\
  val_in_memory tv v (w2n bp + 32 + LENGTH vs * type_memory_size tv)
    data.vs_memory /\
  data = s with vs_memory := data.vs_memory /\
  LENGTH s.vs_memory <= LENGTH data.vs_memory /\
  (!q. q < w2n bp + 32 + LENGTH vs * type_memory_size tv \/
       w2n bp + 32 + (LENGTH vs + 1) * type_memory_size tv <= q ==>
       mem_bytes_at q 1 data.vs_memory = mem_bytes_at q 1 s.vs_memory) ==>
  stmt_state_rel H ctx func cenv cx ff
    (mstore (w2n bp) (n2w (LENGTH vs + 1)) data)
Proof
  strip_tac >>
  `all_have_type tv vs /\ value_has_type tv v` by
    fs[vyperTypingTheory.value_has_type_def,
       vyperTypingTheory.all_have_type_EVERY, EVERY_APPEND] >>
  `elems_val_wf vs tv /\ val_wf tv v` by
    metis_tac[value_has_type_val_wf] >>
  drule_all append_memory_representation_general >> strip_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx func cenv cx ff out` >>
  `out = s with vs_memory := out.vs_memory` by
    (qunabbrev_tac `out` >>
     qpat_x_assum `data = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [mstore_def, LET_THM]) >>
  pop_assum SUBST1_TAC >>
  irule place_store_pointer_memory_state >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[] >>
  conj_tac
  >- simp[Abbr `out`, venomMemPropsTheory.LENGTH_mstore_eq] >>
  rpt strip_tac >>
  `mem_bytes_at q 1 out.vs_memory = mem_bytes_at q 1 data.vs_memory` by
    (qunabbrev_tac `out` >> irule mstore_mem_bytes_at_disjoint >>
     gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  qpat_x_assum `mem_bytes_at q 1 out.vs_memory = _` SUBST1_TAC >>
  sym_tac >> first_x_assum irule >>
  gvs[valueEncodingTheory.type_memory_size_def] >>
  ` (LENGTH vs + 1) * type_memory_size tv <= cap * type_memory_size tv` by
    simp[] >> decide_tac
QED

Theorem append_memory_word_state:
  stmt_state_rel H ctx func cenv cx es s /\
  expr_sim_inv cenv cx env es /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp
    (SOME LocMemory) (Type dty) /\
  (!entry t0. lookup_scopes id es.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) dty = SOME (ArrayTV tv (Dynamic cap)) /\
  write_place cx (MemoryPlace id path)
    (ArrayV (DynArrayV (vs ++ [v]))) es = (INL (),ff) /\
  value_has_type (ArrayTV tv (Dynamic cap))
    (ArrayV (DynArrayV (vs ++ [v]))) /\
  val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    (w2n bp) s.vs_memory /\ type_memory_size tv = 32 /\ LENGTH vs < cap /\
  val_in_memory tv v (w2n bp+32*(1+LENGTH vs))
    (mstore (w2n bp+32*(1+LENGTH vs)) w s).vs_memory ==>
  stmt_state_rel H ctx func cenv cx ff
    (mstore (w2n bp) (n2w (LENGTH vs+1))
      (mstore (w2n bp+32*(1+LENGTH vs)) w s))
Proof
  strip_tac >>
  `all_have_type tv vs /\ value_has_type tv v` by
    fs[vyperTypingTheory.value_has_type_def,
       vyperTypingTheory.all_have_type_EVERY, EVERY_APPEND] >>
  `elems_val_wf vs tv /\ val_wf tv v` by
    metis_tac[value_has_type_val_wf] >>
  drule_all append_memory_word_representation >> strip_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx func cenv cx ff out` >>
  `out = s with vs_memory := out.vs_memory` by
    simp_tac (srw_ss()) [Abbr `out`, mstore_def, LET_THM] >>
  pop_assum SUBST1_TAC >>
  irule place_store_pointer_memory_state >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[] >>
  conj_tac
  >- simp[Abbr `out`, venomMemPropsTheory.LENGTH_mstore_eq] >>
  rpt strip_tac >>
  `mem_bytes_at q 1 out.vs_memory =
   mem_bytes_at q 1 (mstore (w2n bp+32*(1+LENGTH vs)) w s).vs_memory` by
    (qunabbrev_tac `out` >> irule mstore_mem_bytes_at_disjoint >>
     gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  pure_asm_rewrite_tac [] >> sym_tac >>
  irule mstore_mem_bytes_at_disjoint >>
  gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED


Theorem append_memory_array_layout_general:
  stmt_state_rel H ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) ==>
  ?tv. evaluate_type (get_tenv cx) elem = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n bp) s.vs_memory /\
    w2n bp + 32 + cap * type_memory_size tv <= s.vs_alloca_next /\
    0 < cap /\ cap < dimword (:256)
Proof
  rpt strip_tac >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >> gvs[] >>
  `tv0 = entry.type` by
    metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME atv` >>
  `?tv. evaluate_type (get_tenv cx) elem = SOME tv /\
        atv = ArrayTV tv (Dynamic cap)` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `0 < cap` by
    gvs[vyperValueTheory.evaluate_type_def,
        AllCaseEqs()] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[aug_place_lookup_typed]) >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[] >>
     irule memory_value_rel_val_in_memory >> simp[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >>
     gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))` by
    metis_tac[evaluate_subscripts_type] >>
  `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
     (w2n b + k) s.vs_memory` by metis_tac[aug_place_path_project] >>
  `cap < dimword (:256)` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed,
              vyperTypingTheory.well_formed_type_value_def] >>
  simp[] >>
  gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

(* The full-word interface is the stride-32 instance of the general layout. *)
Theorem append_memory_array_layout:
  stmt_state_rel H ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  supported_full_word_type elem ==>
  ?tv. evaluate_type (get_tenv cx) elem = SOME tv /\
    type_memory_size tv = 32 /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n bp) s.vs_memory /\
    w2n bp + 32*(1+cap) <= s.vs_alloca_next /\ cap < dimword (:256)
Proof
  strip_tac >> drule_all append_memory_array_layout_general >> strip_tac >>
  `type_memory_size tv = 32` by
    (qpat_x_assum `supported_full_word_type elem` mp_tac >>
     rw[supported_full_word_type_def] >>
     fs[vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def]) >>
  qexists_tac `tv` >> gvs[] >> decide_tac
QED

(* The declaration witness ties the root's allocation bound to its evaluated
   layout.  Positive evaluated capacity makes every element fit in that root. *)
Theorem append_memory_element_size_bound:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME root_ty /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  evaluate_type (get_tenv cx) elem = SOME tv ==>
  type_memory_bytes cenv elem = type_memory_size tv /\
  type_memory_bytes cenv elem < 2 ** 64
Proof
  strip_tac >>
  `cenv.ce_var_type id = SOME root_ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >> gvs[] >>
  `type_memory_bytes cenv elem = type_memory_size tv /\
   type_memory_bytes cenv root_ty = type_memory_size tv0` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv root_ty < 2 ** 64` by
    metis_tac[locals_alloc_ok_def] >>
  `tv' = ArrayTV tv (Dynamic cap) /\ 0 < cap` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  drule mem_path_offset_sound >> strip_tac >>
  `type_memory_size tv <= type_memory_size tv0` by
    (irule LESS_EQ_TRANS >> qexists_tac `cap * type_memory_size tv` >>
     conj_tac
     >- (Cases_on `cap` >> gvs[] >> simp[arithmeticTheory.MULT_CLAUSES]) >>
     qpat_x_assum `k + type_memory_size _ <= _` mp_tac >>
     simp[valueEncodingTheory.type_memory_size_def]) >>
  metis_tac[LESS_EQ_LESS_TRANS]
QED
