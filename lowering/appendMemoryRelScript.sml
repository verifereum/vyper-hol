(* The two word stores extend a dynamic array's initialized memory prefix. *)
Theory appendMemoryRel
Ancestors
  abiDecoderArrayPrefix valueEncodingProps valueEncodingProofs valueEncodingDefs
  placeStore valueEncodingTyping venomState words list arithmetic
  bodySimAugPlaceLoad supportedTypes memoryValueEncoding loweringStateRelDefs
  exprLoweringProps exprSimHypsDefs exprSimProps loweringPosts
  vyperTypeInvariants vyperPlaceStatePreservation

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
  strip_tac >>
  qabbrev_tac `data = mstore (off + 32 * (1 + LENGTH vs)) w s` >>
  `elems_in_memory vs (off + 32) tv data.vs_memory` by
    (`data = mstore (off + 32 * (1 + LENGTH vs)) w
       (s with vs_memory := s.vs_memory)` by simp[Abbr `data`] >>
     pop_assum SUBST1_TAC >>
     irule (cj 3 mstore_preserves_val_in_memory) >>
     gvs[val_in_memory_def] >> decide_tac) >>
  `elems_in_memory vs (off + 32) tv
    (mstore off (n2w (LENGTH vs + 1)) data).vs_memory` by
    (`mstore off (n2w (LENGTH vs + 1)) data =
      mstore off (n2w (LENGTH vs + 1))
        (data with vs_memory := data.vs_memory)` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule (cj 3 mstore_preserves_val_in_memory) >> simp[]) >>
  `val_in_memory tv v (off + 32 * (1 + LENGTH vs))
    (mstore off (n2w (LENGTH vs + 1)) data).vs_memory` by
    (`mstore off (n2w (LENGTH vs + 1)) data =
      mstore off (n2w (LENGTH vs + 1))
        (data with vs_memory := data.vs_memory)` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule (cj 1 mstore_preserves_val_in_memory) >>
     simp[] >> decide_tac) >>
  `off + 32 + LENGTH vs * type_memory_size tv =
     off + 32 * (1 + LENGTH vs)` by (simp[] >> decide_tac) >>
  qunabbrev_tac `data` >>
  simp_tac std_ss [Once val_in_memory_def, LENGTH_APPEND, LENGTH] >>
  conj_tac >- simp[mstore_mem_word_at_same] >>
  asm_simp_tac std_ss [elems_in_memory_append, val_in_memory_def,
                      vyperValueTheory.type_value_case_def]
QED

Theorem append_memory_word_state:
  stmt_state_rel ctx func cenv cx es s /\
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
  stmt_state_rel ctx func cenv cx ff
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
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx ff out` >>
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


Theorem append_memory_array_layout:
  stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
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
  rpt strip_tac >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >> gvs[] >>
  `tv0 = entry.type` by
    metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME atv` >>
  `?tv. evaluate_type (get_tenv cx) elem = SOME tv /\
        atv = ArrayTV tv (Dynamic cap)` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `type_memory_size tv = 32` by
    (qpat_x_assum `supported_full_word_type elem` mp_tac >>
     rw[supported_full_word_type_def] >>
     fs[vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def]) >>
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
  simp[] >>
  gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED
