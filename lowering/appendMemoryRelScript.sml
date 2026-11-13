(* The two word stores extend a dynamic array's initialized memory prefix. *)
Theory appendMemoryRel
Ancestors
  abiDecoderArrayPrefix valueEncodingProps valueEncodingProofs valueEncodingDefs
  placeStore valueEncodingTyping venomState words list arithmetic

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
