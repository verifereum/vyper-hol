(* Padded child reads through a tuple expression's parent region. *)
Theory tupleChildReadPtr
Ancestors typedCopyPtr typedCopyLayoutPtr

Theorem expr_val_at_tuple_child_store_read_covers:
  !ctx func cenv cx t sa sb es vs p s tvs w G tn i G' tn' q s'.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es (ArrayV (TupleV vs)) (Var p) s /\
    ptr_val_ok cx t (ArrayV (TupleV vs)) (Var p) G tn s /\
    evaluate_type (get_tenv cx) t = SOME (TupleTV tvs) /\ ~is_word_type t /\
    values_have_types tvs vs /\ i < LENGTH tvs /\
    lookup_var p s = SOME w /\
    lookup_var q s' = SOME (w + n2w (SUM (MAP type_memory_size (TAKE i tvs)))) /\
    FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} /\
    0 < val_store_size (EL i tvs) (EL i vs) ==>
    ptr_covers G' tn' q s' (val_store_size (EL i tvs) (EL i vs))
Proof
  rpt strip_tac >> irule expr_val_at_ptr_offset_read_covers >> simp[] >>
  goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  qexistsl [`G`, `ctx`, `func`,
    `SUM (MAP type_memory_size (TAKE i tvs))`, `tn`] >>
  simp[exprSimTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def,
    valueEncodingProofsTheory.type_memory_size_list_sum] >>
  irule tuple_child_store_size_contained >> simp[]
QED

(* The nested String[1] source is padded by its tuple slot, including after
   an offset pointer has been emitted into an otherwise arbitrary state. *)
Theorem tuple_string_padded_child_read_probe[local]:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (TupleT [BaseT (StringT 1)]) sa sb es
    (ArrayV (TupleV [StringV "a"])) (Var p) s /\
  ptr_val_ok cx (TupleT [BaseT (StringT 1)])
    (ArrayV (TupleV [StringV "a"])) (Var p) G tn s /\
  evaluate_type (get_tenv cx) (TupleT [BaseT (StringT 1)]) =
    SOME (TupleTV [BaseTV (StringT 1)]) /\
  lookup_var p s = SOME w /\ lookup_var q s' = SOME w /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' 64
Proof
  rpt strip_tac >>
  `ptr_covers G' tn' q s'
     (val_store_size (EL 0 [BaseTV (StringT 1)]) (EL 0 [StringV "a"]))`
    suffices_by
      simp[exprSimTheory.val_store_size_def, vfmConstantsTheory.word_size_def] >>
  irule expr_val_at_tuple_child_store_read_covers >>
  simp[exprSimTheory.val_store_size_def, vyperTypingTheory.value_has_type_def,
    vfmConstantsTheory.word_size_def] >>
  goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >> simp[] >>
  qexistsl [`G`, `ctx`, `func`, `tn`] >>
  simp[exprSimTheory.val_store_size_def, compileEnvTheory.is_word_type_def,
    vyperTypingTheory.value_has_type_def, vfmConstantsTheory.word_size_def,
    wordsTheory.WORD_ADD_0]
QED
