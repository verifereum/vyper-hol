(* Type and layout facts carried by immediate positional snapshot cells. *)
Theory exprExtRequestSnapshotLayout
Ancestors
  exprExtRequestSnapshotStoreInterface exprExtRequestTypedCells
  exprExtRequestAbiFits exprSimHyps exprSimHypsDefs
  exprExtRequestStagesSource exprExtRequestShape
  vyperTypeArgFits vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem vyperTyping vyperValue valueEncoding valueEncodingProps
  compileEnv vyperMisc list rich_list pair words arithmetic

Theorem extrequest_snapshot_cell_types[local]:
  extrequest_snapshot_cell ctx func ce cx eb cb tb (vv,ty,tv,v) ==>
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv
Proof
  simp[extrequest_snapshot_cell_def]
QED

Theorem extrequest_snapshot_cells_layout[local]:
  !cells. EVERY (extrequest_snapshot_cell ctx func ce cx eb cb tb) cells ==>
  OPT_MMAP (evaluate_type (get_tenv cx))
    (MAP (\(vv,ty,tv,v). ty) cells) =
    SOME (MAP (\(vv,ty,tv,v). tv) cells) /\
  values_have_types (MAP (\(vv,ty,tv,v). tv) cells)
    (MAP (\(vv,ty,tv,v). v) cells) /\
  SUM (MAP (type_memory_bytes ce) (MAP (\(vv,ty,tv,v). ty) cells)) =
    type_memory_size_list (MAP (\(vv,ty,tv,v). tv) cells) /\
  SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) =
    type_memory_size_list (MAP (\(vv,ty,tv,v). tv) cells)
Proof
  Induct >> simp[OPT_MMAP_def, value_has_type_def, type_memory_size_def] >>
  qx_gen_tac `cell` >> PairCases_on `cell` >> strip_tac >>
  drule extrequest_snapshot_cell_types >> strip_tac >>
  simp[OPT_MMAP_def, value_has_type_def, type_memory_size_def]
QED

Theorem extrequest_snapshot_cells_tuple[local]:
  EVERY (extrequest_snapshot_cell ctx func ce cx eb cb tb) cells /\
  SUM (MAP (type_memory_bytes ce) (MAP (\(vv,ty,tv,v). ty) cells)) < 2**64 ==>
  evaluate_type (get_tenv cx) (TupleT (MAP (\(vv,ty,tv,v). ty) cells)) =
    SOME (TupleTV (MAP (\(vv,ty,tv,v). tv) cells)) /\
  value_has_type (TupleTV (MAP (\(vv,ty,tv,v). tv) cells))
    (ArrayV (TupleV (MAP (\(vv,ty,tv,v). v) cells))) /\
  type_memory_bytes ce (TupleT (MAP (\(vv,ty,tv,v). ty) cells)) =
    type_memory_size (TupleTV (MAP (\(vv,ty,tv,v). tv) cells)) /\
  type_memory_size (TupleTV (MAP (\(vv,ty,tv,v). tv) cells)) =
    SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells)
Proof
  strip_tac >> drule extrequest_snapshot_cells_layout >> strip_tac >>
  `type_slot_size_list (MAP (\(vv,ty,tv,v). tv) cells) <= dimword (:256)` by
    (fs[type_memory_size_slots, dimword_def] >> decide_tac) >>
  simp[Once evaluate_type_def, evaluate_types_OPT_MMAP, type_slot_size_def,
       value_has_type_def, type_memory_bytes_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem extrequest_snapshot_value_runtime_typed[local]:
  expr_body_pre ce cx env e es /\ env.type_defs = get_tenv cx /\
  extrequest_snapshot_cell ctx func ce cx eb cb tb
    (vv,lowered_value_type ce e,tv,v) ==>
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type ce e) v
Proof
  strip_tac >> drule extrequest_snapshot_cell_types >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME stv` >>
  `value_has_type stv v` by
    (irule (cj 1 arg_type_fits_value_has_type) >> metis_tac[]) >>
  simp[value_runtime_typed_def] >> metis_tac[]
QED

Theorem extrequest_snapshot_cells_runtime_typed[local]:
  !xs cells.
  EVERY (\e. expr_body_pre ce cx env e es) xs /\
  env.type_defs = get_tenv cx /\
  EVERY (extrequest_snapshot_cell ctx func ce cx eb cb tb) cells /\
  MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type ce) xs ==>
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type ce e) v)
    xs (MAP (\(vv,ty,tv,v). v) cells)
Proof
  Induct
  >- (Cases_on `cells` >> simp[]) >>
  qx_gen_tac `arg` >> Cases_on `cells` >> simp[] >>
  rename1 `extrequest_snapshot_cell ctx func ce cx eb cb tb cell` >>
  PairCases_on `cell` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule_all extrequest_snapshot_value_runtime_typed >> simp[]
QED

Theorem extrequest_snapshot_arguments_assignable[local]:
  EVERY (\e. expr_body_pre ce cx env e es) xs /\
  arg_types_fit (MAP expr_type xs) ats /\
  EVERY (assignable_type (get_tenv cx)) ats ==>
  EVERY (assignable_type (get_tenv cx)) (MAP (lowered_value_type ce) xs)
Proof
  strip_tac >>
  `EVERY (well_formed_type (get_tenv cx)) (MAP expr_type xs)` by
    (simp[EVERY_MAP, EVERY_MEM, well_formed_type_def] >>
     rpt strip_tac >> irule expr_body_pre_type_evaluates >>
     qexistsl_tac [`ce`,`env`,`es`] >> fs[EVERY_MEM]) >>
  `EVERY (well_formed_type (get_tenv cx)) (MAP (lowered_value_type ce) xs)` by
    (simp[EVERY_MAP, EVERY_MEM, well_formed_type_def,
          optionTheory.IS_SOME_EXISTS] >>
     rpt strip_tac >> irule expr_body_pre_lowered_evaluates >>
     qexistsl_tac [`env`,`es`] >> fs[EVERY_MEM]) >>
  `arg_types_fit (MAP (lowered_value_type ce) xs) (MAP expr_type xs)` by
    (simp[arg_types_fit_LIST_REL, LIST_REL_EL_EQN] >>
     rpt strip_tac >> simp[EL_MAP] >>
     irule expr_body_pre_lowered_fits >>
     qexistsl_tac [`cx`,`env`,`es`] >>
     fs[EVERY_EL]) >>
  `EVERY (assignable_type (get_tenv cx)) (MAP expr_type xs)` by
    metis_tac[cj 2 extrequest_fits_assignable] >>
  metis_tac[cj 2 extrequest_fits_assignable]
QED

Theorem extrequest_snapshot_call_typed_cells:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) es /\
  EVERY (extrequest_snapshot_cell ctx func ce cx eb cb tb) cells /\
  MAP (\(vv,ty,tv,v). ty) cells =
    MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest) /\
  MAP (\(vv,ty,tv,v). v) cells = vs ==>
  ?tvs.
  MAP (\(vv,ty,tv,v). tv) cells = tvs /\
  evaluate_type (get_tenv cx)
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))) =
      SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  type_memory_bytes ce
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))) =
      type_memory_size (TupleTV tvs) /\
  SUM (MAP (type_memory_bytes ce)
    (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))) =
      type_memory_size_list tvs /\
  type_memory_size (TupleTV tvs) =
    SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) /\
  (TAKE (LENGTH ats) rest <> [] ==>
    assignable_type (get_tenv cx)
      (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))))
Proof
  strip_tac >>
  `SUM (MAP (type_memory_bytes ce)
    (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))) < 2**64` by
    (drule extrequest_call_cells_bound >> simp[]) >>
  drule extrequest_snapshot_cells_layout >> strip_tac >>
  drule extrequest_snapshot_cells_tuple >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `EVERY (\e. expr_body_pre ce cx env e es) (TAKE (LENGTH ats) rest)` by
    (drule extrequest_operand_body_pre >> simp[EVERY_MEM] >>
     metis_tac[MEM_TAKE, MEM]) >>
  `arg_types_fit (MAP expr_type (TAKE (LENGTH ats) rest)) ats /\
   EVERY (assignable_type (get_tenv cx)) ats` by
    (drule extrequest_body_typed >> simp[Once well_typed_expr_def] >>
     strip_tac >> fs[]) >>
  drule_all extrequest_snapshot_arguments_assignable >> strip_tac >>
  qexists_tac `MAP (\(vv,ty,tv,v). tv) cells` >>
  gvs[assignable_type_def, well_formed_type_def, type_memory_size_def, SF ETA_ss]
QED

Theorem extrequest_snapshot_call_positional_calldata:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) es /\
  EVERY (extrequest_snapshot_cell ctx func ce cx eb cb tb) cells /\
  MAP (\(vv,ty,tv,v). ty) cells =
    MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest) /\
  MAP (\(vv,ty,tv,v). v) cells = vs ==>
  ?av.
  vyper_to_abi (get_tenv cx)
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))
    (ArrayV (TupleV vs)) = SOME av /\
  LENGTH (enc (vyper_to_abi_type (get_tenv cx)
    (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) av) <=
    abi_size_bound ce.ce_struct_fields
      (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest))) /\
  build_ext_calldata (get_tenv cx) fname ats vs =
    SOME (function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++
      enc (vyper_to_abi_type (get_tenv cx)
        (TupleT (MAP (lowered_value_type ce) (TAKE (LENGTH ats) rest)))) av)
Proof
  strip_tac >> drule_all extrequest_snapshot_call_typed_cells >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `EVERY (\e. expr_body_pre ce cx env e es) (TAKE (LENGTH ats) rest)` by
    (drule extrequest_operand_body_pre >> simp[EVERY_MEM] >>
     metis_tac[MEM_TAKE, MEM]) >>
  `LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
      value_runtime_typed env (lowered_value_type ce e) v)
      (TAKE (LENGTH ats) rest) vs` by
    metis_tac[extrequest_snapshot_cells_runtime_typed] >>
  `EVERY (well_typed_expr env) (TAKE (LENGTH ats) rest)` by
    (fs[EVERY_MEM, expr_body_pre_def] >> metis_tac[]) >>
  `EVERY (\e. ~expr_has_effect e) (TAKE (LENGTH ats) rest)` by
    (drule extrequest_body_typed >> simp[] >> metis_tac[EVERY_TAKE]) >>
  `arg_types_fit (MAP expr_type (TAKE (LENGTH ats) rest)) ats /\
   EVERY (assignable_type (get_tenv cx)) ats` by
    (drule extrequest_body_typed >> simp[Once well_typed_expr_def] >>
     strip_tac >> fs[]) >>
  irule extrequest_positional_calldata >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexists_tac `TupleTV tvs` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`env`,`es`] >> asm_rewrite_tac[]
QED
