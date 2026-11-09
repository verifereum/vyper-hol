(* Physical/post-type alignment at an arbitrary return destination. *)
Theory bodyIntCallFamStmtReturnTypes
Ancestors
  exprSimIfExpCompat loweringPosts exprLowering compileEnv context
  vyperTypeSystem typedMemoryCopy valueCopyBytes

Theorem compound_lowered_post_type:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
  lowered_value_type ce e = post_value_type ce e
Proof
  strip_tac >> drule_all ifexp_lowered_type_classify >> strip_tac
  >- metis_tac[post_value_type_lowered] >>
  gvs[post_value_type_def, vyperASTTheory.expr_type_def]
QED

Theorem type_widens_from_word:
  type_widens_to tenv sty dty /\ is_word_type sty ==> sty = dty
Proof
  Cases_on `sty` >> Cases_on `dty` >>
  simp[type_widens_to_def, arg_type_fits_def, is_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `arg_type_fits (BaseT bt) (BaseT bu)` >>
  Cases_on `bt` >> Cases_on `bu` >>
  gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT bd)) (BaseT (BytesT bu))` >>
  Cases_on `bd` >> Cases_on `bu` >>
  gvs[arg_type_fits_def, is_word_type_def]
QED

Theorem return_store_post_type:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  type_widens_to env.type_defs (expr_type e) dty ==>
  compile_store_memory ce src dst dty (lowered_value_type ce e) =
  compile_store_memory ce src dst dty (post_value_type ce e)
Proof
  strip_tac >> Cases_on `is_word_type dty`
  >- simp[compile_store_memory_def] >>
  Cases_on `is_bytestring_type dty`
  >- simp[compile_store_memory_def] >>
  `~is_word_type (expr_type e)` by metis_tac[type_widens_from_word] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  drule_all compound_lowered_post_type >> simp[]
QED
