(* Physical source layout at a genuinely widened place assignment. *)
Theory placeAssignSourceClassification
Ancestors
  exprSimIfExpCompat exprSimHyps exprSimHypsDefs externalNormalizePremises
  placeMemoryTypeInterfaces vyperTypeArgFits valueEncodingProps
  vyperTypeSystem vyperTypeInvariants loweringPosts

Theorem assign_fits_trans_joint[local]:
  (!s d. arg_type_fits s d ==> !u. arg_type_fits d u ==> arg_type_fits s u) /\
  (!ss ds. arg_types_fit ss ds ==> !us. arg_types_fit ds us ==> arg_types_fit ss us)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def]
  >~ [`arg_types_fit (s::ss) us`]
  >- (Cases_on `us` >> gvs[arg_type_fits_def]) >>
  Cases_on `u` >> gvs[arg_type_fits_def] >>
  Cases_on `b` >> gvs[arg_type_fits_def] >>
  rpt CASE_TAC >> gvs[arg_type_fits_def] >>
  Cases_on `b'` >> gvs[arg_type_fits_def]
QED

Theorem assign_fits_antisym_joint[local]:
  (!s d. arg_type_fits s d ==> arg_type_fits d s ==> s = d) /\
  (!ss ds. arg_types_fit ss ds ==> arg_types_fit ds ss ==> ss = ds)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def] >> gvs[]
QED

Theorem assign_relayout_source_classify:
  expr_sim_inv ce cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  type_place_target env t = SOME (Type dty) /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  post_value_type ce e = lowered_value_type ce e /\
  post_value_type ce e <> expr_type e /\
  type_widens_to (get_tenv cx) (post_value_type ce e) dty /\
  ~is_word_type (post_value_type ce e) /\ ~is_word_type dty /\
  ~is_bytestring_type (post_value_type ce e) /\ ~is_bytestring_type dty /\
  post_value_type ce e <> dty
Proof
  strip_tac >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) dty` by
    gvs[type_stmt_def, atarget_accepts_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates]) >>
  drule_all ifexp_lowered_type_classify >> strip_tac >> gvs[] >>
  `arg_type_fits (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty` by
    (PairCases_on `fid` >>
     gvs[expr_sim_inv_def, well_typed_expr_def, exprLoweringTheory.lowered_value_type_def,
         vyperASTTheory.expr_type_def, type_widens_to_def] >>
     metis_tac[]) >>
  `well_formed_type (get_tenv cx) ty` by
    metis_tac[exprSafeOperandTheory.well_typed_expr_type_well_formed,
              vyperASTTheory.expr_type_def] >>
  `type_widens_to (get_tenv cx)
     (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty` by
    fs[type_widens_to_def] >>
  gvs[vyperASTTheory.expr_type_def] >>
  `~is_word_type ty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `~is_bytestring_type ty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  qmatch_asmsub_abbrev_tac `arg_type_fits sty ty` >>
  `type_widens_to (get_tenv cx) sty dty` by
    (fs[type_widens_to_def] >> metis_tac[cj 1 assign_fits_trans_joint]) >>
  `sty <> dty` by
    (strip_tac >> fs[type_widens_to_def] >>
     metis_tac[cj 1 assign_fits_antisym_joint]) >>
  `~is_word_type dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  simp[] >> metis_tac[normalize_return_source_kinds]
QED

Theorem assign_relayout_capacity:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv ==>
  0 < type_memory_size stv /\ 0 < type_memory_bytes ce sty /\
  32 <= type_memory_size dtv /\ 32 <= type_memory_bytes ce dty /\
  (type_memory_bytes ce dty <= 32 ==> type_memory_bytes ce dty = 32)
Proof
  strip_tac >>
  `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
  `0 < type_memory_size dtv` by
    metis_tac[normalize_return_destination_positive] >>
  gvs[type_memory_size_slots]
QED
