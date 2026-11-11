(* Assignment caller facts keep physical, expression and destination types distinct. *)
Theory assignRelayoutCaller
Ancestors
  annassignRelayoutSource typedMemoryCopy compileEnv exprSimHypsDefs
  vyperTypeSystem vyperTypeInvariants supportedTypes vyperAST

Theorem arg_type_fits_trans:
  (!a b. arg_type_fits a b ==> !c. arg_type_fits b c ==> arg_type_fits a c) /\
  (!as_ bs. arg_types_fit as_ bs ==> !cs. arg_types_fit bs cs ==> arg_types_fit as_ cs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[arg_type_fits_def] >> rpt strip_tac >>
  all_tac
  >~ [`arg_types_fit (a::as_) cs`]
  >- (Cases_on `cs` >> gvs[arg_type_fits_def] >> metis_tac[]) >>
  Cases_on `c` >> gvs[arg_type_fits_def] >>
  all_tac
  >~ [`arg_type_fits (BaseT (StringT n)) (BaseT bt)`]
  >- (Cases_on `bt` >> gvs[arg_type_fits_def] >> decide_tac)
  >~ [`arg_type_fits (BaseT (BytesT (Dynamic n))) (BaseT bt)`]
  >- (Cases_on `bt` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[arg_type_fits_def] >> decide_tac) >>
  rename1 `ArrayT t bd` >> Cases_on `bd` >> gvs[arg_type_fits_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem arg_type_fits_antisym:
  (!a b. arg_type_fits a b ==> arg_type_fits b a ==> a = b) /\
  (!as_ bs. arg_types_fit as_ bs ==> arg_types_fit bs as_ ==> as_ = bs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[arg_type_fits_def] >> rpt strip_tac >> gvs[]
QED

Theorem type_widens_to_trans:
  type_widens_to tenv a b /\ type_widens_to tenv b c ==>
  type_widens_to tenv a c
Proof
  simp[type_widens_to_def] >> metis_tac[cj 1 arg_type_fits_trans]
QED

Theorem type_widens_to_antisym:
  type_widens_to tenv a b /\ type_widens_to tenv b a ==> a = b
Proof
  simp[type_widens_to_def] >> metis_tac[cj 1 arg_type_fits_antisym]
QED

Theorem assign_relayout_source_classify:
  !cenv cx env e es dty.
    expr_body_pre cenv cx env e es /\
    type_widens_to env.type_defs (expr_type e) dty /\ ~is_word_type dty /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    ~is_bytestring_type dty /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    post_value_type cenv e = lowered_value_type cenv e /\
    lowered_value_type cenv e <> expr_type e /\
    lowered_value_type cenv e <> dty /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    ?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  `supported_copy_types (expr_type e) (expr_type e)` by simp[supported_copy_types_def] >>
  drule_all annassign_relayout_source_classify >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    metis_tac[type_widens_to_trans] >>
  `lowered_value_type cenv e <> dty` by metis_tac[type_widens_to_antisym] >>
  `~is_bytestring_type dty` by
    (fs[type_widens_to_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
  simp[]
QED
