Theory extRetWideningTransPtr
Ancestors
  vyperTypeSystem vyperAST arithmetic
  extRetSemanticEntryPtr exprSimHyps typedCopyPtr exprLowering loweringPosts

(* The S1 suffix has private copies of this argument.  Export the mutual
   boundary here without importing a whole external-return simulation. *)
Theorem ext_ret_arg_fits_trans_mutual:
  (!a b. !c. arg_type_fits a b /\ arg_type_fits b c ==> arg_type_fits a c) /\
  (!as_ bs. !cs. arg_types_fit as_ bs /\ arg_types_fit bs cs ==>
    arg_types_fit as_ cs)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def]
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT bt)` >> Cases_on `bt` >> gvs[arg_type_fits_def])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT bt)` >> Cases_on `bt` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[arg_type_fits_def])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (ArrayT ct bd)` >> Cases_on `bd` >> gvs[arg_type_fits_def] >>
      metis_tac[LESS_EQ_TRANS])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (ArrayT ct bd)` >> Cases_on `bd` >> gvs[arg_type_fits_def] >>
      metis_tac[])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >> metis_tac[])
  >> Cases_on `cs` >> gvs[arg_type_fits_def] >> metis_tac[]
QED

Theorem ext_ret_type_widens_trans:
  !tenv a b c.
    type_widens_to tenv a b /\ type_widens_to tenv b c ==>
    type_widens_to tenv a c
Proof
  simp[type_widens_to_def] >> metis_tac[ext_ret_arg_fits_trans_mutual]
QED

Theorem ext_ret_aggregate_return_widens:
  !ce cx env es e ret.
    expr_sim_inv ce cx env es /\
    IS_SOME (type_stmt env ret (Return (SOME e))) /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
    type_widens_to env.type_defs (lowered_value_type ce e) ret
Proof
  rpt strip_tac >>
  gvs[type_stmt_return_some_iff] >>
  drule_all post_value_type_widens >> strip_tac >>
  drule_all ext_ret_aggregate_lowered_post_type >> strip_tac >>
  irule ext_ret_type_widens_trans >>
  qexists_tac `expr_type e` >> simp[]
QED
