(* Static classification for declarations with a widened physical RHS. *)
Theory annAssignWidenedPtrFacts
Ancestors
  annAssignPtrFacts exprSimIfExpCompat exprSimHyps exprSimHypsDefs
  bodyExprPreFacts bodySim exprSimSource vyperTypeInvariants
  supportedTypes exprOpenCopies typedMemoryCopy compileEnv vyperAST

Theorem widened_declaration_rhs_classify:
  expr_body_pre ce cx env e es /\
  supported_copy_types typ (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) typ /\ ~is_word_type typ /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?fid args drv. e = Call typ (IntCall fid) args drv /\
    ~is_bytestring_type typ /\ arg_type_fits (lowered_value_type ce e) typ
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
      env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `ce` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  `arg_type_fits (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty` by
    metis_tac[ifexp_body_pre_intcall_physical] >>
  `~is_bytestring_type ty` by
    (fs[expr_type_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
  `typ = ty` by
    (fs[expr_type_def] >>
     metis_tac[supported_copy_types_store_path, typed_copy_bytestring_source]) >>
  gvs[]
QED
