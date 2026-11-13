(* Internal calls are the only incompatible declaration RHS layouts. *)
Theory widenedDeclarationPtrPreparation
Ancestors widenedAssignPtrPreparation exprOpenCopies typedMemoryCopy
  exprSimHyps exprSimHypsDefs bodySim supportedTypes compileEnv vyperAST
  vyperTypeSystem exprSimIfExpCompat

Theorem widened_declaration_rhs_classify_ptr:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  supported_expr tops e /\ supported_copy_types typ (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) typ /\ ~is_word_type typ /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?fid args drv. e = Call typ (IntCall fid) args drv /\
    ~is_bytestring_type typ /\ arg_type_fits (lowered_value_type ce e) typ
Proof
  strip_tac >>
  drule_all widened_assignment_internal_call >> strip_tac >> gvs[] >>
  rename1 `Call ty (IntCall fid) args drv` >>
  `arg_type_fits (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty` by
    metis_tac[exprSimHypsTheory.ifexp_body_pre_intcall_physical] >>
  `~is_bytestring_type ty` by
    (fs[vyperASTTheory.expr_type_def] >>
     metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
  `typ = ty` by
    (fs[vyperASTTheory.expr_type_def] >>
     metis_tac[exprOpenCopiesTheory.supported_copy_types_store_path,
               typedMemoryCopyTheory.typed_copy_bytestring_source]) >>
  gvs[]
QED

