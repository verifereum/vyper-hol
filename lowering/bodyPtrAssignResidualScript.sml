(*
 * The residual forms of the assignment body cases (bodyPtrAssignCases):
 * the pointer twins of the forms S1's own proof still admits (subscript
 * and nested targets, aggregate fields, storage dynamic arrays, internal
 * calls whose return type widens).  Each is stated as S1's lemma of the
 * same name with stmt_frag_ptr, frame_ret_ok_ptr and the body_*_ptr_ok
 * predicates in place of S1's, and is admitted until S1 proves its twin.
 *
 * TOP-LEVEL:
 *   body_assign_other_ptr, body_assign_widened_aggregate_call_ptr,
 *   body_assign_tuple_other_ptr, body_assign_tuple_widened_call_ptr,
 *   body_augassign_other_ptr, body_annassign_widened_aggregate_call_ptr
 *)
Theory bodyPtrAssignResidual
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps supportedStmts supportedDecls
  stmtLowering exprLowering compileEnv vyperAST vyperInterpreter vyperState
  vyperTypeSystem list finite_map

val _ = Parse.hide "body";

(* RESIDUAL: the pointer twin of S1's bodySimStmtCases$body_assign_other, stated as S1
   states it with only the pointer substitutions (stmt_frag_ptr,
   frame_ret_ok_ptr, body_*_ptr_ok). Admitted until S1 proves its twin. *)
Theorem body_assign_other_ptr:
  !d PG cx t e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ptr_ok cx t) /\
    body_expr_ptr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED

(* RESIDUAL: the pointer twin of S1's bodySimStmtCases$body_assign_widened_aggregate_call, stated as S1
   states it with only the pointer substitutions (stmt_frag_ptr,
   frame_ret_ok_ptr, body_*_ptr_ok). Admitted until S1 proves its twin. *)
Theorem body_assign_widened_aggregate_call_ptr:
  !d PG cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* RESIDUAL: the pointer twin of S1's bodySimStmtCases$body_assign_tuple_other, stated as S1
   states it with only the pointer substitutions (stmt_frag_ptr,
   frame_ret_ok_ptr, body_*_ptr_ok). Admitted until S1 proves its twin. *)
Theorem body_assign_tuple_other_ptr:
  !d PG cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ptr_ok cx (TupleTarget gs) v) /\ body_expr_ptr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) /\
    ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                         FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes cenv ty) \/
                (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        supported_scalar_target tops nsid) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* RESIDUAL: the pointer twin of S1's bodySimStmtCases$body_assign_tuple_widened_call, stated as S1
   states it with only the pointer substitutions (stmt_frag_ptr,
   frame_ret_ok_ptr, body_*_ptr_ok). Admitted until S1 proves its twin. *)
Theorem body_assign_tuple_widened_call_ptr:
  !d PG cx gs e tops ctx func cenv env env' ret_ty lctx RetQ es res es'.
    body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    lowered_value_type cenv e <> expr_type e ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* RESIDUAL: the pointer twin of S1's bodySimStmtCases$body_augassign_other, stated as S1
   states it with only the pointer substitutions (stmt_frag_ptr,
   frame_ret_ok_ptr, body_*_ptr_ok). Admitted until S1 proves its twin. *)
Theorem body_augassign_other_ptr:
  !d PG cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ptr_ok cx e) /\ body_base_target_ptr_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  cheat
QED

(* RESIDUAL: the pointer twin of S1's bodySimDeclCases$body_annassign_widened_aggregate_call, stated as S1
   states it with only the pointer substitutions (stmt_frag_ptr,
   frame_ret_ok_ptr, body_*_ptr_ok). Admitted until S1 proves its twin. *)
Theorem body_annassign_widened_aggregate_call_ptr:
  !d PG cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ptr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* RESIDUAL: the pointer twin of S1's bodySimDeclCases$body_annassign_widened_aggregate:
   annAssignPtrDispatch$body_annassign_memory_ptr's hypotheses with its two
   layout disjuncts replaced by the widened non-call copy's form premises.
   Admitted until S1 proves its twin. *)
Theorem body_annassign_widened_aggregate_ptr:
 !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es d PG.
    body_stmt_safe tops (AnnAssign id typ e) /\
 (!tenv s'' tyv t. tenv = get_tenv cx /\
   lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
     (INL tyv,t) ==> body_expr_ptr_ok cx e) /\
 body_inv tops ctx cenv cx /\
 supported_stmt tops bindings (AnnAssign id typ e) /\
 (!target. supported_stmt_expr_exists
   (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
   occurs_abi_decode_target target tops) /\
 expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
 type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
 stmt_exprs_ok cenv (AnnAssign id typ e) /\
 call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
 ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
 lowered_value_type cenv e = expr_type e /\ expr_type e <> typ /\
 ~is_bytestring_type typ /\ ~(has_length_word typ /\ is_empty_value_expr e) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
   (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED
