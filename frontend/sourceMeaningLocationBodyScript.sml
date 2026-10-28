Theory sourceMeaningLocationBody
Ancestors
  sourceMeaningLocationSource sourceMeaningLocationCode sourceMeaningLocationDefs
  sourceMeaningDefs sourceModuleStmt sourceModuleDefs sourceTypeDefs sourceSyntax sourceResolve
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext vyperAST list alist

(* Source-declaration provenance for global identity/type/location metadata.
   Constants may occur in this table, but the reference rule additionally
   requires SR_Dynamic, so they can never be mistaken for runtime reads. *)
Definition source_location_global_metadata_def:
  source_location_global_metadata ctx [] = SOME [] /\
  source_location_global_metadata ctx (d::ds) =
    case source_location_global_metadata ctx ds of NONE => NONE | SOME rest =>
      case d of SD_Variable name annotation initializer =>
        (case source_module_resolve_type ctx annotation of SM_Ok resolution =>
          (case source_type_vtype resolution of Type ty =>
            SOME ((ctx.sm_owner ++ [name],
              (ty,SMR_Global (ctx.sm_env.current_src,name)))::rest)
           | _ => NONE)
         | _ => NONE)
      | _ => SOME rest
End

Datatype:
  source_location_body = SMLB_Pass | SMLB_Return (source_location_meaning option)
    | SMLB_Expr source_location_meaning
    | SMLB_Local string type source_location_meaning
    | SMLB_Assign source_reference source_location_meaning
    | SMLB_If source_location_meaning (source_location_body list) (source_location_body list)
End

Definition source_location_run_def:
  source_location_run cx SMLB_Pass = return () /\
  source_location_run cx (SMLB_Return NONE) = raise (ReturnException NoneV) /\
  source_location_run cx (SMLB_Return (SOME m)) = do
    tv <- source_location_eval cx m;
    v <- materialise cx tv;
    raise (ReturnException v)
  od /\
  source_location_run cx (SMLB_Expr m) = do
    tv <- source_location_eval cx m;
    type_check (~is_HashMapRef tv) "Expr HashMapRef"
  od /\
  source_location_run cx (SMLB_Local id ty m) = do
    t <- lift_option_type (evaluate_type (get_tenv cx) ty) "AnnAssign evaluate_type";
    tv <- source_location_eval cx m;
    v <- materialise cx tv;
    new_variable id t v
  od /\
  source_location_run cx (SMLB_Assign r m) = do
    gv <- (do (loc,subs) <- source_reference_target cx r;
      return (BaseTargetV loc subs) od);
    tv <- source_location_eval cx m;
    v <- materialise cx tv;
    assign_target cx gv (Replace v);
    return ()
  od /\
  source_location_run cx (SMLB_If c yes no) = do
    tv <- source_location_eval cx c;
    push_scope;
    finally (switch_BoolV tv (source_location_runs cx yes) (source_location_runs cx no)) pop_scope
  od /\
  source_location_runs cx [] = return () /\
  source_location_runs cx (m::ms) = do
    source_location_run cx m;
    source_location_runs cx ms
  od
Termination
  WF_REL_TAC `measure (\x. case x of INL (cx,m) => source_location_body_size m
    | INR (cx,ms) => list_size source_location_body_size ms)` >> simp[]
End

Inductive source_location_body_source:
[empty_bodies:]
  source_location_bodies_source refs type_ids ctx ret [] [] refs ctx
[cons_bodies:]
  source_location_body_source refs type_ids ctx ret s bm next_refs next_ctx /\
  source_location_bodies_source next_refs type_ids next_ctx ret ss ms final_refs final_ctx ==>
  source_location_bodies_source refs type_ids ctx ret (s::ss) (bm::ms) final_refs final_ctx
[pass_body:]
  source_location_body_source refs type_ids ctx ret SS_Pass SMLB_Pass refs ctx
[return_none:]
  source_location_body_source refs type_ids ctx ret (SS_Return NONE) (SMLB_Return NONE) refs ctx
[return_value:]
  source_location_source refs type_ids ctx.sm_scopes ctx.sm_table ctx.sm_constants ret original m ==>
  source_location_body_source refs type_ids ctx ret (SS_Return (SOME original))
    (SMLB_Return (SOME m)) refs ctx
[expression_body:]
  source_location_source refs type_ids ctx.sm_scopes ctx.sm_table ctx.sm_constants ty original m ==>
  source_location_body_source refs type_ids ctx ret (SS_Expr original) (SMLB_Expr m) refs ctx
[local_body:]
  source_module_type ctx annotation = SM_Ok ty /\
  source_module_interface_fields ctx annotation = NONE /\
  source_location_source refs type_ids ctx.sm_scopes ctx.sm_table ctx.sm_constants ty original m ==>
  source_location_body_source refs type_ids ctx ret (SS_AnnAssign name annotation (SOME original))
    (SMLB_Local name ty m) ((ctx.sm_owner ++ [name],(ty,SMR_Local name))::refs)
    (source_module_local ctx name ty T)
[assign_body:]
  source_expr_path target = SOME names /\
  source_resolve_name ctx.sm_scopes ctx.sm_table names = SOME (path,SR_Dynamic) /\
  ALOOKUP refs path = SOME (ty,r) /\
  source_location_source refs type_ids ctx.sm_scopes ctx.sm_table ctx.sm_constants ty original m ==>
  source_location_body_source refs type_ids ctx ret (SS_Assign target original)
    (SMLB_Assign r m) refs ctx
[if_body:]
  source_location_source refs type_ids ctx.sm_scopes ctx.sm_table ctx.sm_constants (BaseT BoolT) original m /\
  source_location_bodies_source refs type_ids ctx ret yes ym yr yc /\
  source_location_bodies_source refs type_ids ctx ret no nm nr nc ==>
  source_location_body_source refs type_ids ctx ret (SS_If original yes no)
    (SMLB_If m ym nm) refs ctx
End

Definition source_reference_code_def:
  source_reference_code (SMR_Local id) = NameTarget id /\
  source_reference_code (SMR_Global id) = TopLevelNameTarget id
End

Inductive source_location_body_code:
[empty_code:]
  source_location_bodies_code tenv [] []
[cons_code:]
  source_location_body_code tenv bm s /\ source_location_bodies_code tenv ms ss ==>
  source_location_bodies_code tenv (bm::ms) (s::ss)
[pass_code:]
  source_location_body_code tenv SMLB_Pass Pass
[return_none_code:]
  source_location_body_code tenv (SMLB_Return NONE) (Return NONE)
[return_value_code:]
  source_location_code tenv m e ==>
  source_location_body_code tenv (SMLB_Return (SOME m)) (Return (SOME e))
[expression_code:]
  source_location_code tenv m e ==>
  source_location_body_code tenv (SMLB_Expr m) (Expr e)
[local_code:]
  source_location_code tenv m e ==>
  source_location_body_code tenv (SMLB_Local id ty m) (AnnAssign id ty e)
[assign_code:]
  source_location_code tenv m e ==>
  source_location_body_code tenv (SMLB_Assign r m) (Assign (BaseTarget (source_reference_code r)) e)
[if_code:]
  source_location_code tenv c ce /\
  source_location_bodies_code tenv ym yes /\ source_location_bodies_code tenv nm no ==>
  source_location_body_code tenv (SMLB_If c ym nm) (If ce yes no)
End

Theorem source_reference_code_evaluates:
  eval_base_target cx (source_reference_code r) = source_reference_target cx r
Proof
  Cases_on `r` >> simp[source_reference_code_def,source_reference_target_def,Once evaluate_def] >>
  rename1 `SMR_Global gid` >> Cases_on `gid` >>
  simp[source_reference_target_def,Once evaluate_def]
QED

Theorem source_location_body_code_evaluates:
  !tenv.
  (!m s. source_location_body_code tenv m s ==>
    !cx. get_tenv cx = tenv ==> eval_stmt cx s = source_location_run cx m) /\
  (!ms ss. source_location_bodies_code tenv ms ss ==>
    !cx. get_tenv cx = tenv ==> eval_stmts cx ss = source_location_runs cx ms)
Proof
  gen_tac >> CONV_TAC (REWR_CONV CONJ_COMM) >>
  ho_match_mp_tac source_location_body_code_ind >> rpt conj_tac >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  imp_res_tac (CONJUNCT1 (SPEC_ALL source_location_code_evaluates)) >>
  simp[evaluate_def,source_location_run_def,source_reference_code_evaluates]
QED
