(* Immutable assignment targets are typed only in constructors.  The
   runtime body pointer judgement therefore follows from its constructor
   guard; constructor pointer judgements retain their separate contracts. *)
Theory bodyPtrImmutableDeploy
Ancestors
  bodyPtrPreds bodyPtrDefs bodyAssignPlace bodySim vyperTypeSystem

Theorem body_assign_immutable_deploy_ptr:
  !cx t e d PG tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
                 body_base_target_ptr_ok cx t) /\
    body_expr_ptr_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ ~is_abi_dynamic cenv.ce_struct_fields ty /\
        (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    immutable_root cx t ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac body_assign_immutable_target >> gvs[] >>
  Cases_on `supported_immutable_type tops nsid` >> gvs[] >>
  `?dty. type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty)` by
    (qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
     rpt strip_tac >>
     Cases_on `type_place_target env (TopLevelNameTarget nsid)` >> gvs[] >>
     rename1 `SOME pt` >> Cases_on `pt` >> gvs[]) >>
  drule_all_then strip_assume_tac body_immutable_target_type >>
  fs[stmt_frag_ptr_cx_dead, body_inv_def]
QED
