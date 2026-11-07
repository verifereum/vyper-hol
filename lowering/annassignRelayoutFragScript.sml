(* Declaration prefix and public fragment for typed aggregate relayout. *)
Theory annassignRelayoutFrag
Ancestors
  annassignRelayoutCompose annassignRelayoutSource annassignRelayoutCode
  loweringSlice stmtSimDeclMem stmtSimDecl stmtSimDeclCompose
  stmtSimDeclPath stmtSimDeclSource stmtSimProps exprSimProps exprOperandVar
  exprLoweringProps stmtLoweringMono emitHelperProps fragExec
  stmtSimDefs exprSimDefs loweringPosts exprLowering stmtLowering compileEnv
  context venomInst venomState localPtrsProps
  exprSimHyps exprSimHypsDefs exprSimIfExpCompat exprSimSource vyperTypeSystem vyperTypeInvariants
  exprOpenTerminals exprOpenPrimitives
Libs monadsyntax

Theorem annassign_relayout_code_parts:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c,sf) /\
    cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa ==>
    ?st sA sV sB vv op p.
      declare_local cenv id vtyp sa = (c,st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((),sA) /\
      compile_expr c (expr_type e) e sA = (vv,sV) /\
      unwrap_value c vv sV = (op,sB) /\
      lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
        (lowered_value_type cenv e)
        (case vtyp of ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes c et + 31) DIV 32, type_memory_bytes c et)
         | _ => NONE) (type_memory_bytes c vtyp) sB = ((),sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      ci_mono sA sB /\ ci_mono sB sf /\ cs_extends st sA /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) _)` >>
  `c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_func_return_type = cenv.ce_func_return_type` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
      ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  `(!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
   (!e. lowered_value_type c e = lowered_value_type cenv e)` by
    (conj_tac >- metis_tac[type_memory_bytes_struct_fields] >>
     simp[oneline lowered_value_type_def]) >>
  `?sA sV sB vv op.
     emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((),sA) /\
     compile_expr c (expr_type e) e sA = (vv,sV) /\
     unwrap_value c vv sV = (op,sB) /\
     lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
     compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
       (lowered_value_type cenv e)
       (case vtyp of ArrayT et (Dynamic _) =>
          SOME ((type_memory_bytes c et + 31) DIV 32, type_memory_bytes c et)
        | _ => NONE) (type_memory_bytes c vtyp) sB = ((),sf)` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_inst_unit >>
     gvs[lower_value_def, comp_bind_def] >> metis_tac[]) >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `ci_mono sA sB` by metis_tac[cj 2 compile_expr_grows, ci_mono_def] >>
  `ci_mono sB sf` by metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `cs_extends sA sf` by metis_tac[ci_mono_def, cs_extends_trans] >>
  unabbrev_all_tac >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  qexistsl_tac [`st`, `sA`, `sV`, `sB`, `vv`, `op`,
    `STRING #"%" (toString sa.cs_next_var)`] >> simp[] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]
QED

Theorem residual_call_compile_location:
  !cenv cx env e es ty sa vv sb.
    expr_body_pre cenv cx env e es /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    compile_expr cenv ty e sa = (vv,sb) ==>
    (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `cenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  metis_tac[internal_call_location_cases, compile_intcall_open]
QED

(* The widened RHS's post type is its lowered type, in a context small
   enough that the case split on the call stays cheap. *)
Theorem relayout_post_value_type[local]:
  !c cenv env e typ.
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    sfields_tenv_consistent c.ce_struct_fields env.type_defs /\
    (!e. lowered_value_type c e = lowered_value_type cenv e) /\
    expr_type e = typ /\ ~is_word_type typ /\ ~is_bytestring_type typ /\
    lowered_value_type cenv e <> typ ==>
    post_value_type c e = lowered_value_type cenv e
Proof
  rpt strip_tac >> drule_all ifexp_lowered_type_classify >> strip_tac >>
  gvs[post_value_type_def, vyperASTTheory.expr_type_def]
QED

Theorem compile_annassign_relayout_stmt_frag:
  !ctx func cx lctx RetQ cenv ret_ty id typ e es stv tyv.
    cenv.ce_alloca_locals /\ ~is_word_type typ /\ ~is_bytestring_type typ /\
    ~(has_length_word typ /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    expr_type e = typ /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    lowered_value_type cenv e <> typ /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) typ /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    type_memory_bytes cenv typ = type_memory_size tyv /\
    type_memory_bytes cenv typ < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!gs v es1. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type tyv v /\
       val_wf stv v /\ val_wf tyv v /\ val_footprint stv v = type_memory_size stv) /\
    (!st0 c st1. declare_local cenv id typ st0 = (c,st1) ==>
      expr_sim ctx func c cx (expr_type e) e es /\
      ?env. expr_body_pre c cx env e es) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all annassign_relayout_code_parts >>
  disch_then (qx_choosel_then [`st`, `sA`, `sV`, `sB`, `vv`, `op`, `p`] strip_assume_tac) >>
  rename1 `declare_local cenv id typ sa = (c,st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields /\
   c.ce_func_return_type = cenv.ce_func_return_type` by
    (drule_all declare_local_ptr >> strip_tac >>
     qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
       ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  `(!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
   (!e. lowered_value_type c e = lowered_value_type cenv e)` by
    (conj_tac >- metis_tac[type_memory_bytes_struct_fields] >>
     simp[oneline lowered_value_type_def]) >>
  `stmt_state_rel ctx func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `s0.vs_current_bb = st.cs_current_bb /\
   s0.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
  drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule annassign_admissible_rhs >> metis_tac[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,salloc)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func c cx e es sA sB salloc ee v op t /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
     simp[expr_sim_def] >> disch_then irule >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   FLOOKUP salloc.vs_allocas ai.inst_id =
     SOME (w2n w, type_memory_bytes cenv typ) /\ ai.inst_id < sA.cs_next_id` by
    (simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
     drule emit_inst_extends >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
    (`sA.cs_next_var = st.cs_next_var` by
       (drule emit_inst_extends >> simp[]) >>
     drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
   ~block_is_terminated sV` by
    (irule residual_call_compile_location >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `~block_is_terminated sB` by (drule_all unwrap_value_open >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sB x` by metis_tac[compile_lower_value_var] >>
  `post_value_type c e = lowered_value_type cenv e` by
    (`well_typed_expr env e /\
      sfields_tenv_consistent c.ce_struct_fields env.type_defs` by
       fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
          env_context_consistent_def] >>
     match_mp_tac relayout_post_value_type >> qexistsl_tac [`env`, `typ`] >>
     simp[] >> metis_tac[expr_body_pre_var_types_well_formed]) >>
  (irule annassign_outcome_entry_prefix >>
  qexistsl_tac [`sA`, `salloc`] >> simp[] >>
  irule annassign_relayout_rhs_outcome >>
  goal_assum (drule_at Any) >> simp[ci_mono_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `ai` >> gvs[ci_mono_def] >> metis_tac[])
QED
