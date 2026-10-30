(*
 * The body simulation of S1: declaration cases (#637)
 *
 * The cases of body_sim_mutual that declare a local: AnnAssign, and For,
 * whose loop variable is one.  Every declaration lemma (stmtSimDecl,
 * stmtSimDeclMem, stmtSimDeclEmpty, stmtSimFor, stmtSimForRange) asks
 * that the declared name is unbound in the compile env or held through a
 * pointer.  The typing declares only a name not in env.var_types, and
 * ce_locals_declared (bodySim) binds no other local, so the name is
 * unbound unless it is a module variable's key, the gap
 * declared_name_unbound leaves open.  The loop's scope pop also rests on
 * bodySimStmtCases' GAP eval_stmts_popped_keys_indexed.
 *
 * TOP-LEVEL:
 *   declared_name_unbound        — GAP, a declared name is unbound
 *   declare_local_same_frame, expr_sim_inv_declare_local — the compile
 *                                  env of a declaration is a frame where
 *                                  the statement's expressions simulate
 *   expr_sim_inv_for_scope, expr_sim_inv_for_pop — expr_sim_inv into
 *                                  and out of a loop iteration's scope
 *   body_annassign_case, body_for_case — the cases
 *   body_annassign_other         — RESIDUAL, the declarations not of a
 *                                  word type
 *   body_for_other               — RESIDUAL, the loops but over a range
 *                                  of literals
 *)

Theory bodySimDeclCases
Ancestors
  list finite_map bodySim bodySimStmtCases exprSim exprSimHyps
  exprLoweringProps stmtSim stmtSimDecl stmtSimReturn stmtSimAssign
  stmtSimFor stmtSimForParts stmtSimForRange stmtLowering stmtLoweringMono
  fragExec compileEnv supportedStmts supportedStmtTraverse vyperAST
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeValues
  vyperTypeEvalSoundness vyperTypeEnvPreservation vyperTypeEnvExtension
  vyperTypeScopePop vyperEvalOutcomeSuffix vyperTypeCallGraph
  vyperTypeCallStackSoundness compileVyper moduleLowering intCallCallee
Libs
  monadsyntax

(* ===== Declared names ===== *)

(* GAP (#637 declarations): the typing declares only a name it does not
   know, which the compile env then does not bind.  False at the current
   lowering for a local spelled as a module variable's key ("self." ++
   ...): ce_vars holds module variables at module_var_key nsid and locals
   at their names, so a local named so would find the module variable's
   binding (supported_function_bindings rules such names out for a
   supported program, but the body predicates do not carry it).  The
   change that moves module variables to compile-env fields of their own,
   as the Python compiler keeps them apart, makes ce_vars hold locals only;
   ce_locals_declared then loses its module-key exception and this follows
   from it:
     rpt gen_tac >> strip_tac >>
     `id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
     fs[ce_locals_declared_def] >> metis_tac[] *)
Theorem declared_name_unbound:
  !cenv env ret_ty s env' id.
    ce_locals_declared cenv env /\ type_stmt env ret_ty s = SOME env' /\
    ((?typ e. s = AnnAssign id typ e) \/
     (?typ it n body. s = For id typ it n body)) ==>
    FLOOKUP cenv.ce_vars id = NONE
Proof
  cheat
QED

(* ===== The compile env of a declaration ===== *)

Theorem declare_local_same_frame:
  !cenv id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) ==>
    same_frame cenv c
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  rw[same_frame_def] >> Cases_on `n = id` >> gvs[]
QED

(* Declaring a name the typing does not know keeps expr_sim_inv: its
   clauses speak of the names in env.var_types only. *)
Theorem expr_sim_inv_declare_local:
  !cenv cx env es id ty st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx env es
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  `c.ce_var_type = (id =+ SOME ty) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
          LET_THM] >> strip_tac >> gvs[]) >>
  `c.ce_flag_member_id = cenv.ce_flag_member_id /\
   c.ce_flag_n_members = cenv.ce_flag_n_members /\
   c.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_x_assum `_ with <| ce_vars := _; ce_var_type := _;
                             ce_dynarray_capacity := _ |> = cenv`
       (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> n <> id` by
    (rpt strip_tac >> gvs[FLOOKUP_DEF]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==>
         ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
    metis_tac[] >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> c.ce_var_type n = SOME t` by
    (rw[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def]
QED

(* ===== AnnAssign ===== *)

(* A declaration of a word type: stmtSimDecl's
   compile_annassign_typed_stmt_frag.  A word type takes no wider type, so
   the value has the declared type itself. *)
Theorem body_annassign_word[local]:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    eval_stmt cx (AnnAssign id typ e) es = (res, es') /\
    is_word_type typ ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e)) es res es'
Proof
  rpt strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env e /\ expr_type e = typ /\
   id NOTIN FDOM env.var_types` by
    (gvs[type_stmt_def, AllCaseEqs()] >> metis_tac[type_widens_to_word]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `body_expr_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  irule compile_annassign_typed_stmt_frag >>
  simp[is_word_type_no_length_word, wordsTheory.dimword_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def]) >>
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- metis_tac[compile_expr_grows] >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `expr_body_pre c cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[]) >>
  metis_tac[body_expr_ok_def, body_inv_same_frame]
QED

(* RESIDUAL (#637 declarations): a declaration of a type that is not a
   word.  The name is unbound (declared_name_unbound), but:
   - a value in memory: stmtSimDeclMem's
     compile_annassign_memory_stmt_frag and
     compile_annassign_memory_widen_stmt_frag ask of the declared type
     type_memory_bytes cenv vtyp = type_memory_size tyv,
     0 < type_memory_size tyv and type_memory_size tyv + 64 < dimword (:256),
     and the last has nothing behind it: no clause bounds a local's size
     (Python's allocator rejects a frame past 2 ** 64 bytes,
     MemoryAllocationException; the lowering has no such check), as for
     Assign's memory locals (body_assign_other);
   - empty(T) of a type with a length word: stmtSimDeclEmpty's
     compile_annassign_empty_stmt_frag asks
     type_memory_size tyv < dimword (:256) of the declared type, which may
     be wider than e's (type_widens_to), so alloc_limits_expr of e does
     not bound it either. *)
Theorem body_annassign_other:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (AnnAssign id typ e) es = (res, es') /\
    ~is_word_type typ ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e)) es res es'
Proof
  cheat
QED

Theorem body_annassign_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) ==>
    body_stmt_ok cx (AnnAssign id typ e)
Proof
  rw[body_stmt_ok_def] >> Cases_on `is_word_type typ`
  >- (irule body_annassign_word >> metis_tac[]) >>
  irule body_annassign_other >> metis_tac[]
QED

(* ===== For ===== *)

(* The scope of a loop's iteration: the loop variable, declared in the
   compile env and added to the type environment. *)
Theorem for_pushed_state_well_typed[local]:
  !st tyv v id.
    state_well_typed st /\ value_has_type tyv v /\
    well_formed_type_value tyv ==>
    state_well_typed
      (st with scopes updated_by
         CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                                popped := []|>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem for_pushed_popped_keys[local]:
  !scs id tyv v.
    popped_keys_indexed scs ==>
    popped_keys_indexed
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                        popped := []|>) :: scs)
Proof
  rw[popped_keys_indexed_def, FLOOKUP_UPDATE] >> gvs[]
QED

Theorem scopes_CONS_updated[local]:
  !es x. es with scopes := x :: es.scopes = es with scopes updated_by CONS x
Proof
  simp[evaluation_state_component_equality]
QED

Theorem expr_sim_inv_for_scope:
  !cenv cx env es id fty tyv v st c st1.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    declare_local cenv id fty st = (c, st1) /\ cenv.ce_alloca_locals ==>
    expr_sim_inv c cx (extend_local env id fty F)
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes)
Proof
  rpt strip_tac >> REWRITE_TAC [scopes_CONS_updated] >>
  `env_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `popped_keys_indexed
     (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                       popped := []|>) :: es.scopes)` by
    simp[for_pushed_popped_keys] >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_var_type = (id =+ SOME fty) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
          LET_THM] >> strip_tac >> gvs[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
          ?p sz. FLOOKUP c.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM] >>
     metis_tac[]) >>
  `!n ty. FLOOKUP (extend_local env id fty F).var_types n = SOME ty ==>
          c.ce_var_type n = SOME ty` by
    (rpt gen_tac >> Cases_on `n = id` >>
     simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM,
          combinTheory.APPLY_UPDATE_THM]) >>
  qpat_x_assum
    `_ with <| ce_vars := _; ce_var_type := _;
               ce_dynarray_capacity := _ |> = cenv`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[]
QED

(* After an iteration that goes on (a normal end or a continue), with the
   loop variable's scope popped, expr_sim_inv holds again at the loop's
   compile and type environments: the type soundness of the body, and
   vyperTypeEvalSoundness's for_body_env_consistent_after_pop. *)
Theorem expr_sim_inv_for_pop:
  !cenv cx env es id fty tyv v ret_ty body env_b r2 es2 sc rest.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_stmts cx body
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes) = (r2, es2) /\
    (r2 = INL () \/ r2 = INR ContinueException) /\
    es2.scopes = sc :: rest ==>
    expr_sim_inv cenv cx env (es2 with scopes := rest)
Proof
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  RULE_ASSUM_TAC (REWRITE_RULE [scopes_CONS_updated]) >>
  `env_consistent (extend_local env id fty F) cx
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>)))` by
    (irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all for_pushed_state_well_typed >>
  disch_then (qspec_then `id` assume_tac) >>
  `accounts_well_typed
     (es with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                               popped := []|>))).accounts` by simp[] >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> strip_tac >>
  `env_maps_wf env` by metis_tac[env_consistent_env_maps_wf] >>
  `env_consistent env cx (es2 with scopes := TL es2.scopes)` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
     qpat_x_assum `sum_CASE _ _ _` mp_tac >> simp_tac (srw_ss()) [] >>
     strip_tac
     >- (irule for_body_env_consistent_after_pop >> metis_tac[]) >>
     irule for_body_env_extends_consistent_after_pop >> metis_tac[]) >>
  `state_well_typed (es2 with scopes := TL es2.scopes)` by
    (irule scope_bracket_preserves_swt >> metis_tac[]) >>
  `outcomes_accounts_typed es2.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 2 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  `popped_keys_indexed es2.scopes` by
    (drule (cj 2 eval_stmts_popped_keys_indexed) >> disch_then irule >>
     simp[for_pushed_popped_keys]) >>
  `popped_keys_indexed rest` by gvs[popped_keys_indexed_def] >>
  qpat_x_assum `es2.scopes = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (REWRITE_RULE [TL]) >>
  ASM_REWRITE_TAC [expr_sim_inv_def] >> simp[]
QED

Theorem compile_stmts_grows[local]:
  !c lc ty stmts sa sb.
    compile_stmts c lc ty stmts sa = ((), sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >>
  simp[]
QED

Theorem is_int_type_word[local]:
  !t. is_int_type t ==> is_word_type t
Proof
  Cases >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def]
QED

(* A range of literals: stmtSimFor's compile_for_range_lit_frag, whose
   invariant is expr_sim_inv at the loop's environments.  The literals'
   type bounds the rounds below 2 ** 256. *)
Theorem body_for_range_lit[local]:
  !cx id typ a1 n1 a2 n2 n stmts tops bindings ctx func cenv env env'
   ret_ty lctx RetQ es res es'.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\
       eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id stmts vs) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) = SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
            stmts)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
         stmts) es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) n
            stmts)) es res es'
Proof
  rpt strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `id NOTIN FDOM env.var_types /\ is_int_type typ /\
   well_typed_literal typ (IntL n1) /\ well_typed_literal typ (IntL n2) /\
   well_formed_type env.type_defs typ /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, well_typed_expr_def,
        expr_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  `n1 <= n2 /\ n = Num (n2 - n1) /\ supported_stmts tops bindings stmts` by
    gvs[supported_stmt_def, supported_iterator_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `!k. well_typed_literal typ (IntL k) ==> value_has_type tyv (IntV k)` by
    (rpt strip_tac >> drule_all well_typed_literal_sound >>
     simp[vyperValueOperationTheory.evaluate_literal_def]) >>
  `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)) <> [] ==>
   body_stmts_ok cx stmts` by
    (strip_tac >>
     first_x_assum (qspecl_then [`get_tenv cx`, `es`, `tyv`, `es`, `es`,
       `GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))`, `es`, `es`, `()`,
       `es`] mp_tac) >>
     simp[lift_option_type_def, return_def, eval_iterator_range_lit,
          check_def, assert_def, compatible_bound_def, body_for_ok_def]) >>
  `Num (n2 - n1) < dimword (:256)` by metis_tac[range_end_words] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  drule_all is_int_type_word >> strip_tac >>
  drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
  `call_evaluation_safe cx (int_calls_stmts stmts)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `EVERY (stmt_exprs_ok cenv) stmts` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY] >>
  MATCH_MP_TAC
    (BETA_RULE (Q.SPEC `\ei. expr_sim_inv cenv cx env ei`
                  compile_for_range_lit_frag)) >>
  qexists_tac `tyv` >> simp[wordsTheory.dimword_def] >> rpt conj_tac
  >- metis_tac[compile_stmts_grows]
  >- (rpt strip_tac >>
      `body_stmts_ok cx stmts` by
        (first_x_assum irule >> simp[listTheory.GENLIST_EQ_NIL] >>
         strip_tac >> gvs[]) >>
      `same_frame cenv c` by
        (drule_then irule declare_local_same_frame >> simp[]) >>
      `value_has_type tyv (IntV (n1 + &j))` by
        (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
      qpat_x_assum `body_stmts_ok _ _`
        (irule o REWRITE_RULE [body_stmts_ok_def]) >>
      simp[] >> rpt conj_tac
      >- metis_tac[stmt_exprs_ok_same_frame]
      >- metis_tac[body_inv_same_frame]
      >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
          metis_tac[expr_sim_inv_for_scope, ce_locals_declared_declare_local]) >>
      metis_tac[frame_ret_ok_same_frame]) >>
  rpt strip_tac >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (irule range_value_has_type >> simp[] >> qexists_tac `n2` >> simp[]) >>
  (irule expr_sim_inv_for_pop >> conj_tac >- metis_tac[] >>
   qexistsl_tac [`stmts`, `env_b`, `ei`, `typ`, `id`, `r2`, `ret_ty`, `tyv`,
                 `IntV (n1 + &j)`] >>
   simp[])
QED

(* RESIDUAL (#637 for): a loop over a range whose ends are not both
   literals, or over an array.
   - stmtSimForRange's compile_for_range_checked_frag asks
     bound < dimword (:256), which nothing gives: supported_iterator asks
     only 0 < bound of such a range, and the source has no limit on a
     loop's bound;
   - it asks too that the two ends do not both lower to Lit: the
     lowering skips the checks when both do, which turns on the ends'
     code, not their syntax, and compile_for_range_lit_frag covers only
     literal ends;
   - iteration over an array has no lemma (#559). *)
Theorem body_for_other:
  !cx id typ it n body tops bindings ctx func cenv env env' ret_ty lctx RetQ
   es res es'.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (For id typ it n body) es = (res, es') /\
    ~(?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body)) es res es'
Proof
  cheat
QED

Theorem body_for_case:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx it) ==>
    body_stmt_ok cx (For id typ it n body)
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [body_stmt_ok_def] >>
  rpt strip_tac >>
  Cases_on `?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))`
  >- (qpat_x_assum `?a1 n1 a2 n2. _`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) >>
      drule_all body_for_range_lit >> simp[]) >>
  drule_all body_for_other >> simp[]
QED
