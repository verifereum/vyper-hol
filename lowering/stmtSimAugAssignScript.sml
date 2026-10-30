(*
 * Statement simulation: an augmented assignment to a word local (#637)
 *
 * AugAssign over stmt_frag (stmtSim) for x op= e where x is a local held
 * through its pointer and of a type whose values are word_values.  x op= e
 * is x = x op e on both sides: the source reads x, evaluates e, runs the
 * operator and writes x, as evaluating the expression x op e annotated with
 * x's type and then writing x would, and the lowering is x op e's lowering
 * at x's type (an MLOAD of the pointer, e, compile_binop) and then an
 * MSTORE at the pointer.  So the expression side is compile_bop_word_case's
 * (exprSimOperators), the checked operators' aborts (overflow, division by
 * zero) among its exits, and ** and the narrow or negative shifts rest on
 * exprSimBinopFrag's cheats (#572).  The store is stmtSimAssignStore's.
 *
 * TOP-LEVEL:
 *   compile_augassign_local_case      — x op= e on a word local, for every
 *                                       outcome, given e's expr_sim_case
 *   compile_augassign_local_stmt_frag — the same, given e's expr_sim_ok
 *   eval_augassign_local_bop          — x op= e evaluates as x op e, then
 *                                       writes x
 *   augassign_local_code_bop          — its code is x op e's, then MSTORE
 *)

Theory stmtSimAugAssign
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim exprSimHyps exprSimOps exprSimBinopFrag
  exprSimOperators exprSimLeaves loweringSlice stmtSim stmtSimDecl
  stmtSimDeclStore stmtSimAssignStore
  exprLowering exprBopLowering stmtLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperTypeSystem vyperTyping vyperTypeEnv
  vyperTypeInvariants vyperTypeCallGraph vyperLookup vyperAST
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* ===== The source side ===== *)

(* A local in scope: its target place, the value there and its type. *)
Theorem eval_target_place_local:
  !cx id es entry.
    lookup_scopes id es.scopes = SOME entry ==>
    eval_target_place cx (NameTarget id) es = (INL (MemoryPlace id []), es) /\
    read_place cx (MemoryPlace id []) es = (INL entry.value, es) /\
    place_type_value cx (MemoryPlace id []) es = (INL entry.type, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, get_place_def, return_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, get_place_def] >>
  simp[read_place_def, place_type_value_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, read_memory_path_def,
       evaluate_subscripts_def, subscripts_type_def, lift_sum_def]
QED

(* x op= e on a local x in scope: x's place, its value and its type are read
   without changing the state, e is evaluated, then the operator runs on
   x's value and e's, and the result is written to x. *)
Theorem eval_augassign_local:
  !cx ty id bop e es res es' entry.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 entry.type bop entry.value v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r => write_place cx (MemoryPlace id []) r es1 = (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `cx` strip_assume_tac) eval_target_place_local >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r0, st0)` >>
  Cases_on `r0` >> simp[] >>
  rename1 `eval_expr cx e es = (INL raw, st0)` >>
  Cases_on `read_result cx raw st0` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  qmatch_goalsub_abbrev_tac `evaluate_binop u entry.type bop entry.value v1` >>
  Cases_on `evaluate_binop u entry.type bop entry.value v1` >>
  simp[lift_sum_def, return_def, raise_def]
QED

(* The operator's type argument matters only for in and not in on an
   array. *)
Theorem evaluate_binop_tv:
  !u tv tv' bop v1 v2.
    bop <> In /\ bop <> NotIn ==>
    evaluate_binop u tv bop v1 v2 = evaluate_binop u tv' bop v1 v2
Proof
  rpt strip_tac >> Cases_on `bop` >> gvs[] >>
  ONCE_REWRITE_TAC [evaluate_binop_def] >> simp[] >>
  ONCE_REWRITE_TAC [evaluate_binop_def] >> simp[]
QED

(* ===== The code ===== *)

(* x op= e on a local x held through its pointer p: no declaration, x's
   target is p itself with no code, then MLOAD, e lowered at x's type, the
   operator and MSTORE. *)
Theorem augassign_local_code_parts:
  !cenv lctx ty0 ty id bop e sa c sf p sz.
    stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op MLOAD [Var p] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void MSTORE [Var p; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `emit_op MLOAD [Var p] sa` >> rename1 `_ = (cur_op, s1)` >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs_op, s2)` >> simp[] >>
  Cases_on `compile_binop bop cur_op rhs_op ty NONE
              (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `_ = (res_op, s3)` >> simp[] >>
  Cases_on `emit_void MSTORE [Var p; res_op] s3` >> simp[oneTheory.one]
QED

(* ===== The operator ===== *)

(* The types the type checker allows for x op= e, with op neither in nor
   not in (type_stmt), are word_value_types. *)
Theorem well_typed_binop_augassign_word:
  !ty bop t2.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn ==>
    word_value_type ty /\ word_value_type t2
Proof
  Cases_on `bop` >> rw[well_typed_binop_def, word_value_type_def] >> gvs[]
QED

Theorem word_value_type_memory_size:
  !tenv t tv.
    word_value_type t /\ evaluate_type tenv t = SOME tv ==>
    type_memory_size tv = 32
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT \/ t = BaseT BoolT \/ (?nsid. t = FlagT nsid)` by
    (Cases_on `t` >> fs[word_value_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_int_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), type_memory_size_def]
QED

(* The source's operator on x's value and e's is the operator of the
   expression x op e annotated with x's type: the builtin reads its type
   argument from e's type, x op= e from x's place, and neither matters
   but for in and not in. *)
Theorem bop_result_augassign:
  !cx ty bop t2 v1 v2 es tv.
    bop <> In /\ bop <> NotIn ==>
    bop_result cx ty bop [ty; t2] v1 v2 es =
    case evaluate_binop
           (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
           tv bop v1 v2 of
      INL v => INL v
    | INR err => INR (Error err)
Proof
  rpt strip_tac >> simp[bop_result_def, evaluate_builtin_def] >>
  metis_tac[evaluate_binop_tv]
QED

(* ===== x op= e is x = x op e ===== *)

(* The source: x op= e on a local x in scope evaluates as the expression
   x op e annotated with x's type would, then writes its value to x. *)
Theorem eval_augassign_local_bop:
  !cx ty id bop e es res es' entry.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn ==>
    ?r es1.
      (do tv <- eval_expr cx (Builtin ty (Bop bop) [Name ty id; e]);
          read_result cx tv od) es = (r, es1) /\
      case r of
        INR ex => res = INR ex /\ es' = es1
      | INL v => write_place cx (MemoryPlace id []) v es1 = (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_augassign_local >> strip_tac >>
  Cases_on `(do tv <- eval_expr cx (Builtin ty (Bop bop) [Name ty id; e]);
                read_result cx tv od) es` >>
  rename1 `bind (eval_expr cx (Builtin _ _ _)) _ es = (rr, es2)` >> simp[] >>
  `!ann. (do r0 <- eval_expr cx (Name ann id); read_result cx r0 od) es =
          (INL entry.value, es)` by metis_tac[eval_name_word] >>
  drule eval_expr_bop_cases >> simp[] >> strip_tac >>
  `!w st. bop_result cx ty bop [ty; expr_type e] entry.value w st =
          case evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 entry.type bop entry.value w of
            INL v => INL v
          | INR err => INR (Error err)` by
    (rpt gen_tac >> irule bop_result_augassign >> simp[]) >>
  gvs[vyperASTTheory.expr_type_def] >>
  Cases_on `evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              entry.type bop entry.value v2` >> gvs[]
QED

(* The code: x op= e on a local held through its pointer is the lowering
   of x op e at x's type, then an MSTORE of its result at the pointer. *)
Theorem augassign_local_code_bop:
  !cenv lctx ty0 ty id bop e sa c sf p sz.
    stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    c = cenv /\
    ?s3 res_op.
      lower_value compile_expr cenv ty (Builtin ty (Bop bop) [Name ty id; e])
        sa = (res_op, s3) /\
      emit_void MSTORE [Var p; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all augassign_local_code_parts >> strip_tac >> simp[] >>
  `is_word_type ty /\ ~is_bytestring_type ty` by
    metis_tac[word_value_type_word] >>
  Cases_on `lower_value compile_expr cenv ty
              (Builtin ty (Bop bop) [Name ty id; e]) sa` >>
  rename1 `_ = (op', s')` >>
  drule lower_value_bop >> simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  drule_all lower_value_name_word >> strip_tac >>
  gvs[expr_int_literal_def]
QED

(* A well-formed type's width is whole bytes: Vyper's int widths are
   multiples of 8, and decimal and every other type are 168 or 256 bits. *)
Theorem well_formed_type_bits:
  !tenv ty. well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  Cases_on `ty` >> simp[type_bits_def] >> rename1 `BaseT bt` >>
  Cases_on `bt` >>
  rw[type_bits_def, well_formed_type_def, vyperValueTheory.evaluate_type_def]
QED

(* The typing side: x op e meets expr_sim_pre where e does, x is a local
   of type ty and the type checker accepts x op= e. *)
Theorem expr_sim_pre_augassign:
  !cenv cx env ty id bop e es.
    expr_sim_pre cenv cx env e es /\ FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) ==>
    expr_sim_pre cenv cx env (Builtin ty (Bop bop) [Name ty id; e]) es
Proof
  rpt strip_tac >>
  drule expr_sim_pre_var_types_well_formed >>
  disch_then drule >> strip_tac >>
  drule well_formed_type_bits >> strip_tac >>
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      vyperASTTheory.expr_type_def]
QED

(* expr_sim_pre_augassign under expr_body_pre: e may make internal calls. *)
Theorem expr_body_pre_augassign:
  !cenv cx env ty id bop e es.
    expr_body_pre cenv cx env e es /\ FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) ==>
    expr_body_pre cenv cx env (Builtin ty (Bop bop) [Name ty id; e]) es
Proof
  rpt strip_tac >>
  drule expr_body_pre_var_types_well_formed >>
  disch_then drule >> strip_tac >>
  drule well_formed_type_bits >> strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      vyperASTTheory.expr_type_def]
QED

Theorem name_sim_case[local]:
  !nocalls ctx func cenv cx ann id.
    expr_sim_case nocalls ctx func cenv cx (Name ann id)
Proof
  rw[expr_sim_case_def] >> irule expr_sim_ok_apply >>
  simp[compile_name_sim, expr_sim_pre_body, int_calls_expr_def] >>
  metis_tac[]
QED

(* x op e simulates where e does, with or without internal calls. *)
Theorem augassign_bop_case:
  !nocalls ctx func cenv cx ty id bop e.
    expr_sim_case nocalls ctx func cenv cx e /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ty (Bop bop) [Name ty id; e])
Proof
  rpt strip_tac >>
  drule_all well_typed_binop_augassign_word >> strip_tac >>
  irule compile_bop_word_case >>
  simp[name_sim_case, vyperASTTheory.expr_type_def]
QED

Theorem augassign_bop_sim:
  !ctx func cenv cx env ty id bop e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    expr_sim ctx func cenv cx ty (Builtin ty (Bop bop) [Name ty id; e]) es
Proof
  rpt strip_tac >> irule expr_sim_ok_apply >>
  reverse conj_tac
  >- (qexists_tac `env` >> irule expr_sim_pre_augassign >> simp[]) >>
  drule_all well_typed_binop_augassign_word >> strip_tac >>
  irule compile_bop_word_sim >>
  simp[compile_name_sim, vyperASTTheory.expr_type_def]
QED

(* ===== The statement ===== *)

(* A local the typing environment knows: it is held through a pointer
   variable, it is in scope, and its entry's type is its type's. *)
Theorem expr_sim_inv_local:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (?entry. lookup_scopes id es.scopes = SOME entry) /\
    !entry. lookup_scopes id es.scopes = SOME entry ==>
            evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  rpt gen_tac >> strip_tac >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
  qpat_x_assum `!id ty. _ ==> IS_SOME _` drule >>
  qpat_x_assum `!id ty. _ ==> ?p sz. _` drule >>
  simp[optionTheory.IS_SOME_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ _ ==> _` drule_all >> simp[]
QED

(* x op= e on a word local x, for every outcome, given e's expr_sim_case
   (so e may make internal calls unless nocalls): x op e's errors exit,
   the checked operators' aborts among them, and on a value the MSTORE
   writes it to x's region. *)
(* Why it holds.  The source reads x, evaluates e and runs the operator,
   which is how x op e evaluates (eval_augassign_local_bop), and the code
   is x op e's lowering then the MSTORE (augassign_local_code_bop); x op e
   meets expr_body_pre where e does, so its expr_sim is compile_bop_word_case's.
   The scopes at the write hold x at the type ty evaluates to
   (expr_sim_inv at the state after e), so the result's typed word is the
   word the store lays out at x's type (store_lays_out_word_value). *)
Theorem compile_augassign_local_case:
  !nocalls ctx func cx lctx RetQ cenv ty0 env ty id bop e es res es'.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
    FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e)) es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  drule_all augassign_local_code_bop >> strip_tac >>
  rename1 `emit_void MSTORE [Var p; res_op] s3 = _` >>
  drule_all eval_augassign_local_bop >>
  disch_then (qx_choosel_then [`r`, `es1`] strip_assume_tac) >>
  `expr_body_pre cenv cx env (Builtin ty (Bop bop) [Name ty id; e]) es` by
    (irule expr_body_pre_augassign >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx
     (Builtin ty (Bop bop) [Name ty id; e])` by
    (irule augassign_bop_case >> simp[]) >>
  `expr_sim ctx func cenv cx ty (Builtin ty (Bop bop) [Name ty id; e]) es` by
    (irule expr_sim_case_apply >> simp[int_calls_expr_def] >> metis_tac[]) >>
  qspecl_then [`cenv`, `cx`, `env`, `Builtin ty (Bop bop) [Name ty id; e]`,
               `es`, `r`, `es1`] mp_tac expr_body_pre_word_result >>
  impl_tac >- simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `Builtin ty (Bop bop) [Name ty id; e]`,
               `es`, `ty`, `sa`, `res_op`, `s3`] mp_tac
    expr_body_pre_lower_value_word_shape >>
  impl_tac >- simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  Cases_on `r`
  >~ [`INR ex`]
  >- (gvs[] >> drule_all expr_sim_error_run >> strip_tac >>
      drule exit_result_not_error >> strip_tac >>
      disj2_tac >> simp[stmt_exit_def] >> metis_tac[]) >>
  fs[vyperASTTheory.expr_type_def] >>
  rename1 `write_place cx (MemoryPlace id []) v es1 = (res, es')` >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all write_place_local >> strip_tac >>
  rename1 `find_containing_scope id es1.scopes = SOME (pre, env1, entry1, rest)` >>
  `lookup_scopes id es1.scopes = SOME entry1` by
    metis_tac[find_containing_scope_lookup] >>
  `evaluate_type (get_tenv cx) ty = SOME entry1.type` by
    metis_tac[expr_sim_inv_local] >>
  gvs[vyperASTTheory.expr_type_def] >>
  (* x op e, from s0 to its end u *)
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s3`, `res_op`, `INL v`, `es1`, `s0`]
                mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  rename1 `expr_post func cenv cx _ es sa s3 s0 es1 v res_op u` >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def, vyperASTTheory.expr_type_def] >>
  strip_tac >>
  `eval_operand res_op u = SOME (typed_val_to_w256 entry1.type v)` by
    gvs[] >>
  `store_lays_out entry1.type entry1.type v` by
    (irule store_lays_out_word_value >>
     metis_tac[word_value_type_memory_size]) >>
  drule_all assign_local_store_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  disj1_tac >> qexists_tac `t` >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
           fresh_id_def, emit_def, comp_return_def] >>
      strip_tac >> Cases_on `s3.cs_current_insts` >>
      gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
          venomInstTheory.mk_inst_def, is_terminator_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspecl_then [`fuel`, `run_from fuel ctx func t`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func u <> Error e) ==> _`
    (qspec_then `fuel'` mp_tac) >>
  simp[] >> metis_tac[]
QED

(* compile_augassign_local_case for an operand with no internal call. *)
Theorem compile_augassign_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty0 env ty id bop e es res es'.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e)) es res es'
Proof
  rpt strip_tac >> irule compile_augassign_local_case >>
  fs[expr_sim_pre_body, expr_sim_ok_case] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `T` >> simp[]
QED

(* Integrity gate: the source and code sides and the store carry no
   admission; the statement itself inherits exprSimBinopFrag's (#572). *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "AUGASSIGN_AUDIT OK\n"
     else raise Fail "augmented assignment inherited admission"
  end) [eval_augassign_local_bop, augassign_local_code_bop,
        expr_sim_pre_augassign, expr_body_pre_augassign, expr_sim_inv_local, assign_local_store_run];
