(*
 * Statement simulation: Assign to a local (#637)
 *
 * x = e for a local x already in scope, held in memory at its pointer.
 * The source evaluates e, checks x is in scope, reads e's value and
 * writes it into the scope that holds x (write_place on MemoryPlace x []).
 * The lowering evaluates e, takes x's pointer (no code), unwraps the value
 * and stores it there with compile_assign_value.
 *
 * TOP-LEVEL:
 *   is_word_type_no_length_word     — a word type has no length word
 *   eval_assign_local               — the source run: the forced value of
 *                                     e, then write_place on x
 *   eval_assign_local_error         — an error of x = e is e's
 *   compile_assign_local_stmt_frag  — x = e for a word-typed local x and a
 *                                     word-typed e, every outcome
 *)

Theory stmtSimAssign
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclStore
  stmtSimDecl stmtSimAssignStore
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperLookup vyperExprNoControl
  venomInst venomState
Libs
  monadsyntax

Theorem is_word_type_no_length_word:
  !t. is_word_type t ==> ~has_length_word t
Proof
  ho_match_mp_tac is_word_type_ind >>
  simp[is_word_type_def, has_length_word_def, is_bytestring_type_def]
QED

(* x = e, unless it fails with a type error: e's forced value r, and on an
   error that error, on a value v the write of v into x. *)
Theorem eval_assign_local:
  !cx id e es res es'.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1 /\ no_control_exc ex) /\
      (!v. r = INL v ==> write_place cx (MemoryPlace id []) v es1 = (res, es'))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[]
  >- (rename1 `eval_expr cx e es = (INL pv, es1)` >>
      simp[Once evaluate_def, bind_def] >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, return_def, raise_def] >>
      Cases_on `lookup_scopes id es1.scopes` >>
      simp[raise_def, return_def, get_place_def]
      >- (strip_tac >> gvs[]) >>
      Cases_on `read_result cx pv es1` >>
      rename1 `read_result cx pv es1 = (r2, es2)` >>
      Cases_on `r2` >> simp[] >> strip_tac >> gvs[] >>
      drule read_result_no_control >> simp[]) >>
  strip_tac >> gvs[] >>
  imp_res_tac (cj 1 eval_expr_no_control) >> simp[]
QED

Theorem eval_assign_local_error:
  !cx id e es ex es' lctx.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (INR ex, es') /\
    stmt_res_ok lctx (INR ex) ==>
    (do result <- eval_expr cx e; read_result cx result od) es = (INR ex, es') /\
    expr_res_ok (INR ex : value + exception)
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_assign_local >> impl_tac >- gvs[stmt_res_ok_def] >>
  strip_tac >> Cases_on `r` >> gvs[]
  >- (drule write_place_local >> gvs[stmt_res_ok_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

(* The code of x = e for a word-typed local x and word-typed e: e's value,
   then one MSTORE at x's pointer. *)
Theorem assign_local_word_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) /\ fn_has_code sa sf func ==>
    c = cenv /\
    ?sb op.
      lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
      emit_void MSTORE [Var p; op] sb = ((), sf) /\
      cs_extends sa sb /\ cs_extends sb sf /\
      fn_has_code sa sb func /\ fn_has_code sb sf func
Proof
  rpt gen_tac >> strip_tac >>
  `~has_length_word (expr_type e)` by
    metis_tac[is_word_type_no_length_word] >>
  drule compile_get_target_ptr_local >> strip_tac >>
  `?st2 src_vv sb op.
     compile_expr cenv (expr_type e) e sa = (src_vv, st2) /\
     unwrap_value cenv src_vv st2 = (op, sb) /\
     emit_void MSTORE [Var p; op] sb = ((), sf) /\ c = cenv` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac (srw_ss())
       [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
        compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, LET_THM] >>
     Cases_on `compile_expr cenv (expr_type e) e sa` >>
     rename1 `compile_expr _ _ _ _ = (src_vv, st2)` >>
     Cases_on `unwrap_value cenv src_vv st2` >>
     rename1 `unwrap_value _ _ _ = (op, sb)` >>
     Cases_on `emit_void MSTORE [Var p; op] sb` >>
     rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
     simp[] >> strip_tac >> gvs[]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op, sb)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sb` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `cs_extends sb sf` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sf func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[]
QED

(* On a value: e's fragment reaches the MSTORE in expr_post, at the scopes
   e leaves, and the MSTORE writes x there. *)
Theorem assign_local_word_success_run:
  !ctx func cenv cx id e es es' etv sa sb sf op p sz s0.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (INL (), es') /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       store_lays_out etv entry.type v) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_assign_local >> simp[] >> strip_tac >>
  Cases_on `r` >> gvs[] >>
  rename1 `write_place cx (MemoryPlace id []) v es1 = (INL (), es')` >>
  drule write_place_local >> simp[] >> strip_tac >> gvs[] >>
  `lookup_scopes id es1.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out etv entry.type v` by metis_tac[] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  qpat_x_assum `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op s1 = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  drule_all assign_local_store_run >>
  strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

(* x = e for a local x of a word type and e of a word type, for every
   outcome: e's errors exit, and on a value it is stored at x's pointer.
   store_lays_out says the stored word is how x's type lays e's value out:
   a word_value, or an address or bytesN of x's type
   (store_lays_out_word_value, store_lays_out_typed). *)
Theorem compile_assign_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es res es' p sz vtyp etv.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       store_lays_out etv entry.type v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_word_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op, sB)` >> gvs[] >>
  Cases_on `res`
  >- (rename1 `eval_stmt _ _ _ = (INL u, _)` >> Cases_on `u` >>
      drule_all assign_local_word_success_run >> strip_tac >>
      disj1_tac >> qexistsl [`t`, `cenv`] >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
           fresh_id_def, emit_def, comp_return_def] >>
      strip_tac >> Cases_on `sB.cs_current_insts` >>
      gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
          venomInstTheory.mk_inst_def, is_terminator_def]) >>
  rename1 `eval_stmt _ _ _ = (INR y, _)` >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INR y, es') /\
   expr_res_ok (INR y : value + exception)` by
    (drule eval_assign_local_error >> disch_then drule >> simp[]) >>
  drule_all expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED
