(*
 * Statement simulation: return from an internal function (#637, #638)
 *
 * The return statement over stmt_frag (stmtSim), for an internal function
 * that returns one word on the stack: the value's fragment, then RET with
 * the value and the return PC, which ret_pc_ok in stmt_frag keeps defined.
 *
 * TOP-LEVEL:
 *   intret_q                     — the RetQ of such a function: an IntRet
 *                                  in result_rel with the returned value
 *   compile_return_word_int_frag — return e, for every outcome of e
 *)

Theory stmtSimReturn
Ancestors
  list fragExec exprSim stmtSim
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv
  vyperInterpreter vyperState vyperExprNoControl vyperStatePreservation
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* An internal function's return, related to the source's as result_rel
   (compileEnv) does: an IntRet whose values match v, adopting no free
   memory pointer, with state_rel at the source state without its scopes.
   intret_vals_match checks the values only for stack returns
   (ce_returns_count = 1 here); a memory return's are not on the stack. *)
Definition intret_q_def:
  intret_q func cenv cx ret_tv v (es : evaluation_state) r <=>
    ?ir s. r = IntRet ir s /\
           result_rel func ret_tv cenv cx (INR (ReturnException v), es) r
End

(* No scope holds a local once the frame is left. *)
Theorem state_rel_scopes_nil:
  !func cenv cx es s.
    state_rel func cenv cx es s ==>
    state_rel func cenv cx (es with scopes := []) s
Proof
  rw[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def, local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

(* Reassociate source return evaluation at the forced-value boundary. *)
Theorem eval_return_forced[local]:
  !cx e es.
    eval_stmt cx (Return (SOME e)) es =
    bind (do raw <- eval_expr cx e; read_result cx raw od)
      (\v. raise (ReturnException v)) es
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,est)` >>
  Cases_on `raw` >> simp[]
QED

(* return e in an internal function whose result, a word, goes back on the
   stack (ce_returns_count = 1, no return buffer): e's fragment, whose
   errors exit, then RET [e's operand; the return PC]. *)
Theorem compile_return_word_int_frag:
  !ctx func cx lctx cenv ty e es res es' rpc rsz ret_tv.
    eval_stmt cx (Return (SOME e)) es = (res, es') /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
    expr_type e = ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ret_tv /\
    expr_sim ctx func cenv cx ty e es /\
    (!sa op sb. lower_value compile_expr cenv ty e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx ty (Return (SOME e))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       compile_internal_return_from_env_def, compile_internal_return_def] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  simp[] >>
  Cases_on `emit_inst RET [op; Var rpc] [] s1` >> rename1 `_ = (u, s2)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends sa s1` by metis_tac[] >>
  `cs_extends s1 s2` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split] >>
  qspecl_then [`s1`, `s2`, `func`, `[mk_inst s1.cs_next_id RET [op; Var rpc] []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (LENGTH s1.cs_current_insts) =
     SOME (mk_inst s1.cs_next_id RET [op; Var rpc] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  (* the source *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[eval_return_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[Once bind_def, raise_def] >> strip_tac >>
  `expr_res_ok r1` by (
    Cases_on `r1`
    >- gvs[expr_res_ok_def] >>
    qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
    simp[bind_def] >> Cases_on `eval_expr cx e es` >>
    rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
    imp_res_tac read_result_no_control >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (
    (* the value: RET with it and the return PC *)
    gvs[expr_post_def, return_def] >>
    qpat_x_assum `expr_val_rel _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
    rename1 `eval_operand op sv = SOME w` >>
    `w = typed_val_to_w256 ret_tv v` by
      (qpat_x_assum `!tv. _` (qspec_then `ret_tv` mp_tac) >> simp[]) >>
    `?pc. lookup_var rpc sv = SOME pc` by
      (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >>
       strip_tac >> qexists_tac `w'` >> first_x_assum irule >> simp[]) >>
    `run_from 0 ctx func sv =
     IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |> sv` by
      simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
           venomInstTheory.mk_inst_def, step_inst_base_def,
           eval_operands_def, eval_operand_def] >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
      (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
    `state_rel func cenv cx (es' with scopes := []) sv` by
      (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
    qexists_tac `fuel'` >>
    simp[exit_result_def, stmt_exit_def, intret_q_def, result_rel_def,
         intret_vals_match_def]) >>
  qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

(* Integrity gate for the forced return boundary and RET consumer. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RETURN_FORCE_AUDIT OK\n"
     else raise Fail "forced return inherited admission"
  end) [eval_return_forced, state_rel_scopes_nil, compile_return_word_int_frag];
