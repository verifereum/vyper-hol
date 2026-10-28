(*
 * Statement simulation: return from an internal function (#637, #638)
 *
 * The return statement over stmt_frag (stmtSim), for an internal function
 * that returns one word on the stack: the value's fragment, the optional
 * guard release, then RET with the value and the defined return PC.
 *
 * TOP-LEVEL:
 *   return_unlock_state          — exact VM epilogue effect (all guards)
 *   intret_q                     — exact singleton IntRet after that effect
 *   intret_q_source_epilogue      — source transient-epilogue bridge
 *   return_unlock_changes_source_relation — old-contract counterevidence
 *   compile_return_word_int_frag — return e, for every outcome of e
 * Helpers: code shape, operand preservation, execution and scope/index frames.
 *)

Theory stmtSimReturn
Ancestors
  list rich_list pair fragExec exprSim stmtSim
  internalReturnLockProps loweringHalt context nonreentrantEquiv localPtrsProps
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv
  vyperInterpreter vyperState vyperExprNoControl
  venomExecSemantics venomInst venomState

(* The statement-level source Return only raises ReturnException.  Its
   function epilogue releases the guard later; compiled RET releases it now.
   Record that exact effect, including the one executed store instruction.
   Persistent guards use the legacy unlocked value 3, transient guards 0. *)
Definition return_unlock_state_def:
  return_unlock_state cenv s =
    let (nr,key,ut,iv) = cenv.ce_nonreentrant in
      if nr /\ ~iv then
        (if ut then tstore (n2w key) 0w s else sstore (n2w key) 3w s)
          with vs_inst_idx := SUC s.vs_inst_idx
      else s
End

Definition return_unlock_insts_def:
  return_unlock_insts cenv id =
    let (nr,key,ut,iv) = cenv.ce_nonreentrant in
      if nr /\ ~iv then
        [mk_inst id (if ut then TSTORE else SSTORE)
           [Lit (n2w key); Lit (if ut then 0w else 3w)] []]
      else []
End

(* Exact epilogue-aware RetQ: result_rel holds BEFORE the unlock, and the
   returned VM state is precisely its optional unlock, not an arbitrary
   state with selected effects equal.  No guard cases are excluded. *)
Definition intret_q_def:
  intret_q func cenv cx ret_tv v (es : evaluation_state) r <=>
    ?ir s. r = IntRet ir (return_unlock_state cenv s) /\
           ir.iret_values = [typed_val_to_w256 ret_tv v] /\
           result_rel func ret_tv cenv cx (INR (ReturnException v), es)
             (IntRet ir s)
End

Theorem compile_internal_word_return_code:
  cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  compile_internal_return_from_env cenv ty src_ty op rpc st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET [op;rpc] []]
Proof
  rpt strip_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_internal_return_from_env_def, compile_internal_return_def,
       compile_return_unlock_def, compile_nonreentrant_unlock_def,
       return_unlock_insts_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_void_def, emit_inst_def, fresh_id_def, emit_def]
QED

Theorem eval_operand_return_index[local,simp]:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* Reuse the external-return unlock frame for transient guards; extend it
   to persistent guards without imposing its transient-only precondition. *)
Theorem eval_operand_return_unlock:
  !cenv s op.
    eval_operand op (return_unlock_state cenv s) = eval_operand op s
Proof
  rpt gen_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info2`
  >- (qspecl_then
        [`info0`, `info3`, `info1`,
         `if info0 /\ ~info3 then SUC s.vs_inst_idx else s.vs_inst_idx`,
         `s`, `return_unlock_state cenv s`] mp_tac optional_unlock_state >>
      impl_tac
      >- (Cases_on `info0` >> Cases_on `info3` >>
          simp[return_unlock_state_def]) >>
      simp[]) >>
  Cases_on `info0` >> Cases_on `info3` >>
  simp[return_unlock_state_def]
QED

Theorem step_internal_word_return[local]:
  !id op rpc s.
    step_inst_base (mk_inst id RET [op;rpc] []) s =
      case eval_operand op s of
        NONE => Error "ret: undefined return value"
      | SOME w => case eval_operand rpc s of
          NONE => Error "ret: undefined return value"
        | SOME pc => IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |> s
Proof
  rpt gen_tac >> simp[step_inst_base_def, eval_operands_def] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand rpc s` >> simp[]
QED

Theorem step_persistent_return_unlock[local]:
  !id key s.
    step_inst_base (mk_inst id SSTORE [Lit key; Lit 3w] []) s =
      OK (sstore key 3w s)
Proof
  simp[step_inst_base_def, exec_write2_def, eval_operand_def]
QED

(* Lift the exact optional-store/RET sequence into the containing function. *)
Theorem internal_word_return_run:
  !cenv st st' func ctx s op rpc w pc.
  fn_has_code st st' func /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET [op;rpc] []] /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME w /\ eval_operand rpc s = SOME pc ==>
  run_from 0 ctx func s =
    IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
      (return_unlock_state cenv s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `st'.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    assume_tac (Q.SPEC `0` th) >> assume_tac (Q.SPEC `1` th)) >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[return_unlock_insts_def, return_unlock_state_def] >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
       mk_inst_def, is_terminator_def,
       SRULE [mk_inst_def] step_internal_word_return,
       SRULE [mk_inst_def] step_persistent_return_unlock,
       SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit,
       eval_operand_def] >>
  simp[Once exec_block_def, step_inst_non_invoke, mk_inst_def,
       SRULE [mk_inst_def] step_internal_word_return, arithmeticTheory.ADD1]
QED

(* No scope holds a local once the frame is left. *)
Theorem state_rel_scopes_nil:
  !func cenv cx es s.
    state_rel func cenv cx es s ==>
    state_rel func cenv cx (es with scopes := []) s
Proof
  rw[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def, local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

Theorem state_rel_return_index[local,simp]:
  !func cenv cx es s n.
    state_rel func cenv cx es (s with vs_inst_idx := n) <=>
    state_rel func cenv cx es s
Proof
  simp[state_rel_def, local_ptrs_rel_inst_idx, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def,
       contract_storage_def, contract_transient_def]
QED

(* For the source's transient guard representation, RetQ implies ordinary
   result_rel after exactly the source function epilogue.  Persistent guards
   remain covered by the main exact VM contract; the source release primitive
   only writes transient storage, so no persistent/source parity is claimed. *)
Theorem intret_q_source_epilogue:
  !func cenv cx ret_tv v es r nr key iv.
    cenv.ce_nonreentrant = (nr,key,T,iv) /\
    intret_q func cenv cx ret_tv v es r ==>
    ?es'.
      (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target key
       else vyperState$return ()) es = (INL (),es') /\
      result_rel func ret_tv cenv cx (INR (ReturnException v),es') r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `intret_q _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intret_q_def]) >>
  Cases_on `nr` >> Cases_on `iv` >>
  gvs[return_unlock_state_def, result_rel_def, vyperStateTheory.return_def,
      release_nonreentrant_lock_execution] >>
  irule state_rel_transient_update >> simp[]
QED

(* Evidence that the old unchanged-source contract is genuinely false for
   a held transient guard, rather than merely difficult for metis. *)
Theorem return_unlock_changes_source_relation:
  !func cenv cx es s key.
    cenv.ce_nonreentrant = (T,key,T,F) /\
    state_rel func cenv cx es s /\ tload (n2w key) s <> 0w ==>
    ~state_rel func cenv cx es (return_unlock_state cenv s)
Proof
  rpt gen_tac >> strip_tac >>
  simp[return_unlock_state_def] >> strip_tac >>
  qpat_assum `state_rel _ _ _ _ s`
    (mp_tac o GEN_ALL o MATCH_MP state_rel_transient_lookup) >>
  disch_then (qspec_then `n2w key` assume_tac) >>
  qpat_x_assum `state_rel _ _ _ _ (tstore _ _ _)`
    (mp_tac o GEN_ALL o MATCH_MP state_rel_transient_lookup) >>
  disch_then (qspec_then `n2w key` mp_tac) >> simp[]
QED

(* return e in an internal function whose result, a word, goes back on the
   stack (ce_returns_count = 1, no return buffer): e's fragment, whose
   errors exit, the exact optional unlock, then RET [operand; return PC]. *)
Theorem compile_return_word_int_frag:
  !ctx func cx lctx cenv ty e es res es' rpc rsz ret_tv.
    eval_stmt cx (Return (SOME e)) es = (res, es') /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
    expr_type e = ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ret_tv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==> ?v. tv = Value v) /\
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
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  simp[] >>
  Cases_on `compile_internal_return_from_env cenv ty (expr_type e) op (Var rpc) s1` >>
  rename1 `_ = (u, s2)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_internal_word_return_code >> strip_tac >>
  `cs_extends sa s1` by metis_tac[] >>
  `cs_extends s1 s2` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    (irule fn_has_code_split >> simp[]) >>
  (* the source *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  strip_tac >>
  `expr_res_ok r1` by (
    Cases_on `r1`
    >- gvs[expr_res_ok_def] >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[] >> rename1 `no_control_exc y` >> Cases_on `y` >> gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (
    (* the value: RET with it and the return PC *)
    gvs[expr_post_def, materialise_def, return_def] >>
    qpat_x_assum `expr_val_rel _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
    rename1 `eval_operand op sv = SOME w` >>
    `w = typed_val_to_w256 ret_tv v` by
      (qpat_x_assum `!tv. _` (qspec_then `ret_tv` mp_tac) >> simp[]) >>
    `?pc. lookup_var rpc sv = SOME pc` by
      (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >>
       strip_tac >> rename1 `lookup_var rpc s0 = SOME old_pc` >>
       qexists_tac `old_pc` >> first_x_assum irule >> simp[]) >>
    `run_from 0 ctx func sv =
     IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
       (return_unlock_state cenv sv)` by
      (irule internal_word_return_run >>
       qexistsl_tac [`op`, `pc`, `Var rpc`, `s1`, `s2`] >>
       simp[eval_operand_def]) >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
      (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
    `state_rel func cenv cx (es' with scopes := []) sv` by
      (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
    qexists_tac `fuel'` >>
    simp[exit_result_def, stmt_exit_def, intret_q_def] >>
    disj2_tac >> qexists_tac `sv` >>
    simp[result_rel_def, intret_vals_match_def]) >>
  qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >> disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:toplevel_value``]
                      expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("internal return simulation is not kernel closed: " ^ name)
  end) (DB.thms "stmtSimReturn");
