(*
 * Statement simulation for every outcome (#637, core)
 *
 * The judgment stmt_frag: the code of a statement or a statement list, run
 * from stmt_state_rel at the source state where it is evaluated, ends the
 * way the source's outcome says:
 *   - normal completion: at the end of the code, in a block left open;
 *   - break / continue: at the start of the enclosing loop's exit or
 *     increment block (the labels of its loop context);
 *   - in each of these, stmt_state_rel at the source state after it, the
 *     variables handed out before the code and the allocations made before
 *     it kept, and every non-Error result from there a result from the
 *     start;
 *   - an error other than a type error, or an assertion: an exit as
 *     expr_exit allows (an Abort; Revert_abort for an assertion, or
 *     ExHalt_abort for "UNREACHABLE");
 *   - a return: an exit the caller's RetQ accepts.  RetQ is the frame's:
 *     intret_q (stmtSimReturn) for an internal function (#638), the halt of
 *     the return sequence for an external one (#640).
 * stmt_state_rel speaks of the current frame's locals and variables, so an
 * internal-function body reuses the judgment with its own RetQ.  The
 * allocation frontier vs_alloca_next is the current frame's: a callee
 * allocates above its caller's, and INVOKE gives the caller its frontier
 * back (merge_callee_state), so alloca_room survives a call.
 *
 * A list's declarations extend the compile environment its later
 * statements see; the relation at a list's end is at the extended cenv',
 * which differs from cenv only on names in the innermost scope
 * (cenv_top_ext).  If and For pop that scope, and with it go back to their
 * own cenv (stmt_state_rel_pop_top_ext).
 *
 * TOP-LEVEL:
 *   stmts_env, stmt_env — compile_stmts, and a statement with its
 *                         declaration, returning the compile environment
 *   stmt_res_ok, stmt_exit, stmt_lands, cenv_top_ext, ret_pc_ok, stmt_frag
 *   stmt_frag_nil, stmt_frag_cons, stmt_frag_cons_env — statement lists
 *   stmt_state_rel_pop_top_ext     — leaving a scope
 *   compile_pass_frag, compile_break_frag, compile_continue_frag
 *   compile_expr_stmt_frag, compile_expr_stmt_frag_ok
 *                                  — an expression statement
 *   declare_local_ptr              — a local declared through a pointer
 *
 * The other statements: If, Raise and Assert in stmtSimIf; For over a
 * range with literal ends in stmtSimFor (its blocks in stmtSimForParts,
 * the loop in stmtSimForLoop), and with other ends in stmtSimForRange;
 * Return of a word or of a tuple of words from an internal function in
 * stmtSimReturn; AnnAssign of a local held in one word (a word_value, an
 * address, a bytesN) in stmtSimDecl, of a memory-backed local whose value
 * is lowered at the declared type, or is a bytestring of another bound, in
 * stmtSimDeclMem, and of a local initialised with the empty value in
 * stmtSimDeclEmpty; Raise and Assert
 * with a string literal reason in stmtSimReason, with another reason held on
 * the stack or in memory in stmtSimReasonExpr, and with a reason read from
 * storage or transient storage in stmtSimReasonStorage; AugAssign to a
 * local held in one word in stmtSimAugAssign; Assign to a local held in one
 * word in stmtSimAssign, to a memory-backed local in stmtSimAssignMem, to
 * a tuple of locals each held in one word in stmtSimAssignTuple or with
 * memory-backed elements in stmtSimAssignTupleMem, and to a storage or
 * transient variable held in one word in stmtSimAssignStorage.  Not covered
 * yet: Assign to an aggregate storage or transient variable, Assign and
 * AugAssign to other targets (#550), Append and For over an array (#559),
 * Log (#570), memory-backed declarations whose initialisation changes the
 * value's layout (compile_store_memory_typed), reasons held in code
 * (immutables) or calldata, and memory-backed returns.
 *)

Theory stmtSim
Ancestors
  stmtSimDefs stmtSimZero stmtSimPass stmtSimProps stmtSimSeq
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState venomMemDefs integer_word
Libs
  monadsyntax intLib

(* ===== The judgment ===== *)

(* compile_stmts, returning the compile environment after the list's
   declarations. *)

(* A statement with its declaration, as compile_stmts compiles it,
   returning the compile environment after the declaration. *)

(* The source outcomes the judgment speaks of: normal completion, a break
   or continue inside a loop, a return, an error other than a type error,
   or an assertion.  Type errors, and a break or continue outside a loop,
   are left out. *)

(* The exits a source outcome allows: an expression's (expr_exit), and for
   a return of v whatever RetQ accepts of v and the source state after it.
   RetQ sees that state without its scopes: the locals are the frame's,
   and the scopes that If and For pop on the way out do not matter to the
   caller. *)

(* A normal finish, a break and a continue are not exits. *)

(* Where the code of a fragment from sa to sb leaves off on an outcome
   that does not exit: its end, or the start of the loop's exit or
   increment block. *)

(* cenv' is cenv with bindings changed only for names of locals (unbound
   or held through a pointer on both sides) that the scopes below the
   innermost do not hold: the declarations of the innermost scope, and
   names out of scope.  Leaving the innermost scope goes back to cenv
   (stmt_state_rel_pop_top_ext).  Of the other fields only ce_var_type and
   ce_dynarray_capacity may differ, for any name. *)

(* The return PC of an internal function's frame (ce_return_pc, the
   variable RETPC_PARAM binds at the function's entry) is defined, and it
   was handed out before sa, so stmt_frag's frame on old variables keeps
   it.  RET reads it; an external function has none. *)

(* The code m (a statement with its declaration, or a statement list),
   compiled in cenv from sa to sb under the code premises of the statement
   lemmas, run in func from a state related at es where the source's
   outcome is res, ending in es'.  m returns the compile environment after
   its declarations, cenv'.  On normal completion the relation at the end
   is at cenv', and the block is left open, so a list goes on with its next
   statement in cenv'.  Where the code leaves off otherwise (a break or a
   continue) it is at some cenv'' that extends cenv in the innermost scope:
   cenv' may hold declarations the source never ran. *)

(* An entry-frame version of stmt_frag.  Frame is a premise on the actual
   target entry state, not an assertion that every related state has a
   suitable layout.  In particular stmt_state_rel alone does not reserve
   constructor immutable memory against ALLOCA.  The postcondition is the
   same as stmt_frag; no preservation of an arbitrary Frame is promised. *)

(* Both fresh and replayed ALLOCAs must start above the reserved prefix.
   A frontier bound alone is insufficient for a replayed allocation. *)



(* Locals live outside the module table, so a prefix bound transports to
   the declaration environment. *)


(* The return PC stays defined and unassigned as the code goes on, where
   the variables handed out before it keep their values. *)




(* A terminator at the end of the code that jumps to lbl: every non-Error
   result after the jump is a result from before it. *)

(* ===== pass, break, continue ===== *)


(* A break or continue in a loop jumps to the loop's exit or increment
   block. *)
Theorem compile_break_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break) es (INR BreakException) es
Proof
  rw[stmt_frag_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  disj1_tac >> qexistsl_tac [`jump_to ex s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  qspecl_then [`ctx`, `func`, `sa`, `sj`, `s0`,
               `mk_inst sa.cs_next_id JMP [Label ex] []`, `ex`]
    mp_tac run_from_jump_end >>
  impl_tac
  >- simp[venomInstTheory.mk_inst_def, is_terminator_def, step_jmp_behavior] >>
  strip_tac >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to] >>
  rpt conj_tac >> TRY (simp[jump_to_def, lookup_var_def] >> NO_TAC) >>
  rpt strip_tac >> metis_tac[]
QED

Theorem compile_continue_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue) es (INR ContinueException)
      es
Proof
  rw[stmt_frag_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  disj1_tac >> qexistsl_tac [`jump_to inc s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  qspecl_then [`ctx`, `func`, `sa`, `sj`, `s0`,
               `mk_inst sa.cs_next_id JMP [Label inc] []`, `inc`]
    mp_tac run_from_jump_end >>
  impl_tac
  >- simp[venomInstTheory.mk_inst_def, is_terminator_def, step_jmp_behavior] >>
  strip_tac >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to] >>
  rpt conj_tac >> TRY (simp[jump_to_def, lookup_var_def] >> NO_TAC) >>
  rpt strip_tac >> metis_tac[]
QED

(* ===== Statement lists ===== *)



(* Leaving the innermost scope of a list's extended environment goes back
   to the environment the list started in. *)

(* A declaration keeps the locals' pointers reserved. *)


(* A statement with its declaration keeps the locals' pointers reserved
   and only appends code. *)

(* A statement list: the head's judgment, and on its normal completion the
   tail's judgment in the environment the head's declaration gives, give
   the list's judgment. *)

(* The same, with the tail's judgment in every environment that extends
   cenv in the innermost scope. *)

(* ===== Declarations ===== *)

(* declare_local with locals held through pointers: the local's binding is
   a fresh pointer variable, and nothing else of cenv changes. *)


(* compile_stmts is stmts_env without the environment. *)

(* ===== Expression statements ===== *)

(* expr_exit on an exception does not depend on the result's value type. *)

(* An expression statement: its expression's fragment, which leaves its
   block open where the expression evaluates, run for its effects.  A value
   of any kind but a hashmap is dropped; an expression never raises a
   return, break or continue. *)
Theorem compile_expr_stmt_frag_ok:
  !ctx func cx lctx RetQ cenv ty e es res es'.
    eval_stmt cx (Expr e) es = (res, es') /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e es = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  strip_tac >>
  `expr_vv_res_ok r1` by (
    Cases_on `r1` >> gvs[stmt_res_ok_def] >>
    TRY (rename1 `is_HashMapRef tv` >> Cases_on `tv` >>
         gvs[expr_vv_res_ok_def, expr_res_ok_def] >> NO_TAC) >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[no_control_exc_def, expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `vv`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (gvs[vv_post_def] >> Cases_on `is_HashMapRef tv` >>
      gvs[stmt_res_ok_def] >>
      disj1_tac >> rename1 `stmt_state_rel ctx func cenv cx _ s1` >>
      qexists_tac `s1` >>
      simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >>
  Cases_on `r1` >> gvs[] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

(* The same, with the expression's fragment leaving its block open from
   every start. *)
Theorem compile_expr_stmt_frag:
  !ctx func cx lctx RetQ cenv ty e es res es'.
    eval_stmt cx (Expr e) es = (res, es') /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) /\
                ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      es res es'
Proof
  rpt strip_tac >> irule compile_expr_stmt_frag_ok >> simp[] >>
  metis_tac[]
QED
