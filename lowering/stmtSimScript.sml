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
 *   stmt_frag_nil, stmt_frag_cons — statement lists
 *   stmt_state_rel_pop_top_ext     — leaving a scope
 *   compile_pass_frag, compile_break_frag, compile_continue_frag
 *   compile_expr_stmt_frag         — an expression statement
 *   declare_local_ptr              — a local declared through a pointer
 *
 * The other statements: If, Raise and Assert in stmtSimIf; For over a
 * range with literal ends in stmtSimFor (its blocks in stmtSimForParts,
 * the loop in stmtSimForLoop), and with other ends in stmtSimForRange;
 * Return of a word or of a tuple of words from an internal function in
 * stmtSimReturn; AnnAssign of a local held in one word (a word_value, an
 * address, a bytesN) in stmtSimDecl, and of a memory-backed local whose
 * value is lowered at the declared type in stmtSimDeclMem; Raise and Assert
 * with a string literal reason in stmtSimReason, with another reason held on
 * the stack or in memory in stmtSimReasonExpr, and with a reason read from
 * storage or transient storage in stmtSimReasonStorage; AugAssign to a
 * local held in one word in stmtSimAugAssign; Assign to a local held in one
 * word in stmtSimAssign, to a memory-backed local in stmtSimAssignMem, and
 * to a tuple of locals each held in one word in stmtSimAssignTuple.  Not
 * covered yet: Assign and AugAssign to other targets (#550), Append and For
 * over an array (#559), Log (#570), the other memory-backed declarations
 * (empty values, bytestring literals of another length, initialisations that
 * widen the value), reasons held in code (immutables) or calldata, and
 * memory-backed returns.
 *)

Theory stmtSim
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* ===== The judgment ===== *)

(* compile_stmts, returning the compile environment after the list's
   declarations. *)
Definition stmts_env_def:
  stmts_env cenv lctx ty [] = return cenv /\
  stmts_env cenv lctx ty (s::ss) =
    do cs <- comp_get;
       if block_is_terminated cs then return cenv
       else
         do cenv' <- declare_stmt_local cenv s;
            compile_stmt cenv' lctx ty s;
            stmts_env cenv' lctx ty ss
         od
    od
End

(* A statement with its declaration, as compile_stmts compiles it,
   returning the compile environment after the declaration. *)
Definition stmt_env_def:
  stmt_env cenv lctx ty s =
    do cenv' <- declare_stmt_local cenv s;
       compile_stmt cenv' lctx ty s;
       return cenv'
    od
End

(* The source outcomes the judgment speaks of: normal completion, a break
   or continue inside a loop, a return, an error other than a type error,
   or an assertion.  Type errors, and a break or continue outside a loop,
   are left out. *)
Definition stmt_res_ok_def:
  stmt_res_ok lctx (res : unit + exception) <=>
    res = INL () \/
    (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str)) \/
    (?v. res = INR (ReturnException v)) \/
    ((res = INR BreakException \/ res = INR ContinueException) /\
     ?ex inc. lctx = InLoop ex inc)
End

(* The exits a source outcome allows: an expression's (expr_exit), and for
   a return of v whatever RetQ accepts of v and the source state after it.
   RetQ sees that state without its scopes: the locals are the frame's,
   and the scopes that If and For pop on the way out do not matter to the
   caller. *)
Definition stmt_exit_def:
  stmt_exit RetQ es' (res : unit + exception) r <=>
    expr_exit res r \/
    ?v. res = INR (ReturnException v) /\
        RetQ v (es' with scopes := []) r
End

(* A normal finish, a break and a continue are not exits. *)
Theorem stmt_exit_loop_ctl:
  !RetQ es rr.
    ~stmt_exit RetQ es (INL ()) rr /\
    ~stmt_exit RetQ es (INR BreakException) rr /\
    ~stmt_exit RetQ es (INR ContinueException) rr
Proof
  rw[stmt_exit_def] >> Cases_on `rr` >> simp[expr_exit_def]
QED

(* Where the code of a fragment from sa to sb leaves off on an outcome
   that does not exit: its end, or the start of the loop's exit or
   increment block. *)
Definition stmt_lands_def:
  stmt_lands lctx (sb : compile_state) (res : unit + exception) s <=>
    (res = INL () /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?ex inc. lctx = InLoop ex inc /\ s.vs_inst_idx = 0 /\
       ((res = INR BreakException /\ s.vs_current_bb = ex) \/
        (res = INR ContinueException /\ s.vs_current_bb = inc)))
End

(* cenv' is cenv with bindings changed only for names of locals (unbound
   or held through a pointer on both sides) that the scopes below the
   innermost do not hold: the declarations of the innermost scope, and
   names out of scope.  Leaving the innermost scope goes back to cenv
   (stmt_state_rel_pop_top_ext).  Of the other fields only ce_var_type and
   ce_dynarray_capacity may differ, for any name. *)
Definition cenv_top_ext_def:
  cenv_top_ext cenv cenv' (scopes : (string |-> scope_entry) list) <=>
    cenv' with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
                  ce_dynarray_capacity := cenv.ce_dynarray_capacity |> =
      cenv /\
    !n. FLOOKUP cenv'.ce_vars n <> FLOOKUP cenv.ce_vars n ==>
        (!l. FLOOKUP cenv.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        (!l. FLOOKUP cenv'.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        ?sc rest. scopes = sc :: rest /\ lookup_scopes n rest = NONE
End

(* The return PC of an internal function's frame (ce_return_pc, the
   variable RETPC_PARAM binds at the function's entry) is defined, and it
   was handed out before sa, so stmt_frag's frame on old variables keeps
   it.  RET reads it; an external function has none. *)
Definition ret_pc_ok_def:
  ret_pc_ok cenv sa s <=>
    !x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x /\ ?w. lookup_var x s = SOME w
End

(* The code m (a statement with its declaration, or a statement list),
   compiled in cenv from sa to sb under the code premises of the statement
   lemmas, run in func from a state related at es where the source's
   outcome is res, ending in es'.  m returns the compile environment after
   its declarations, cenv'.  On normal completion the relation at the end
   is at cenv', and the block is left open, so a list goes on with its next
   statement in cenv'.  Where the code leaves off otherwise (a break or a
   continue) it is at some cenv'' that extends cenv in the innermost scope:
   cenv' may hold declarations the source never ran. *)
Definition stmt_frag_def:
  stmt_frag ctx func cx lctx RetQ cenv (m : compile_env compiler) es res es'
  <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      ~block_is_terminated sa /\ stmt_res_ok lctx res /\
      stmt_state_rel func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      (?s cenv''.
         stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
         cenv_top_ext cenv cenv'' es'.scopes /\
         stmt_state_rel func cenv'' cx es' s /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s0 = r) \/
      (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
                stmt_exit RetQ es' res r)
End

(* The return PC stays defined and unassigned as the code goes on, where
   the variables handed out before it keep their values. *)
Theorem ret_pc_ok_frame:
  !cenv cenv' sa sb s s'.
    ret_pc_ok cenv sa s /\ cenv'.ce_return_pc = cenv.ce_return_pc /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x s' = SOME w) ==>
    ret_pc_ok cenv' sb s'
Proof
  rw[ret_pc_ok_def] >> qpat_x_assum `!x sz. _` drule >> strip_tac
  >- (fs[not_fresh_at_def] >> rpt strip_tac >>
      qpat_x_assum `!n. sa.cs_next_var <= n ==> _` (qspec_then `n` mp_tac) >>
      simp[]) >>
  rename1 `lookup_var x s = SOME w` >> qexists_tac `w` >>
  qpat_x_assum `!x w. _ ==> _` irule >> simp[]
QED

Theorem ret_pc_ok_jump_to:
  !cenv sa l s. ret_pc_ok cenv sa (jump_to l s) <=> ret_pc_ok cenv sa s
Proof
  simp[ret_pc_ok_def, lookup_var_def, jump_to_def]
QED

Theorem cenv_top_ext_return_pc:
  !cenv c sc. cenv_top_ext cenv c sc ==> c.ce_return_pc = cenv.ce_return_pc
Proof
  rw[cenv_top_ext_def] >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem cenv_top_ext_refl:
  !cenv scopes. cenv_top_ext cenv cenv scopes
Proof
  rw[cenv_top_ext_def, compileEnvTheory.compile_env_component_equality]
QED

(* A terminator at the end of the code that jumps to lbl: every non-Error
   result after the jump is a result from before it. *)
Theorem run_from_jump_end:
  !ctx func sa sb ss inst lbl.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
    fn_has_code sa sb func /\
    ss.vs_current_bb = sa.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sa.cs_current_insts /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst ss = OK (jump_to lbl ss) /\ ~ss.vs_halted ==>
    !fuel r. run_from fuel ctx func (jump_to lbl ss) = r /\
             (!e. r <> Error e) ==>
             ?fuel'. run_from fuel' ctx func ss = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule run_from_jump_result >> gvs[] >> metis_tac[]
QED

(* ===== pass, break, continue ===== *)

Theorem compile_pass_frag:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass) es
      (INL ()) es
Proof
  rw[stmt_frag_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  disj1_tac >> qexists_tac `s0` >>
  simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]
QED

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

Theorem stmts_env_cons:
  !cenv lctx ty s ss sa.
    ~block_is_terminated sa ==>
    stmts_env cenv lctx ty (s::ss) sa =
    (do c <- stmt_env cenv lctx ty s; stmts_env c lctx ty ss od) sa
Proof
  rw[stmts_env_def, stmt_env_def, comp_bind_def, comp_get_def,
     comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem cenv_top_ext_trans:
  !c1 c2 c3 sc1 sc2.
    cenv_top_ext c1 c2 sc1 /\ cenv_top_ext c2 c3 sc2 /\
    (sc1 = [] <=> sc2 = []) /\ MAP FDOM (TL sc1) = MAP FDOM (TL sc2) ==>
    cenv_top_ext c1 c3 sc2
Proof
  rw[cenv_top_ext_def]
  >- fs[compileEnvTheory.compile_env_component_equality]
  >- (Cases_on `FLOOKUP c2.ce_vars n = FLOOKUP c1.ce_vars n` >> gvs[] >>
      metis_tac[])
  >- (Cases_on `FLOOKUP c3.ce_vars n = FLOOKUP c2.ce_vars n` >> gvs[] >>
      metis_tac[]) >>
  Cases_on `FLOOKUP c3.ce_vars n = FLOOKUP c2.ce_vars n`
  >- (`FLOOKUP c2.ce_vars n <> FLOOKUP c1.ce_vars n` by metis_tac[] >>
      qpat_x_assum `!n. FLOOKUP c2.ce_vars n <> _ ==> _`
        (qspec_then `n` mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> Cases_on `sc2` >> gvs[] >>
      irule lookup_scopes_none_map_fdom >> metis_tac[]) >>
  metis_tac[]
QED

(* Leaving the innermost scope of a list's extended environment goes back
   to the environment the list started in. *)
Theorem stmt_state_rel_pop_top_ext:
  !func cenv cenv' cx es ss sc rest.
    stmt_state_rel func cenv' cx es ss /\ cenv_top_ext cenv cenv' es.scopes /\
    es.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    stmt_state_rel func cenv cx (es with scopes := rest) ss
Proof
  rpt strip_tac >>
  drule_all stmt_state_rel_pop_scope >> strip_tac >>
  irule stmt_state_rel_cenv_cong >>
  qexists_tac `cenv'` >> fs[cenv_top_ext_def] >> rpt conj_tac
  >- (rpt strip_tac >> CCONTR_TAC >>
      qpat_x_assum `!n. FLOOKUP cenv'.ce_vars n <> _ ==> _`
        (qspec_then `n` mp_tac) >>
      simp[] >> rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      qpat_x_assum `!n. FLOOKUP cenv'.ce_vars n <> _ ==> _`
        (qspec_then `n` mp_tac) >>
      simp[] >> metis_tac[])
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      qpat_x_assum `!n. FLOOKUP cenv'.ce_vars n <> _ ==> _`
        (qspec_then `n` mp_tac) >>
      simp[] >> metis_tac[]) >>
  fs[compileEnvTheory.compile_env_component_equality]
QED

(* A declaration keeps the locals' pointers reserved. *)
Theorem declare_stmt_local_reserved:
  !cenv stmt st cenv' st'.
    declare_stmt_local cenv stmt st = (cenv', st') /\
    local_ptrs_reserved cenv st ==>
    local_ptrs_reserved cenv' st' /\ st.cs_next_var <= st'.cs_next_var /\
    cs_extends st st'
Proof
  rpt gen_tac >> Cases_on `stmt` >>
  simp[declare_stmt_local_def, comp_return_def] >>
  TRY (rw[] >> simp[cs_extends_refl] >> NO_TAC) >>
  rw[declare_local_def, comp_bind_def, fresh_var_def, comp_return_def] >>
  gvs[cs_extends_refl] >>
  TRY (irule cs_extends_same_block >> simp[] >> NO_TAC) >>
  TRY (fs[local_ptrs_reserved_def] >> NO_TAC) >>
  fs[local_ptrs_reserved_def, FLOOKUP_UPDATE] >> rw[] >> gvs[AllCaseEqs()] >>
  fs[not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
  FIRST (map (fn (a, b) =>
    first_x_assum drule >> disch_then (qspecl_then [a, b] mp_tac) >>
    simp[] >> TRY (qexists_tac `st.cs_next_var` >> simp[]) >> NO_TAC)
    [(`n1`, `sz1`), (`n2`, `sz2`)])
QED

Theorem stmt_frag_nil:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty []) es
      (INL ()) es
Proof
  rw[stmt_frag_def, stmts_env_def, comp_return_def] >>
  disj1_tac >> qexists_tac `s0` >>
  simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]
QED

(* A statement with its declaration keeps the locals' pointers reserved
   and only appends code. *)
Theorem stmt_env_reserved:
  !cenv lctx ty stmt sa c sb.
    stmt_env cenv lctx ty stmt sa = (c, sb) /\
    (!c'. cs_mono (compile_stmt c' lctx ty stmt)) /\
    local_ptrs_reserved cenv sa ==>
    local_ptrs_reserved c sb /\ cs_extends sa sb /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_all declare_stmt_local_reserved >> strip_tac >>
  fs[cs_mono_def] >> first_x_assum drule >> strip_tac >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> metis_tac[])
  >- metis_tac[cs_extends_trans] >>
  decide_tac
QED

(* A statement list: the head's judgment, and on its normal completion the
   tail's judgment in the environments that extend cenv in the innermost
   scope, give the list's judgment. *)
Theorem stmt_frag_cons:
  !ctx func cx lctx RetQ cenv ty stmt ss es res es'.
    eval_stmts cx (stmt::ss) es = (res, es') /\
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    (!r1 es1. eval_stmt cx stmt es = (r1, es1) ==>
       stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
         es r1 es1) /\
    (!es1 c. eval_stmt cx stmt es = (INL (), es1) /\
             cenv_top_ext cenv c es1.scopes ==>
       stmt_frag ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         es1 res es') ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty (stmt::ss))
      es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  drule_all stmt_env_reserved >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `!c. cs_mono (stmts_env _ _ _ _)` (qspec_then `c` mp_tac) >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  Cases_on `eval_stmt cx stmt es` >> rename1 `_ = (r1, es1)` >>
  qpat_x_assum `!r1 es1. _ ==> stmt_frag _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`r1`, `es1`] mp_tac) >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `r1` >> simp[]
  >- (
    (* the head completes: go on with the tail at c *)
    rename1 `eval_stmt cx stmt es = (INL u, es1)` >> Cases_on `u` >> fs[] >>
    strip_tac >> simp[stmt_frag_def] >>
    disch_then (qspecl_then [`sa`, `sm`, `s0`, `c`] mp_tac) >>
    simp[stmt_res_ok_def, stmt_exit_def] >> strip_tac >>
    qpat_x_assum `stmt_lands _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def]) >>
    rename1 `stmt_state_rel func c cx es1 s1` >>
    `ret_pc_ok c sm s1` by
      (qspecl_then [`cenv`, `c`, `sa`, `sm`, `s0`, `s1`] mp_tac
         ret_pc_ok_frame >>
       impl_tac >- (fs[] >> drule cenv_top_ext_return_pc >> simp[]) >>
       simp[]) >>
    qpat_x_assum `!c'. _ ==> stmt_frag _ _ _ _ _ _ _ _ _ _`
      (qspec_then `c` mp_tac) >>
    simp[stmt_frag_def] >>
    disch_then (qspecl_then [`sm`, `sb`, `s1`, `cenv'`] mp_tac) >>
    simp[] >> strip_tac
    >- (
      disj1_tac >> rename1 `stmt_state_rel func c3 cx es' s2` >>
      qexistsl_tac [`s2`, `c3`] >> simp[] >>
      `cenv_top_ext cenv c3 es'.scopes` by
        (irule cenv_top_ext_trans >> qexistsl_tac [`c`, `es1.scopes`] >>
         simp[] >> drule eval_stmts_preserves_scopes_dom >>
         rw[preserves_scopes_dom_def] >> gvs[]) >>
      `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x s2 = SOME w` by
        (rpt strip_tac >>
         `not_fresh_at sm x` by
           (fs[not_fresh_at_def] >> rw[] >> first_x_assum irule >>
            decide_tac) >>
         `lookup_var x s1 = SOME w` by res_tac >> res_tac) >>
      `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s2.vs_allocas aid = SOME b` by
        (rpt strip_tac >> res_tac >> res_tac) >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s2 <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >> impl_tac >- metis_tac[] >>
      strip_tac >> metis_tac[]) >>
    disj2_tac >>
    `!e. run_from fuel ctx func s1 <> Error e` by
      metis_tac[exit_result_not_error] >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
      drule >> strip_tac >>
    qexists_tac `fuel'` >> asm_rewrite_tac[] >> fs[stmt_exit_def]) >>
  (* the head exits, breaks or continues: the list does the same *)
  rpt strip_tac >> gvs[stmt_frag_def] >>
  first_x_assum (qspecl_then [`sa`, `sm`, `s0`, `c`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> rename1 `stmt_state_rel func c4 cx es' s4` >>
      qexistsl_tac [`s4`, `c4`] >> fs[stmt_lands_def]) >>
  disj2_tac >> qexists_tac `fuel` >> simp[]
QED

(* ===== Declarations ===== *)

(* declare_local with locals held through pointers: the local's binding is
   a fresh pointer variable, and nothing else of cenv changes. *)
Theorem declare_local_ptr:
  !cenv id fty st bc st1.
    declare_local cenv id fty st = (bc, st1) /\ cenv.ce_alloca_locals ==>
    st1 = st with cs_next_var := st.cs_next_var + 1 /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var (STRING #"%" (toString st.cs_next_var)))
                   (type_memory_bytes cenv fty)) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv
Proof
  rw[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def,
     LET_THM] >>
  gvs[FLOOKUP_UPDATE, compileEnvTheory.compile_env_component_equality]
QED

Theorem declare_local_reserved:
  !cenv id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ local_ptrs_reserved cenv st ==>
    local_ptrs_reserved c st1
Proof
  rpt strip_tac >>
  qspecl_then [`cenv`, `AnnAssign id ty (Literal ty (IntL 0))`, `st`, `c`,
               `st1`] mp_tac declare_stmt_local_reserved >>
  simp[declare_stmt_local_def]
QED

(* compile_stmts is stmts_env without the environment. *)
Theorem compile_stmts_env:
  !ss cenv lctx ty st.
    compile_stmts cenv lctx ty ss st = ((), SND (stmts_env cenv lctx ty ss st))
Proof
  Induct
  >- simp[compile_stmt_def, stmts_env_def, comp_return_def] >>
  rpt gen_tac >> simp[Once compile_stmt_def, stmts_env_def] >>
  simp[comp_bind_def, comp_get_def, comp_ignore_bind_def] >> rw[] >>
  simp[comp_return_def, comp_bind_def] >> rpt (pairarg_tac >> gvs[])
QED

(* ===== Expression statements ===== *)

(* expr_exit on an exception does not depend on the result's value type. *)
Theorem expr_exit_INR_type:
  !ex rr. expr_exit (INR ex : 'a + exception) rr =
          expr_exit (INR ex : 'b + exception) rr
Proof
  rpt gen_tac >> Cases_on `rr` >> Cases_on `ex` >> simp[expr_exit_def] >>
  TRY (rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def])
QED

(* An expression statement: its expression's fragment, which leaves its
   block open, run for its effects.  A value of any kind but a hashmap is
   dropped; an expression never raises a return, break or continue. *)
Theorem compile_expr_stmt_frag:
  !ctx func cx lctx RetQ cenv ty e es res es'.
    eval_stmt cx (Expr e) es = (res, es') /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) /\
                ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >>
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
      disj1_tac >> rename1 `stmt_state_rel func cenv cx _ s1` >>
      qexists_tac `s1` >>
      simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >>
  Cases_on `r1` >> gvs[] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED
