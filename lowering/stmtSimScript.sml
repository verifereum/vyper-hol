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
 *     IntRet with intret_vals_match for an internal function (#638), the
 *     halt of the return sequence for an external one (#640).
 * The relation is frame-local: stmt_state_rel speaks of the current
 * frame's locals, allocations and variables only, so an internal-function
 * body reuses the judgment with its own RetQ.
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
 *   stmt_res_ok, stmt_exit, stmt_lands, cenv_top_ext, stmt_frag
 *   cs_mono               — code only appended, variables handed out forward
 *   stmt_frag_nil, stmt_frag_cons — statement lists
 *   stmt_state_rel_pop_top_ext     — leaving a scope
 *   compile_pass_frag, compile_break_frag, compile_continue_frag
 *   compile_expr_stmt_frag         — an expression statement
 *   compile_if_stmt_frag           — If, either branch, every outcome
 *   compile_raise_frag, compile_assert_frag
 *   compile_for_range_frag         — For over a range with literal ends,
 *                                    under a loop invariant
 *   compile_for_range_frag_simple  — the same with the body's judgment at
 *                                    every source state
 *   for_iteration                  — one pass of the range loop
 *   for_loop                       — the range loop from any counter value
 *
 * Not here: Assign/AugAssign (#550), Append and For over an array (#559),
 * Log (#570). Return of a word from an internal function is in
 * stmtSimReturn; AnnAssign of a word local and Raise and Assert with a
 * string literal reason are in stmtSimCases; the other returns,
 * declarations and reasons are not covered yet.
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
   variable RETPC_PARAM binds at the function's entry) is defined, and the
   code from sa on never assigns it.  RET reads it; an external function
   has none. *)
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
  disj1_tac >> qexistsl_tac [`jump_to ex s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  qspecl_then [`ctx`, `func`, `sa`, `cs'`, `s0`,
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
  disj1_tac >> qexistsl_tac [`jump_to inc s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  qspecl_then [`ctx`, `func`, `sa`, `cs'`, `s0`,
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

(* A compile action that only appends code and hands out variables
   forward. *)
Definition cs_mono_def:
  cs_mono (m : 'a compiler) <=>
    !sa x sb. m sa = (x, sb) ==>
              cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
End

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

Theorem local_ptrs_rel_cenv_cong:
  !func cenv cenv' scopes ss.
    local_ptrs_rel func cenv' scopes ss /\
    (!n e. lookup_scopes n scopes = SOME e ==>
           FLOOKUP cenv.ce_vars n = FLOOKUP cenv'.ce_vars n) ==>
    local_ptrs_rel func cenv scopes ss
Proof
  rw[local_ptrs_rel_def, local_region_def] >> metis_tac[]
QED

(* state_rel reads cenv through the locals in scope and its other
   (storage, transient, immutable) bindings. *)
Theorem state_rel_cenv_cong:
  !func cenv cenv' cx vs ss.
    state_rel func cenv' cx vs ss /\
    (!n e. lookup_scopes n vs.scopes = SOME e ==>
           FLOOKUP cenv.ce_vars n = FLOOKUP cenv'.ce_vars n) /\
    (!n l. FLOOKUP cenv.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv'.ce_vars n = SOME l) /\
    (!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv.ce_vars n = SOME l) /\
    cenv'.ce_module = cenv.ce_module /\ cenv'.ce_is_ctor = cenv.ce_is_ctor ==>
    state_rel func cenv cx vs ss
Proof
  rw[state_rel_def]
  >- metis_tac[local_ptrs_rel_cenv_cong]
  >- (simp[storage_vars_rel_def] >> conj_tac >> rpt strip_tac
      >- (`FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module,name)) =
           SOME (StorageLoc slot)` by
            (qpat_x_assum `!n l. FLOOKUP cenv.ce_vars n = SOME l /\ _ ==> _`
               irule >> simp[]) >>
          qpat_x_assum `storage_vars_rel cenv' cx` mp_tac >>
          simp[storage_vars_rel_def] >> metis_tac[]) >>
      qpat_x_assum `!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ _ ==> _` irule >>
      simp[] >> qpat_x_assum `storage_vars_rel cenv' cx` mp_tac >>
      simp[storage_vars_rel_def] >> metis_tac[])
  >- (simp[transient_vars_rel_def] >> conj_tac >> rpt strip_tac
      >- (`FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module,name)) =
           SOME (TransientLoc slot)` by
            (qpat_x_assum `!n l. FLOOKUP cenv.ce_vars n = SOME l /\ _ ==> _`
               irule >> simp[]) >>
          qpat_x_assum `transient_vars_rel cenv' cx` mp_tac >>
          simp[transient_vars_rel_def] >> metis_tac[]) >>
      qpat_x_assum `!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ _ ==> _` irule >>
      simp[] >> qpat_x_assum `transient_vars_rel cenv' cx` mp_tac >>
      simp[transient_vars_rel_def] >> metis_tac[])
  >- (fs[immutables_rel_def, LET_THM] >> Cases_on `cenv.ce_is_ctor` >>
      gvs[] >> rpt strip_tac >>
      `FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module,name)) =
       SOME (ImmutableLoc byte_offset)` by (first_x_assum irule >> simp[]) >>
      metis_tac[]) >>
  fs[logs_rel_def, LIST_REL_EL_EQN, log_entry_equiv_def]
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
  drule_all stmt_state_rel_pop_scope >>
  rw[stmt_state_rel_def] >- (
    irule state_rel_cenv_cong >>
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
    fs[compileEnvTheory.compile_env_component_equality]) >>
  res_tac
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
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:toplevel_value``]
                      expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

(* ===== A condition and its JNZ ===== *)

(* A boolean condition lowered from sa to s1 and a JNZ on it right after,
   in a block that fn holds as finished: on a value, b, the run goes on
   from the JNZ's target for b in a state related at the source state
   after the condition, the variables handed out before sa and the
   allocations kept; on an error it exits as expr_exit allows. *)
Theorem cond_jump_frag:
  !ctx func cx cenv e es r1 es1 sa op s1 s3 s4 lt lf s0.
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    expr_type e = BaseT BoolT /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op, s1) /\
    eval_expr cx e es = (r1, es1) /\ expr_res_ok r1 /\
    (!v. r1 = INL (Value v) ==> ?b. v = BoolV b) /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    emit_inst JNZ [op; Label lt; Label lf] [] s3 = ((), s4) /\
    lookup_block s4.cs_current_bb func.fn_blocks =
      SOME <| bb_label := s4.cs_current_bb;
              bb_instructions := s4.cs_current_insts |> /\
    fn_has_code sa s1 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?b s. r1 = INL (Value (BoolV b)) /\
           stmt_state_rel func cenv cx es1 s /\ ~s.vs_halted /\
           (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                  lookup_var x s = SOME w) /\
           (!aid bnd. FLOOKUP s0.vs_allocas aid = SOME bnd ==>
                      FLOOKUP s.vs_allocas aid = SOME bnd) /\
           !fuel r. run_from fuel ctx func (jump_to (if b then lt else lf) s) = r /\
                    (!e. r <> Error e) ==>
                    ?fuel'. run_from fuel' ctx func s0 = r) \/
    (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
              expr_exit r1 r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (
    disj1_tac >> gvs[expr_post_def] >>
    rename1 `stmt_state_rel func cenv cx es1 sv` >> qexists_tac `sv` >>
    simp[] >> rpt strip_tac >>
    drule emit_inst_extends >> strip_tac >>
    qabbrev_tac `jnz = mk_inst s3.cs_next_id JNZ [op; Label lt; Label lf] []` >>
    `get_instruction <| bb_label := s4.cs_current_bb;
                        bb_instructions := s4.cs_current_insts |>
       sv.vs_inst_idx = SOME jnz` by
      gvs[get_instruction_def, EL_LENGTH_APPEND] >>
    `eval_operand op sv = SOME (if b then 1w else 0w)` by
      gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
          typed_val_to_w256_def, val_to_w256_def] >>
    `step_inst_base jnz sv = OK (jump_to (if b then lt else lf) sv)` by
      (qunabbrev_tac `jnz` >> simp[venomInstTheory.mk_inst_def] >>
       drule step_jnz_behavior >> disch_then (fn th => simp[th]) >>
       Cases_on `b` >> simp[]) >>
    `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
      simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
    `run_from (SUC fuel) ctx func sv =
     run_from fuel ctx func (jump_to (if b then lt else lf) sv)` by
      (qspecl_then [`fuel`, `ctx`, `func`, `sv`,
         `<| bb_label := s4.cs_current_bb;
             bb_instructions := s4.cs_current_insts |>`,
         `jnz`, `if b then lt else lf`,
         `run_from fuel ctx func (jump_to (if b then lt else lf) sv)`]
         mp_tac run_from_jump_result >>
       impl_tac >- gvs[] >> simp[]) >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
      (qspec_then `SUC fuel` mp_tac) >>
    impl_tac >- metis_tac[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `fuel` >> fs[]
QED

(* ===== if/else ===== *)

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

(* An if/else in the source, for every outcome: the condition's error,
   a condition that is not a bool (a type error), or the branch the
   condition selects run in a fresh scope, which is popped after it
   whatever its outcome; its declarations are new to the scopes below. *)
Theorem eval_stmt_if_all:
  !cx c ss1 ss2 es res es'.
    eval_stmt cx (If c ss1 ss2) es = (res, es') ==>
    ?r1 es1. eval_expr cx c es = (r1, es1) /\
      ((?ex. r1 = INR ex /\ res = INR ex /\ es' = es1) \/
       (?tv. r1 = INL tv /\ (!b. tv <> Value (BoolV b)) /\
             ?m. res = INR (Error (TypeError m))) \/
       (?b es2 sc rest. r1 = INL (Value (BoolV b)) /\
          eval_stmts cx (if b then ss1 else ss2)
            (es1 with scopes := FEMPTY :: es1.scopes) = (res, es2) /\
          es2.scopes = sc :: rest /\ es' = es2 with scopes := rest /\
          !n. n IN FDOM sc ==> lookup_scopes n rest = NONE))
Proof
  rpt gen_tac >>
  `!x. x with scopes updated_by CONS FEMPTY =
       x with scopes := FEMPTY :: x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       finally_def, return_def] >>
  Cases_on `eval_expr cx c es` >> rename1 `eval_expr cx c es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `switch_BoolV tv` >>
  Cases_on `?b. tv = Value (BoolV b)`
  >- (
    gvs[] >>
    qabbrev_tac `esA = es1 with scopes := FEMPTY :: es1.scopes` >>
    Cases_on `eval_stmts cx (if b then ss1 else ss2) esA` >>
    rename1 `_ = (r2, es2)` >>
    `switch_BoolV (Value (BoolV b)) (eval_stmts cx ss1) (eval_stmts cx ss2)
       esA = (r2, es2)` by (Cases_on `b` >> gvs[switch_BoolV_def]) >>
    `es2.scopes <> []` by
      (drule eval_stmts_preserves_scopes_dom >>
       simp[preserves_scopes_dom_def, Abbr `esA`]) >>
    Cases_on `es2.scopes` >> gvs[] >>
    `!id. id IN FDOM h ==> lookup_scopes id t = NONE` by
      (rpt strip_tac >> drule eval_stmts_new_in_head_not_in_tail >>
       simp[Abbr `esA`]) >>
    Cases_on `r2` >> simp[pop_scope_def, return_def, raise_def]) >>
  `tv <> Value (BoolV T) /\ tv <> Value (BoolV F)` by metis_tac[] >>
  simp[switch_BoolV_def, raise_def, pop_scope_def, return_def] >>
  strip_tac >> disj1_tac >> gvs[] >> metis_tac[]
QED

(* compile_if_parts (loweringSlice), with where the code ends when both
   branches end their blocks: no exit block follows. *)
Theorem compile_if_parts_all:
  !cenv lctx ty c ss1 ss2 st st'.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') ==>
    ?cond_op s1 s4 s5 s6 s7 s8 s9 s10 s11 then_lbl else_lbl exit_lbl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      cs_extends s1 s4 /\ s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      s4.cs_next_var = s1.cs_next_var /\
      emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] s4 =
        ((), s5) /\
      new_block then_lbl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label exit_lbl] [] s7 = ((), s8)) /\
      new_block else_lbl s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label exit_lbl] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block exit_lbl s11 = (x11, st')) /\
      (block_is_terminated s7 /\ block_is_terminated s10 ==> st' = s11)
Proof
  rpt gen_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_get_def,
       emit_jmp_if_not_terminated_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  (fn (asl, w) =>
     MAP_EVERY (fn v => Cases_on `^v`)
       (filter (fn v => type_of v = oneSyntax.one_ty)
          (free_varsl (w :: asl))) (asl, w)) >>
  rename1 `fresh_label "then" s1 = (then_lbl, s2)` >>
  rename1 `fresh_label "else" s2 = (else_lbl, s3)` >>
  rename1 `fresh_label "if_exit" s3 = (exit_lbl, s4)` >>
  rename1 `emit_inst JNZ _ _ s4 = ((), s5)` >>
  rename1 `new_block then_lbl s5 = (x5, s6)` >>
  rename1 `compile_stmts _ _ _ ss1 s6 = ((), s7)` >>
  rename1 `new_block else_lbl s8 = (x8, s9)` >>
  rename1 `compile_stmts _ _ _ ss2 s9 = ((), s10)` >>
  strip_tac >>
  rename1 `(if block_is_terminated s10 then _ else _) s10 = ((), s11)` >>
  qexistsl_tac [`s4`, `s5`, `s6`, `s7`, `s8`, `s9`, `s10`, `s11`,
                `then_lbl`, `else_lbl`, `exit_lbl`, `x5`, `x8`] >>
  imp_res_tac fresh_label_props >>
  `cs_extends s1 s4` by
    metis_tac[cs_extends_fresh_label, cs_extends_trans] >>
  rpt conj_tac >> fs[] >>
  TRY (Cases_on `block_is_terminated s7` >> fs[comp_return_def] >> NO_TAC) >>
  TRY (Cases_on `block_is_terminated s10` >> fs[comp_return_def] >> NO_TAC) >>
  rpt strip_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[]
QED

(* The branch an if/else takes, from the start of its block, run in the
   branch's fresh scope: on normal completion it jumps to the exit block
   (when its code does not end its block, a JMP there follows it), and
   leaving the branch pops its scope, which goes back to cenv. *)
Theorem if_branch_frag:
  !ctx func cx lctx RetQ cenv ty ss esA res es2 sc rest sa sb sj sx lbl' x
   exit_lbl st' s0.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty ss)
      esA res es2 /\
    compile_stmts cenv lctx ty ss sa = ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    sa.cs_current_insts = [] /\ stmt_res_ok lctx res /\
    stmt_state_rel func cenv cx esA s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = 0 /\
    es2.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
    (~block_is_terminated sb ==>
     emit_inst JMP [Label exit_lbl] [] sb = ((), sj) /\
     new_block lbl' sj = (x, sx) /\ fn_has_code sb sx func /\
     st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []) ==>
    (?s. stmt_lands lctx st' res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb) /\
         stmt_state_rel func cenv cx (es2 with scopes := rest) s /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s0 = r) \/
    (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
              stmt_exit RetQ (es2 with scopes := rest) res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`,
                           `FST (stmts_env cenv lctx ty ss sa)`] mp_tac) >>
  impl_tac
  >- (fs[compile_stmts_env, block_is_terminated_def] >>
      Cases_on `stmts_env cenv lctx ty ss sa` >> gvs[]) >>
  strip_tac
  >- (
    rename1 `stmt_state_rel func cenv2 cx es2 s1` >>
    `stmt_state_rel func cenv cx (es2 with scopes := rest) s1` by
      (qspecl_then [`func`, `cenv`, `cenv2`, `cx`, `es2`, `s1`, `sc`, `rest`]
         mp_tac stmt_state_rel_pop_top_ext >> simp[]) >>
    qpat_x_assum `stmt_lands _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def])
    >- (
      (* the branch completes: the JMP to the exit block *)
      fs[] >>
      drule emit_inst_extends >> strip_tac >>
      `cs_extends sb sj /\ cs_extends sj sx` by
        metis_tac[cs_appends_emit_helpers, cs_appends_def,
                  cs_extends_new_block] >>
      `fn_has_code sb sj func` by metis_tac[fn_has_code_split] >>
      qspecl_then [`ctx`, `func`, `sb`, `sj`, `s1`,
                   `mk_inst sb.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`]
        mp_tac run_from_jump_end >>
      impl_tac
      >- simp[venomInstTheory.mk_inst_def, step_jmp_behavior,
              is_terminator_def] >>
      strip_tac >>
      disj1_tac >> qexists_tac `jump_to exit_lbl s1` >>
      simp[stmt_lands_def, stmt_state_rel_jump_to] >>
      rpt conj_tac >> TRY (simp[jump_to_def] >> NO_TAC) >>
      TRY (fs[jump_to_def, lookup_var_def] >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      rpt strip_tac >>
      qpat_x_assum
        `!fuel r. run_from fuel ctx func (jump_to _ _) = r /\ _ ==> _`
        (qspecl_then [`fuel`, `run_from fuel ctx func (jump_to exit_lbl s1)`]
           mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
    (* a break or continue: at the loop's block *)
    disj1_tac >> qexists_tac `s1` >> fs[stmt_lands_def]) >>
  disj2_tac >> qexists_tac `fuel` >> fs[stmt_exit_def]
QED

(* if/else, for every outcome: the condition's error exits, and the
   branch the condition selects runs in a fresh scope, from the block the
   JNZ enters, with its own judgment at cenv. *)
Theorem compile_if_stmt_frag:
  !ctx func cx lctx RetQ cenv ty c ss1 ss2 es res es'.
    eval_stmt cx (If c ss1 ss2) es = (res, es') /\
    expr_type c = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!b es1 res2 es2.
       eval_expr cx c es = (INL (Value (BoolV b)), es1) /\
       eval_stmts cx (if b then ss1 else ss2)
         (es1 with scopes := FEMPTY :: es1.scopes) = (res2, es2) ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes) res2 es2) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule compile_if_parts_all >> strip_tac >>
  (* the code *)
  imp_res_tac new_block_props >> imp_res_tac emit_inst_extends >>
  `stmts_env cenv lctx ty ss1 s6 = (FST (stmts_env cenv lctx ty ss1 s6), s7) /\
   stmts_env cenv lctx ty ss2 s9 = (FST (stmts_env cenv lctx ty ss2 s9), s10)` by
    (fs[compile_stmts_env] >>
     Cases_on `stmts_env cenv lctx ty ss1 s6` >>
     Cases_on `stmts_env cenv lctx ty ss2 s9` >> gvs[]) >>
  `cs_extends s6 s7 /\ s6.cs_next_var <= s7.cs_next_var /\
   cs_extends s9 s10 /\ s9.cs_next_var <= s10.cs_next_var` by
    (fs[cs_mono_def] >> metis_tac[]) >>
  `!sx sy. (if block_is_terminated sx then sy = sx
            else emit_inst JMP [Label exit_lbl] [] sx = ((), sy)) ==>
           cs_extends sx sy /\ sx.cs_next_var = sy.cs_next_var` by
    (rw[] >> imp_res_tac emit_inst_extends >>
     metis_tac[cs_extends_refl, cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by metis_tac[] >>
  `cs_extends s7 s8 /\ s7.cs_next_var = s8.cs_next_var /\
   cs_extends s10 s11 /\ s10.cs_next_var = s11.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s8 s9` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `cs_extends s11 sb` by
    (Cases_on `block_is_terminated s7 /\ block_is_terminated s10`
     >- (fs[] >> simp[cs_extends_refl]) >>
     `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
     metis_tac[cs_extends_new_block]) >>
  `cs_extends sa s4 /\ cs_extends sa s6 /\ cs_extends s6 s9 /\
   cs_extends s7 s9 /\ cs_extends s9 sb /\ cs_extends s10 sb /\
   cs_extends s7 sb /\ cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s6 s7 func /\ fn_has_code s9 s10 func /\
   fn_has_code s7 s9 func /\ fn_has_code s10 sb func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_refl,
              cs_extends_trans] >>
  `lookup_block s5.cs_current_bb func.fn_blocks =
     SOME <| bb_label := s5.cs_current_bb;
             bb_instructions := s5.cs_current_insts |>` by
    metis_tac[fn_has_code_new_block] >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var` by
    (fs[] >> decide_tac) >>
  (* the source *)
  qpat_x_assum `eval_stmt _ _ _ = _`
    (strip_assume_tac o MATCH_MP eval_stmt_if_all)
  >- (
    (* the condition's error *)
    fs[] >>
    `expr_res_ok r1` by
      (gvs[] >> imp_res_tac (cj 1 eval_expr_no_control) >>
       gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
    qspecl_then [`ctx`, `func`, `cx`, `cenv`, `c`, `es`, `r1`, `es1`, `sa`,
                 `cond_op`, `s1`, `s4`, `s5`, `then_lbl`, `else_lbl`, `s0`]
      mp_tac cond_jump_frag >>
    impl_tac >- fs[] >> strip_tac >> fs[] >>
    disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >> disj1_tac >>
    ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:toplevel_value``]
                        expr_exit_INR_type] >>
    first_assum ACCEPT_TAC)
  >- gvs[stmt_res_ok_def] >>
  (* the branch the condition selects *)
  fs[] >>
  qspecl_then [`ctx`, `func`, `cx`, `cenv`, `c`, `es`,
               `INL (Value (BoolV b))`, `es1`, `sa`, `cond_op`, `s1`, `s4`,
               `s5`, `then_lbl`, `else_lbl`, `s0`] mp_tac cond_jump_frag >>
  impl_tac >- fs[expr_res_ok_def] >>
  strip_tac >> fs[] >>
  rename1 `stmt_state_rel func cenv cx es1 sv` >>
  `!st l. sa.cs_next_var <= st.cs_next_var ==>
          ret_pc_ok cenv st (jump_to l sv)` by
    (rpt strip_tac >> REWRITE_TAC [ret_pc_ok_jump_to] >>
     qspecl_then [`cenv`, `cenv`, `sa`, `st`, `s0`, `sv`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var` by
    decide_tac >>
  Cases_on `b` >> fs[]
  >- (
    qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty`, `ss1`,
                 `es1 with scopes := FEMPTY::es1.scopes`, `res`, `es2`, `sc`,
                 `rest`, `s6`, `s7`, `s8`, `s9`, `else_lbl`, `x8`, `exit_lbl`,
                 `sb`, `jump_to then_lbl sv`] mp_tac if_branch_frag >>
    impl_tac
    >- (rpt conj_tac >>
        fs[stmt_state_rel_jump_to, stmt_state_rel_push_scope, jump_to_def]
        >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[]) >>
        strip_tac >> fs[] >>
        `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
        imp_res_tac new_block_props >> fs[]) >>
    strip_tac
    >- (
      disj1_tac >>
      rename1 `stmt_state_rel func cenv cx (es2 with scopes := rest) sz` >>
      qexistsl_tac [`sz`, `cenv`] >> fs[cenv_top_ext_refl] >> rpt conj_tac
      >- (strip_tac >> fs[] >>
          `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
          imp_res_tac new_block_props >> fs[block_is_terminated_def])
      >- (rpt strip_tac >>
          `not_fresh_at s6 x` by
            (fs[not_fresh_at_def] >> rw[] >> first_x_assum irule >>
             decide_tac) >>
          `lookup_var x sv = SOME w` by res_tac >>
          `lookup_var x (jump_to then_lbl sv) = SOME w` by
            fs[lookup_var_def, jump_to_def] >>
          res_tac)
      >- (rpt strip_tac >> res_tac >>
          `FLOOKUP (jump_to then_lbl sv).vs_allocas aid = SOME b` by
            fs[jump_to_def] >>
          res_tac) >>
      rpt strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func sz <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >> impl_tac >- fs[] >> strip_tac >>
      qpat_x_assum
        `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      qpat_x_assum `b'` (fn th => REWRITE_TAC [EQT_INTRO th]) >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
    disj2_tac >>
    qpat_x_assum
      `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
      (qspec_then `fuel` mp_tac) >>
    qpat_x_assum `b'` (fn th => REWRITE_TAC [EQT_INTRO th]) >>
    impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
    qexists_tac `fuel'` >> gvs[]) >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty`, `ss2`,
               `es1 with scopes := FEMPTY::es1.scopes`, `res`, `es2`, `sc`,
               `rest`, `s9`, `s10`, `s11`, `sb`, `exit_lbl`,
               `s11.cs_current_bb`, `exit_lbl`, `sb`, `jump_to else_lbl sv`]
    mp_tac if_branch_frag >>
  impl_tac
  >- (rpt conj_tac >>
      fs[stmt_state_rel_jump_to, stmt_state_rel_push_scope, jump_to_def]
      >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[]) >>
      strip_tac >>
      qpat_x_assum `_ \/ _ ==> ?x11. _` mp_tac >> fs[] >> strip_tac >>
      imp_res_tac new_block_props >> fs[]) >>
  strip_tac
  >- (
    disj1_tac >>
    rename1 `stmt_state_rel func cenv cx (es2 with scopes := rest) sz` >>
    qexistsl_tac [`sz`, `cenv`] >> fs[cenv_top_ext_refl] >> rpt conj_tac
    >- (strip_tac >> fs[] >>
        `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
        imp_res_tac new_block_props >> fs[block_is_terminated_def])
    >- (rpt strip_tac >>
        `not_fresh_at s9 x` by
          (fs[not_fresh_at_def] >> rw[] >> first_x_assum irule >>
           decide_tac) >>
        `lookup_var x sv = SOME w` by res_tac >>
        `lookup_var x (jump_to else_lbl sv) = SOME w` by
          fs[lookup_var_def, jump_to_def] >>
        res_tac)
    >- (rpt strip_tac >> res_tac >>
        `FLOOKUP (jump_to else_lbl sv).vs_allocas aid = SOME b` by
          fs[jump_to_def] >>
        res_tac) >>
    rpt strip_tac >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sz <> Error e) ==> _`
      (qspec_then `fuel` mp_tac) >> impl_tac >- fs[] >> strip_tac >>
    qpat_x_assum
      `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
      (qspec_then `fuel'` mp_tac) >>
    qpat_x_assum `~b'` (fn th => REWRITE_TAC [EQF_INTRO th]) >>
    impl_tac >- metis_tac[] >> metis_tac[]) >>
  disj2_tac >>
  qpat_x_assum
    `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  qpat_x_assum `~b'` (fn th => REWRITE_TAC [EQF_INTRO th]) >>
  impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
  qexists_tac `fuel'` >> gvs[]
QED

(* ===== Raise and Assert ===== *)

(* An emitted instruction that aborts where the run reaches it exits as
   the source outcome allows. *)
Theorem emit_abort_exit:
  !ctx func opc ops st st' s0 RetQ es' res.
    emit_inst opc ops [] st = ((), st') /\ fn_has_code st st' func /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s0.vs_halted /\
    opc <> INVOKE /\
    (?a s'. step_inst_base (mk_inst st.cs_next_id opc ops []) s0 =
              Abort a s' /\ expr_exit res (Abort a s')) ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             stmt_exit RetQ es' res r
Proof
  rpt strip_tac >> drule emit_inst_extends >> strip_tac >>
  `frag_exec ctx st st' (\s. s = s0) (\s. F) (stmt_exit RetQ es' res)` by
    (irule frag_exec_step_abort >> fs[] >> qexists_tac `0` >>
     fs[step_inst_non_invoke, venomInstTheory.mk_inst_def, stmt_exit_def]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >> simp[frag_exec_def]
QED

Theorem step_revert_zero:
  !id s.
    ?s'. step_inst_base (mk_inst id REVERT [Lit 0w; Lit 0w] []) s =
         Abort Revert_abort s'
Proof
  rpt gen_tac >> simp[venomInstTheory.mk_inst_def] >>
  irule_at Any step_revert_behavior >> simp[eval_operand_def]
QED

Theorem step_invalid:
  !id s.
    ?s'. step_inst_base (mk_inst id INVALID [] []) s = Abort ExHalt_abort s'
Proof
  simp[venomInstTheory.mk_inst_def, step_inst_base_def]
QED

(* raise and raise UNREACHABLE: a REVERT with no data, and INVALID. *)
Theorem compile_raise_frag:
  !ctx func cx lctx RetQ cenv ty rk es res es'.
    (rk = RaiseBare \/ rk = RaiseUnreachable) /\
    eval_stmt cx (Raise rk) es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_abort_exit >>
  disch_then (qspecl_then [`ctx`, `func`, `s0`, `RetQ`, `es'`, `res`]
                mp_tac) >>
  (impl_tac
   >- (fs[markerTheory.Abbrev_def] >>
       qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, raise_def] >> strip_tac >>
       gvs[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid])) >>
  metis_tac[]
QED

(* assert and assert UNREACHABLE: the condition, a JNZ to the ok block,
   which is where the code ends, and a fail block that aborts with REVERT
   (no data) or INVALID. *)
Theorem compile_assert_frag:
  !ctx func cx lctx RetQ cenv ty e ak es res es'.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >> (
    qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
    simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
    Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
    rename1 `_ = (op, s1)` >> simp[] >>
    Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok, s2)` >> simp[] >>
    Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl, s3)` >>
    simp[] >>
    Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
    rename1 `_ = (u4, s4)` >> simp[] >>
    Cases_on `new_block fl s4` >> rename1 `_ = (x5, s5)` >> simp[] >>
    qmatch_goalsub_abbrev_tac `emit_inst opc ops [] s5` >>
    Cases_on `emit_inst opc ops [] s5` >> rename1 `_ = (u6, s6)` >> simp[] >>
    Cases_on `new_block ok s6` >> rename1 `new_block ok s6 = (x7, s7)` >>
    simp[] >> strip_tac >> gvs[] >>
    imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
    imp_res_tac emit_inst_extends >>
    `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
     cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
     cs_extends s6 s7` by
      metis_tac[cs_extends_fresh_label, cs_extends_new_block,
                cs_appends_emit_helpers, cs_appends_def] >>
    `fn_has_code sa s1 func /\ fn_has_code s4 s5 func /\
     fn_has_code s5 s6 func` by
      metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
                cs_extends_refl] >>
    `lookup_block s4.cs_current_bb func.fn_blocks =
       SOME <| bb_label := s4.cs_current_bb;
               bb_instructions := s4.cs_current_insts |>` by
      metis_tac[fn_has_code_new_block] >>
    qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def] >>
    Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
    strip_tac >>
    `expr_res_ok r1 /\ !v. r1 = INL (Value v) ==> ?b. v = BoolV b` by (
      Cases_on `r1` >> gvs[]
      >- (rename1 `switch_BoolV tv` >>
          Cases_on `?b. tv = Value (BoolV b)` >> gvs[expr_res_ok_def] >>
          `tv <> Value (BoolV T) /\ tv <> Value (BoolV F)` by metis_tac[] >>
          gvs[switch_BoolV_def, raise_def, stmt_res_ok_def]) >>
      imp_res_tac (cj 1 eval_expr_no_control) >>
      gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
    qspecl_then [`ctx`, `func`, `cx`, `cenv`, `e`, `es`, `r1`, `es1`, `sa`,
                 `op`, `s1`, `s3`, `s4`, `ok`, `fl`, `s0`] mp_tac cond_jump_frag >>
    impl_tac >- fs[] >> strip_tac
    >- (
      Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def]
      >- (
        (* the condition holds: the ok block, where the code ends *)
        disj1_tac >> rename1 `stmt_state_rel func cenv cx es' sv` >>
        qexists_tac `jump_to s7.cs_current_bb sv` >>
        gvs[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
            block_is_terminated_def] >>
        simp[jump_to_def, lookup_var_def] >> fs[lookup_var_def, jump_to_def]) >>
      (* it fails: the fail block aborts *)
      disj2_tac >> rename1 `stmt_state_rel func cenv cx es' sv` >>
      qmatch_goalsub_abbrev_tac `stmt_exit RetQ es' rres _` >>
      qspecl_then [`ctx`, `func`, `opc`, `ops`, `s5`, `s6`,
                   `jump_to s5.cs_current_bb sv`, `RetQ`, `es'`, `rres`]
        mp_tac emit_abort_exit >>
      impl_tac
      >- (fs[markerTheory.Abbrev_def, jump_to_def] >> gvs[expr_exit_def] >>
          metis_tac[step_revert_zero, step_invalid]) >>
      strip_tac >>
      qpat_x_assum
        `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >>
      impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
      qexists_tac `fuel'` >> gvs[]) >>
    (* the condition's error *)
    disj2_tac >> qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >>
    disj1_tac >>
    ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:toplevel_value``]
                        expr_exit_INR_type] >>
    first_assum ACCEPT_TAC)
QED

(* ===== for over a literal range ===== *)

Theorem eval_iterator_range_lit:
  !cx a1 n1 a2 n2 es.
    n1 <= n2 ==>
    eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) es =
    (INL (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM, return_def] >>
  simp[Once evaluate_def, return_def, evaluate_literal_def] >>
  simp[Once evaluate_def, return_def, evaluate_literal_def] >>
  simp[get_range_limits_def, lift_sum_def, return_def]
QED

(* A range with literal ends, nonempty or empty, within the loop's bound:
   the loop over its values. *)
Theorem eval_stmt_for_range_lit:
  !cx id fty a1 n1 a2 n2 bound body es res es' tyv.
    eval_stmt cx
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound body) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ n1 <= n2 /\
    Num (n2 - n1) <= bound ==>
    eval_for cx tyv id body (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
      es = (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       lift_option_type_def, lift_option_def, return_def, raise_def] >>
  simp[eval_iterator_range_lit, check_def, assert_def, compatible_bound_def]
QED

(* One iteration: the body in a scope holding the loop variable, which is
   popped after it; a normal end or a continue goes on with the rest of the
   values, a break ends the loop, any other exception leaves it. *)
Theorem eval_for_cons_cases:
  !cx tyv nm stmts v vs es res es'.
    eval_for cx tyv nm stmts (v::vs) es = (res, es') /\
    lookup_scopes nm es.scopes = NONE ==>
    ?r2 es2 sc rest.
      eval_stmts cx stmts
        (es with scopes :=
           (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) ::
           es.scopes) = (r2, es2) /\
      es2.scopes = sc :: rest /\ MAP FDOM rest = MAP FDOM es.scopes /\
      (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
      ((r2 = INL () \/ r2 = INR ContinueException) /\
       eval_for cx tyv nm stmts vs (es2 with scopes := rest) = (res, es') \/
       r2 = INR BreakException /\ res = INL () /\
       es' = es2 with scopes := rest \/
       (?e. r2 = INR e /\ e <> BreakException /\ e <> ContinueException) /\
       res = r2 /\ es' = es2 with scopes := rest)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_with_var_def,
       finally_def, try_def, return_def] >>
  `!x. x with scopes updated_by
         CONS (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) =
       x with scopes :=
         (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) ::
         x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[] >>
  qabbrev_tac `esA = es with scopes :=
     (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) ::
     es.scopes` >>
  Cases_on `eval_stmts cx stmts esA` >> rename1 `_ = (r2, es2)` >>
  `es2.scopes <> [] /\ MAP FDOM (TL es2.scopes) = MAP FDOM es.scopes` by
    (drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def, Abbr `esA`]) >>
  Cases_on `es2.scopes` >> fs[] >>
  `!id. id IN FDOM h ==> lookup_scopes id t = NONE` by
    (rpt strip_tac >> Cases_on `id = nm`
     >- (gvs[] >> irule lookup_scopes_none_map_fdom >> metis_tac[]) >>
     drule eval_stmts_new_in_head_not_in_tail >> simp[Abbr `esA`]) >>
  Cases_on `r2` >> fs[pop_scope_def, return_def, raise_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = ContinueException` >> Cases_on `ex = BreakException` >>
  fs[handle_loop_exception_def, return_def, raise_def, pop_scope_def] >>
  rw[] >> fs[]
QED

(* The increment block of a range loop: the counter cv goes up by one and
   the run goes back to the condition block. *)
Theorem for_incr_block:
  !ctx func dd cv nv c lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
    lookup_var cv dd = SOME c ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to cond_lbl
           (update_var cv (c + 1w) (update_var nv (c + 1w) dd))) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func dd = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |>` >>
  `!fu. run_from fu ctx func dd =
        run_from fu ctx func (update_var nv (c + 1w) dd with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `dd`, `bb`,
                  `mk_inst i1 ADD [Var cv; Lit 1w] [nv]`,
                  `update_var nv (c + 1w) dd`] mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
              is_terminator_def] >>
         `step_inst_base (mk_inst i1 ADD [Var cv; Lit 1w] [nv]) dd =
          OK (update_var nv (c + 1w) dd)` by
           (irule step_ADD >> simp[eval_operand_def]) >>
         fs[venomInstTheory.mk_inst_def]) >>
     simp[]) >>
  qabbrev_tac `d1 = update_var nv (c + 1w) dd with vs_inst_idx := 1` >>
  `!fu. run_from fu ctx func d1 =
        run_from fu ctx func (update_var cv (c + 1w) d1 with vs_inst_idx := 2)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst i2 ASSIGN [Var nv] [cv]`,
                  `update_var cv (c + 1w) d1`] mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, Abbr `d1`, get_instruction_def,
              venomInstTheory.mk_inst_def, is_terminator_def,
              update_var_def] >>
         simp[step_inst_base_def, eval_operand_def, lookup_var_def,
              update_var_def, FLOOKUP_UPDATE]) >>
     simp[Abbr `d1`]) >>
  qabbrev_tac `d2 = update_var cv (c + 1w) d1 with vs_inst_idx := 2` >>
  `jump_to cond_lbl d2 =
   jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) dd))` by
    simp[Abbr `d2`, Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d2 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d2`, `bb`,
                  `mk_inst i3 JMP [Label cond_lbl] []`, `cond_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac >- (fs[Abbr `bb`, Abbr `d2`, Abbr `d1`, get_instruction_def,
                     venomInstTheory.mk_inst_def, is_terminator_def,
                     update_var_def, step_jmp_behavior]) >>
     simp[]) >>
  fs[]
QED

(* The condition block of a range loop: the counter cv against the end ev,
   to the exit block when they are equal and to the body otherwise. *)
Theorem for_cond_block:
  !ctx func cc cv ev dv a b lbl exit_lbl body_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to (if a = b then exit_lbl else body_lbl)
           (update_var dv (bool_to_word (a = b)) cc)) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |>` >>
  `!fu. run_from fu ctx func cc =
        run_from fu ctx func
          (update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `cc`, `bb`,
                  `mk_inst j1 EQ [Var cv; Var ev] [dv]`,
                  `update_var dv (bool_to_word (a = b)) cc`]
       mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
              is_terminator_def] >>
         `step_inst_base (mk_inst j1 EQ [Var cv; Var ev] [dv]) cc =
          OK (update_var dv (bool_to_word (a = b)) cc)` by
           (irule step_EQ >> simp[eval_operand_def]) >>
         fs[venomInstTheory.mk_inst_def]) >>
     simp[]) >>
  qabbrev_tac `d1 = update_var dv (bool_to_word (a = b)) cc with
                      vs_inst_idx := 1` >>
  `jump_to (if a = b then exit_lbl else body_lbl) d1 =
   jump_to (if a = b then exit_lbl else body_lbl)
     (update_var dv (bool_to_word (a = b)) cc)` by
    simp[Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d1 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []`,
                  `if a = b then exit_lbl else body_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac
     >- (fs[Abbr `bb`, Abbr `d1`, get_instruction_def,
            venomInstTheory.mk_inst_def, is_terminator_def,
            update_var_def] >>
         qmatch_goalsub_abbrev_tac `step_inst_base _ ss` >>
         `eval_operand (Var dv) ss = SOME (bool_to_word (a = b))` by
           simp[Abbr `ss`, eval_operand_def, lookup_var_def,
                FLOOKUP_UPDATE] >>
         drule step_jnz_behavior >>
         disch_then (qspecl_then [`exit_lbl`, `body_lbl`, `j2`] mp_tac) >>
         simp[] >> strip_tac >>
         Cases_on `a = b` >> fs[bool_to_word_def, Abbr `ss`, jump_to_def]) >>
     simp[]) >>
  fs[]
QED

(* The entry block of a range loop with literal ends: the counter cv starts
   at a, the end ev is a + b, and the run goes to the condition block. *)
Theorem for_entry_block:
  !ctx func ee cv ev a b lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ASSIGN [Lit a] [cv];
                                  mk_inst i2 ADD [Lit a; Lit b] [ev];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to cond_lbl (update_var ev (a + b) (update_var cv a ee))) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ee = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ASSIGN [Lit a] [cv];
                                  mk_inst i2 ADD [Lit a; Lit b] [ev];
                                  mk_inst i3 JMP [Label cond_lbl] []] |>` >>
  `!fu. run_from fu ctx func ee =
        run_from fu ctx func (update_var cv a ee with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `ee`, `bb`,
                  `mk_inst i1 ASSIGN [Lit a] [cv]`, `update_var cv a ee`]
       mp_tac run_from_step >>
     impl_tac
     >- simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
             is_terminator_def, step_inst_base_def, eval_operand_def] >>
     simp[]) >>
  qabbrev_tac `d1 = update_var cv a ee with vs_inst_idx := 1` >>
  `!fu. run_from fu ctx func d1 =
        run_from fu ctx func (update_var ev (a + b) d1 with vs_inst_idx := 2)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst i2 ADD [Lit a; Lit b] [ev]`,
                  `update_var ev (a + b) d1`] mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, Abbr `d1`, get_instruction_def,
              venomInstTheory.mk_inst_def, is_terminator_def,
              update_var_def] >>
         qspecl_then [`Lit a`, `Lit b`, `a`, `b`, `i2`, `ev`,
           `ee with <|vs_vars := ee.vs_vars |+ (cv, a); vs_inst_idx := 1|>`]
           mp_tac step_ADD >>
         simp[eval_operand_def, venomInstTheory.mk_inst_def,
              update_var_def]) >>
     simp[Abbr `d1`]) >>
  qabbrev_tac `d2 = update_var ev (a + b) d1 with vs_inst_idx := 2` >>
  `jump_to cond_lbl d2 =
   jump_to cond_lbl (update_var ev (a + b) (update_var cv a ee))` by
    simp[Abbr `d2`, Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d2 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d2`, `bb`,
                  `mk_inst i3 JMP [Label cond_lbl] []`, `cond_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac >- (fs[Abbr `bb`, Abbr `d2`, Abbr `d1`, get_instruction_def,
                     venomInstTheory.mk_inst_def, is_terminator_def,
                     update_var_def, step_jmp_behavior]) >>
     simp[]) >>
  fs[]
QED

(* The end of the block a range loop starts in: the loop variable's ALLOCA,
   then the jump to the entry block. *)
Theorem for_start_block:
  !ctx func s0 s1 aa pre lbl entry_lbl i.
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                pre ++ [aa; mk_inst i JMP [Label entry_lbl] []] |> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    aa.inst_opcode = ALLOCA /\ step_inst_base aa s0 = OK s1 /\
    s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted ==>
    !fuel rr.
      run_from fuel ctx func (jump_to entry_lbl s1) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s0 = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions :=
                pre ++ [aa; mk_inst i JMP [Label entry_lbl] []] |>` >>
  `!fu. run_from fu ctx func s0 =
        run_from fu ctx func (s1 with vs_inst_idx := SUC (LENGTH pre))` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `s0`, `bb`, `aa`, `s1`]
       mp_tac run_from_step >>
     impl_tac
     >- simp[Abbr `bb`, get_instruction_def, EL_LENGTH_APPEND,
             is_terminator_def] >>
     simp[]) >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `jump_to entry_lbl (s1 with vs_inst_idx := SUC (LENGTH pre)) =
   jump_to entry_lbl s1` by simp[jump_to_def] >>
  qspecl_then [`fuel`, `ctx`, `func`, `s1 with vs_inst_idx := SUC (LENGTH pre)`,
               `bb`, `mk_inst i JMP [Label entry_lbl] []`, `entry_lbl`, `rr`]
    mp_tac run_from_jump_result >>
  impl_tac
  >- (fs[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
         is_terminator_def, step_jmp_behavior] >>
      simp[EL_APPEND2]) >>
  fs[]
QED

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

(* An integer literal lowers to its word. *)
Theorem lower_value_int_lit:
  !cenv ty a n st.
    lower_value compile_expr cenv ty (Literal a (IntL n)) st = (Lit (i2w n), st)
Proof
  simp[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
       compile_literal_vv_def, unwrap_value_def]
QED

(* The code of a range loop with literal ends, its locals held through
   pointers: the loop variable's ALLOCA ending the block it starts in, the
   entry block (the counter and the end), the condition block, the body
   block (the counter stored into the loop variable, then the body), the
   increment block, and the exit block, where the code ends. *)
Theorem compile_for_range_parts:
  !cenv lctx ty id fty a1 n1 a2 n2 bound stmts st st' func.
    compile_stmt cenv lctx ty
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) st = ((), st') /\
    cenv.ce_alloca_locals /\ fn_has_code st st' func /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb) ==>
    ?p cv ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl bc sb0 sb1 sj
     nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 2)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 3)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc, st with cs_next_var := st.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (st.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 4 /\ cs_extends st sb0 /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks =
        SOME <| bb_label := st.cs_current_bb;
                bb_instructions :=
                  st.cs_current_insts ++
                  [mk_inst st.cs_next_id ALLOCA
                     [Lit (n2w (type_memory_bytes cenv fty))] [p];
                   mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []] |> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <| bb_label := entry_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
                   mk_inst (st.cs_next_id + 3) ADD
                     [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
                   mk_inst (st.cs_next_id + 4) JMP [Label cond_lbl] []] |> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <| bb_label := cond_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 5) EQ [Var cv; Var ev] [dv];
                   mk_inst (st.cs_next_id + 6) JNZ
                     [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
             get_instruction bbb 0 =
               SOME (mk_inst (st.cs_next_id + 7) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts =
         sb1.cs_current_insts ++
         [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <| bb_label := incr_lbl;
                bb_instructions :=
                  [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
                   mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
                   mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []] |> /\
      st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM, lower_value_int_lit] >>
  Cases_on `declare_local cenv id fty st` >> rename1 `_ = (bc, st1)` >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_stmts bc _ ty stmts _ = ((), sb1)` >>
  qpat_x_assum `(if block_is_terminated sb1 then _ else _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [comp_bind_def, comp_return_def,
                                         fresh_id_def, emit_def, LET_THM]) >>
  rename1 `_ = ((), sj)` >>
  qmatch_asmsub_abbrev_tac `compile_stmts bc _ ty stmts sb0 = _` >>
  strip_tac >> qexistsl_tac [`sb0`, `sb1`, `sj`] >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  `cs_extends st sb0` by
    (simp[cs_extends_def, Abbr `sb0`] >> qexists_tac `[_; _; _]` >> simp[]) >>
  `sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
   sj.cs_next_var = sb1.cs_next_var /\ cs_extends sb1 sj /\
   (~block_is_terminated sb1 ==>
    sj.cs_current_insts =
      sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP
         [Label (fresh_label_output "for_incr" (st.cs_next_label + 3))] []])` by
    (Cases_on `block_is_terminated sb1` >>
     fs[comp_return_def, comp_bind_def, fresh_id_def, emit_def, LET_THM] >>
     gvs[cs_extends_refl] >>
     irule cs_extends_same_block >> simp[]) >>
  `cs_extends sj st'` by
    (qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[cs_extends_def] >>
     qexists_tac `[_; <| bb_label := sj.cs_current_bb;
                         bb_instructions := sj.cs_current_insts |>]` >>
     simp[]) >>
  `?nb. sb1.cs_blocks = nb ++ sb0.cs_blocks` by
    (qpat_x_assum `cs_extends sb0 sb1` mp_tac >> simp[cs_extends_def] >>
     metis_tac[]) >>
  `!l b. MEM b (emitted_blocks st st') /\ b.bb_label = l ==>
         lookup_block l func.fn_blocks = SOME b` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `emitted_blocks st st' =
   [HD st'.cs_blocks; HD (TL st'.cs_blocks)] ++ nb ++
   [HD sb0.cs_blocks; HD (TL sb0.cs_blocks); HD (TL (TL sb0.cs_blocks))]` by
    (irule emitted_blocks_append >>
     qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[Abbr `sb0`]) >>
  `cs_extends sb1 st' /\ cs_extends sb0 st'` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `?bbb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bbb /\
         isPREFIX sb0.cs_current_insts bbb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  qpat_x_assum `_ = st'` (assume_tac o SYM) >> rpt conj_tac
  >- simp[Abbr `sb0`]
  >- simp[Abbr `sb0`]
  >- simp[Abbr `sb0`]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj2_tac >> disj2_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qexists_tac `bbb` >>
      qpat_x_assum `lookup_block sb0.cs_current_bb _ = _` mp_tac >>
      qpat_x_assum `isPREFIX sb0.cs_current_insts _` mp_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
      Cases_on `bbb.bb_instructions` >> fs[get_instruction_def])
  >- (strip_tac >>
      qpat_x_assum `~block_is_terminated sb1 ==> _` drule >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj1_tac >> disj1_tac >> disj1_tac >>
      qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) [])
  >- (qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) []) >>
  qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
  simp_tac (srw_ss()) []
QED

(* stmt_state_rel reads the compile environment through the locals in
   scope and its other bindings. *)
Theorem stmt_state_rel_cenv_cong:
  !func cenv cenv' cx es ss.
    stmt_state_rel func cenv' cx es ss /\
    (!n e. lookup_scopes n es.scopes = SOME e ==>
           FLOOKUP cenv.ce_vars n = FLOOKUP cenv'.ce_vars n) /\
    (!n l. FLOOKUP cenv.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv'.ce_vars n = SOME l) /\
    (!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv.ce_vars n = SOME l) /\
    cenv'.ce_module = cenv.ce_module /\ cenv'.ce_is_ctor = cenv.ce_is_ctor ==>
    stmt_state_rel func cenv cx es ss
Proof
  rw[stmt_state_rel_def] >- (irule state_rel_cenv_cong >> metis_tac[]) >>
  res_tac
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

(* The counter of a range loop over [n1, n2), as a word. *)
Theorem i2w_counter_ne:
  !n1 n2 k. n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) ==>
            (i2w (n1 + &k) : bytes32) <> i2w n2
Proof
  rpt strip_tac >>
  qabbrev_tac `N = Num (n2 - n1)` >>
  `&N = n2 - n1` by (simp[Abbr `N`] >> intLib.ARITH_TAC) >>
  `n2 = (n1 + &k) + &(N - k)` by
    (`&(N - k) = &N - &k : int` by simp[integerTheory.INT_SUB] >>
     intLib.ARITH_TAC) >>
  `(i2w n2 : bytes32) = i2w (n1 + &k) + n2w (N - k)` by
    (qpat_x_assum `n2 = _`
       (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
     simp[GSYM integer_wordTheory.word_i2w_add,
          integer_wordTheory.i2w_pos]) >>
  `i2w (n1 + &k) + n2w (N - k) = (i2w (n1 + &k) : bytes32)` by metis_tac[] >>
  `(n2w (N - k) : bytes32) = 0w` by
    metis_tac[wordsTheory.WORD_ADD_RID_UNIQ, wordsTheory.WORD_ADD_COMM] >>
  `N - k < dimword (:256) /\ 0 < N - k` by decide_tac >>
  qpat_x_assum `n2w (N - k) = 0w` mp_tac >>
  fs[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]
QED

Theorem i2w_counter_end:
  !n1 n2. n1 <= n2 ==> (i2w (n1 + &Num (n2 - n1)) : bytes32) = i2w n2
Proof
  rpt strip_tac >>
  `n1 + &Num (n2 - n1) = n2` by
    (`&Num (n2 - n1) = n2 - n1` by intLib.ARITH_TAC >> intLib.ARITH_TAC) >>
  simp[]
QED

Theorem i2w_counter_suc:
  !n1 k. (i2w (n1 + &k) : bytes32) + 1w = i2w (n1 + &(k + 1))
Proof
  rpt gen_tac >>
  `(1w : bytes32) = i2w 1` by simp[integer_wordTheory.i2w_pos] >>
  pop_assum SUBST1_TAC >> simp[integer_wordTheory.word_i2w_add] >>
  AP_TERM_TAC >> intLib.ARITH_TAC
QED

(* A range loop's iteration starts: the condition block finds the counter
   short of the end and jumps to the body block, whose MSTORE stores the
   counter into the loop variable.  The relation then holds at the body's
   environment bc, for the source state with the loop variable's scope
   pushed. *)
Theorem for_body_entry:
  !ctx func cenv bc cx esk cc id tyv p sz w ainst cv ev dv n1 n2 k
   cond_lbl exit_lbl body_lbl j1 j2 j3 bbb.
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    lookup_scopes id esk.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor /\
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 ==>
    ?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
         ~s2.vs_halted /\
         stmt_state_rel func bc cx
           (esk with scopes :=
              (FEMPTY |+ (id, <| assignable := F; type := tyv;
                                 value := IntV (n1 + &k) |>)) :: esk.scopes)
           s2 /\
         (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
         s2.vs_allocas = cc.vs_allocas /\
         !fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  `(i2w (n1 + &k) : bytes32) <> i2w n2` by metis_tac[i2w_counter_ne] >>
  qabbrev_tac `s1 = jump_to body_lbl (update_var dv (bool_to_word F) cc)` >>
  `!fuel rr. run_from fuel ctx func s1 = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func cc = rr` by
    (qspecl_then [`ctx`, `func`, `cc`, `cv`, `ev`, `dv`, `i2w (n1 + &k)`,
                  `i2w n2`, `cond_lbl`, `exit_lbl`, `body_lbl`, `j1`, `j2`]
       mp_tac for_cond_block >> simp[Abbr `s1`]) >>
  `lookup_var p s1 = SOME w /\ lookup_var cv s1 = SOME (i2w (n1 + &k)) /\
   s1.vs_current_bb = body_lbl /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
   s1.vs_allocas = cc.vs_allocas /\
   (!x. x <> dv ==> lookup_var x s1 = lookup_var x cc)` by
    (simp[Abbr `s1`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n w) (i2w (n1 + &k)) s1 with vs_inst_idx := 1` >>
  `!fu. run_from fu ctx func s1 = run_from fu ctx func s2` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `s1`, `bbb`,
                  `mk_inst j3 MSTORE [Var p; Var cv] []`,
                  `mstore (w2n w) (i2w (n1 + &k)) s1`] mp_tac run_from_step >>
     impl_tac
     >- (simp[venomInstTheory.mk_inst_def, is_terminator_def] >>
         `step_inst_base (mk_inst j3 MSTORE [Var p; Var cv] []) s1 =
          OK (mstore (w2n w) (i2w (n1 + &k)) s1)` by
           (irule step_MSTORE >> simp[eval_operand_def]) >>
         fs[venomInstTheory.mk_inst_def]) >>
     simp[Abbr `s2`]) >>
  `stmt_state_rel func cenv cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (simp[Abbr `s1`, stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel func bc cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >> simp[] >>
     rpt strip_tac >> Cases_on `n = id` >> gvs[lookup_scopes_def] >>
     res_tac >> gvs[]) >>
  qspecl_then [`func`, `bc`, `cx`, `esk with scopes := FEMPTY :: esk.scopes`,
               `s1`, `id`, `p`, `sz`, `w`, `ainst`, `IntV (n1 + &k)`, `tyv`,
               `FEMPTY`, `esk.scopes`, `F`] mp_tac stmt_state_rel_declare_word >>
  impl_tac >- simp[lookup_scopes_def, word_value_def] >>
  simp[val_to_w256_def] >> strip_tac >>
  qexists_tac `s2` >>
  simp[Abbr `s2`, stmt_state_rel_inst_idx] >> rpt conj_tac >>
  TRY (simp[mstore_def, LET_THM] >> NO_TAC) >>
  TRY (rpt strip_tac >> fs[mstore_def, LET_THM, lookup_var_def] >> NO_TAC) >>
  metis_tac[]
QED

(* Every non-Error result from a is one from b, and from b one from c:
   then from a one from c. *)
Theorem run_from_results_trans[local]:
  !ctx func a b c.
    (!fuel r. run_from fuel ctx func a = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx func b = r) /\
    (!fuel r. run_from fuel ctx func b = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx func c = r) ==>
    !fuel r. run_from fuel ctx func a = r /\ (!e. r <> Error e) ==>
             ?fuel'. run_from fuel' ctx func c = r
Proof
  metis_tac[]
QED

(* The rest of an iteration from the increment block, at DD. *)
val for_incr_tac =
  qpat_x_assum `stmt_state_rel func cenv cx (es2 with scopes := rest) DD`
    assume_tac >>
  qspecl_then [`ctx`, `func`, `DD`, `cv`, `nv`, `i2w (n1 + &k)`, `incr_lbl`,
               `cond_lbl`, `i1`, `i2`, `i3`] mp_tac for_incr_block >>
  impl_tac >- fs[] >> strip_tac >>
  disj1_tac >> simp[] >>
  qexists_tac `jump_to cond_lbl (update_var cv (i2w (n1 + &k) + 1w)
                 (update_var nv (i2w (n1 + &k) + 1w) DD))` >>
  rpt conj_tac
  >- simp[jump_to_def]
  >- simp[jump_to_def]
  >- fs[jump_to_def, update_var_def]
  >- (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
      fs[] >> irule stmt_state_rel_update_var >> fs[])
  >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          i2w_counter_suc]
  >- fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  >- fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  >- (rpt strip_tac >> fs[jump_to_def, update_var_def, lookup_var_def,
                          FLOOKUP_UPDATE] >> metis_tac[])
  >- (rpt strip_tac >> fs[jump_to_def, update_var_def] >> metis_tac[]) >>
  (* the results chain back through DD (and s3 when DD is its jump) to cc *)
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `run_from fuel ctx func XX` >>
  qspecl_then [`ctx`, `func`, `XX`, `DD`, `cc`] mp_tac
    run_from_results_trans >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      FIRST [first_assum ACCEPT_TAC,
             MATCH_MP_TAC run_from_results_trans >> qexists_tac `s3` >>
             conj_tac >> first_assum ACCEPT_TAC]) >>
  disch_then (qspecl_then [`fuel`, `run_from fuel ctx func XX`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> simp[];

(* One iteration of a range loop, from the condition block with the counter
   at n1 + k short of the end: the body runs in the loop variable's scope,
   at bc, from the body block's MSTORE on.  On a normal end or a continue
   the run comes back to the condition block with the counter at
   n1 + k + 1, related at the source state after the iteration (the
   loop variable's scope popped); on a break it reaches the exit block; on
   any other outcome it exits as the body does. *)
Theorem for_iteration:
  !ctx func cenv bc cx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv nv
   n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st r2 es2 sc rest.
    (* the code *)
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    lookup_block incr_lbl func.fn_blocks =
      SOME <| bb_label := incr_lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
    fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
    sb0.cs_current_bb = body_lbl /\ LENGTH sb0.cs_current_insts = 1 /\
    ~block_is_terminated sb0 /\
    (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts =
       sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
     fn_has_code sb1 sj func) /\
    fn_inst_ids_distinct func /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\
    (* the environments and variables *)
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!scs. not_local_ptr cenv scs cv /\ not_local_ptr cenv scs dv /\
           not_local_ptr cenv scs nv) /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
    cv <> ev /\ cv <> p /\ ev <> p /\
    not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\ not_fresh_at sb0 p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    32 <= sz /\ type_memory_size tyv = 32 /\
    (* the iteration *)
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    eval_stmts cx stmts
      (esk with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k) |>)) :: esk.scopes) =
      (r2, es2) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
      (esk with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k) |>)) :: esk.scopes)
      r2 es2 /\
    stmt_res_ok (InLoop exit_lbl incr_lbl) r2 /\
    es2.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    ((r2 = INL () \/ r2 = INR ContinueException) /\
     ?cc'. cc'.vs_current_bb = cond_lbl /\ cc'.vs_inst_idx = 0 /\
           ~cc'.vs_halted /\
           stmt_state_rel func cenv cx (es2 with scopes := rest) cc' /\
           lookup_var cv cc' = SOME (i2w (n1 + &(k + 1))) /\
           lookup_var ev cc' = SOME (i2w n2) /\ lookup_var p cc' = SOME w /\
           (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                  lookup_var x cc' = SOME v) /\
           (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                  FLOOKUP cc'.vs_allocas a = SOME b) /\
           !fuel rr. run_from fuel ctx func cc' = rr /\ (!e. rr <> Error e) ==>
                     ?fuel'. run_from fuel' ctx func cc = rr) \/
    (r2 = INR BreakException /\
     ?s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel func cenv cx (es2 with scopes := rest) s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b) /\
         !fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr) \/
    (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
               stmt_exit RetQ (es2 with scopes := rest) r2 rr)
Proof
  rpt gen_tac >> strip_tac >>
  `bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor` by
    (qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `bc`, `cx`, `esk`, `cc`, `id`, `tyv`,
               `p`, `sz`, `w`, `ainst`, `cv`, `ev`, `dv`, `n1`, `n2`, `k`,
               `cond_lbl`, `exit_lbl`, `body_lbl`, `j1`, `j2`, `j3`, `bbb`]
    mp_tac for_body_entry >>
  impl_tac >- fs[] >> strip_tac >>
  `ret_pc_ok bc sb0 s2` by
    (qspecl_then [`cenv`, `bc`, `st`, `sb0`, `cc`, `s2`] mp_tac
       ret_pc_ok_frame >>
     impl_tac
     >- (rpt conj_tac
         >- first_assum ACCEPT_TAC
         >- (qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >>
             simp[])
         >- first_assum ACCEPT_TAC >>
         rpt strip_tac >>
         qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> strip_tac >>
         qpat_x_assum `!x. x <> dv ==> lookup_var x s2 = _` drule >> simp[]) >>
     simp[]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_def]) >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s2`,
     `FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)`] mp_tac) >>
  impl_tac
  >- (fs[compile_stmts_env] >>
      Cases_on `stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0` >>
      gvs[]) >>
  strip_tac
  >- (
    (* the body reaches its end, the increment block or the exit block *)
    rename1 `stmt_state_rel func c3 cx es2 s3` >>
    qabbrev_tac `esA = esk with scopes :=
           (FEMPTY |+ (id, <| assignable := F; type := tyv;
                              value := IntV (n1 + &k) |>)) :: esk.scopes` >>
    `cenv_top_ext cenv bc esA.scopes` by
      (simp[cenv_top_ext_def, Abbr `esA`] >> rpt strip_tac >>
       Cases_on `n = id` >> gvs[]) >>
    `cenv_top_ext cenv c3 es2.scopes` by
      (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `esA.scopes`] >>
       simp[] >>
       qpat_x_assum `eval_stmts _ _ _ = _`
         (strip_assume_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
       gvs[preserves_scopes_dom_def, Abbr `esA`]) >>
    `stmt_state_rel func cenv cx (es2 with scopes := rest) s3` by
      (qspecl_then [`func`, `cenv`, `c3`, `cx`, `es2`, `s3`, `sc`, `rest`]
         mp_tac stmt_state_rel_pop_top_ext >> simp[]) >>
    `!x v. not_fresh_at sb0 x /\ x <> dv /\ lookup_var x cc = SOME v ==>
           lookup_var x s3 = SOME v` by
      (rpt strip_tac >> first_x_assum irule >> fs[]) >>
    `lookup_var cv s3 = SOME (i2w (n1 + &k)) /\
     lookup_var ev s3 = SOME (i2w n2) /\ lookup_var p s3 = SOME w` by
      (rpt conj_tac >> first_x_assum irule >> fs[]) >>
    `!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
           FLOOKUP s3.vs_allocas a = SOME b` by
      (rpt strip_tac >> first_x_assum irule >> fs[]) >>
    `!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
           lookup_var x s3 = SOME v` by
      (rpt strip_tac >> first_x_assum irule >> fs[not_fresh_at_def] >>
       rw[] >> first_x_assum irule >> decide_tac) >>
    `!fuel rr. run_from fuel ctx func s3 = rr /\ (!e. rr <> Error e) ==>
               ?fuel'. run_from fuel' ctx func cc = rr` by
      (rpt strip_tac >>
       qpat_x_assum `!fuel r. run_from fuel ctx func s3 = r /\ _ ==> _`
         (qspecl_then [`fuel`, `rr`] mp_tac) >> simp[] >> strip_tac >>
       qpat_x_assum `!fuel rr. run_from fuel ctx func s2 = rr /\ _ ==> _`
         (qspecl_then [`fuel'`, `rr`] mp_tac) >> simp[]) >>
    qpat_x_assum `stmt_lands _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def])
    >- (
      (* its end: the JMP to the increment block *)
      `~block_is_terminated sb1` by fs[] >>
      qpat_x_assum `~block_is_terminated sb1 ==> _` drule >> strip_tac >>
      qspecl_then [`ctx`, `func`, `sb1`, `sj`, `s3`,
                   `mk_inst sb1.cs_next_id JMP [Label incr_lbl] []`, `incr_lbl`]
        mp_tac run_from_jump_end >>
      impl_tac
      >- simp[venomInstTheory.mk_inst_def, step_jmp_behavior,
              is_terminator_def] >>
      strip_tac >> qabbrev_tac `DD = jump_to incr_lbl s3` >>
      `DD.vs_current_bb = incr_lbl /\ DD.vs_inst_idx = 0 /\ ~DD.vs_halted /\
       (!x. lookup_var x DD = lookup_var x s3) /\
       DD.vs_allocas = s3.vs_allocas /\
       stmt_state_rel func cenv cx (es2 with scopes := rest) DD` by
        simp[Abbr `DD`, jump_to_def, lookup_var_def, stmt_state_rel_jump_to] >>
      for_incr_tac)
    >- (
      (* a break: the exit block *)
      disj2_tac >> disj1_tac >> simp[] >> qexists_tac `s3` >> fs[]) >>
    (* a continue: the increment block *)
    qabbrev_tac `DD = s3` >> for_incr_tac) >>
  (* the body exits *)
  disj2_tac >> disj2_tac >>
  qpat_x_assum `!fuel rr. run_from fuel ctx func s2 = rr /\ _ ==> _`
    (qspecl_then [`fuel`, `run_from fuel ctx func s2`] mp_tac) >>
  impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
  qexistsl_tac [`fuel'`, `run_from fuel ctx func s2`] >>
  gvs[stmt_exit_def]
QED

(* A range loop from its condition block with the counter at n1 + k and m
   iterations left: it reaches the exit block on the source's normal end
   (a break included), related at the source state after the loop, or
   exits as the source's outcome allows. *)
Theorem for_loop:
  !m P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w res es'.
    (* the code *)
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    lookup_block incr_lbl func.fn_blocks =
      SOME <| bb_label := incr_lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
    fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
    sb0.cs_current_bb = body_lbl /\ LENGTH sb0.cs_current_insts = 1 /\
    ~block_is_terminated sb0 /\
    (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts =
       sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
     fn_has_code sb1 sj func) /\
    fn_inst_ids_distinct func /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\
    (* the environments and variables *)
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!scs. not_local_ptr cenv scs cv /\ not_local_ptr cenv scs dv /\
           not_local_ptr cenv scs nv) /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
    cv <> ev /\ cv <> p /\ ev <> p /\
    not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\ not_fresh_at sb0 p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    32 <= sz /\ type_memory_size tyv = 32 /\
    (* the body, at the iteration states over a source state where P holds *)
    (!ei j r2 es2.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) r2 es2) /\
    (* P holds again after an iteration that goes on *)
    (!ei j r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    (* the loop from iteration k *)
    k + m = Num (n2 - n1) /\
    eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m) esk =
      (res, es') /\
    stmt_res_ok lctx res /\ P esk /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) ==>
    (?s. res = INL () /\ s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
         ~s.vs_halted /\ stmt_state_rel func cenv cx es' s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b) /\
         !fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr) \/
    (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
               stmt_exit RetQ es' res rr)
Proof
  Induct
  >- (
    (* no iteration left: the counter is at the end *)
    rpt gen_tac >> strip_tac >>
    `(i2w (n1 + &k) : bytes32) = i2w n2` by
      (`k = Num (n2 - n1)` by decide_tac >> simp[i2w_counter_end]) >>
    qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, return_def] >> strip_tac >>
    qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
    qpat_x_assum `esk = es'` (SUBST_ALL_TAC o SYM) >>
    qspecl_then [`ctx`, `func`, `cc`, `cv`, `ev`, `dv`, `i2w (n1 + &k)`,
                 `i2w n2`, `cond_lbl`, `exit_lbl`, `body_lbl`, `j1`, `j2`]
      mp_tac for_cond_block >> simp[] >> strip_tac >>
    disj1_tac >> qexists_tac `jump_to exit_lbl (update_var dv 1w cc)` >>
    rpt conj_tac
    >- simp[jump_to_def]
    >- simp[jump_to_def]
    >- fs[jump_to_def, update_var_def]
    >- (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
        fs[])
    >- (rpt strip_tac >> fs[jump_to_def, update_var_def, lookup_var_def,
                            FLOOKUP_UPDATE] >> metis_tac[])
    >- fs[jump_to_def, update_var_def] >>
    metis_tac[]) >>
  (* an iteration, then the loop from the next counter *)
  rpt gen_tac >> strip_tac >>
  `k < Num (n2 - n1)` by decide_tac >>
  `GENLIST (\j. (IntV (n1 + &(k + j)) : value)) (SUC m) =
   (IntV (n1 + &k) : value) ::
   GENLIST (\j. (IntV (n1 + &(k + 1 + j)) : value)) m` by
    (simp[GENLIST_CONS, combinTheory.o_DEF] >>
     simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
     `k + SUC x = x + (k + 1)` by decide_tac >> simp[]) >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `GENLIST _ (SUC m) = _` (fn th => REWRITE_TAC [th]) >>
  strip_tac >> drule_all eval_for_cons_cases >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `bc`, `cx`, `RetQ`, `ty`, `stmts`, `esk`,
               `cc`, `id`, `tyv`, `p`, `sz`, `w`, `ainst`, `cv`, `ev`, `dv`,
               `nv`, `n1`, `n2`, `k`, `cond_lbl`, `exit_lbl`, `body_lbl`,
               `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sb0`,
               `sb1`, `sj`, `st`, `r2`, `es2`, `sc`, `rest`]
    mp_tac for_iteration >>
  (impl_tac
   >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
       >- (qpat_assum `!scs. lookup_scopes id scs = NONE ==> _` irule >>
           first_assum ACCEPT_TAC)
       >- (qpat_assum `!ei j r2 es2. P ei /\ _ ==> stmt_frag _ _ _ _ _ _ _ _ _ _`
             irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
       fs[stmt_res_ok_def])) >>
  strip_tac >>
  TRY (qpat_x_assum `stmt_exit _ _ _ _` mp_tac >>
       qpat_x_assum `r2 = _` (fn th => REWRITE_TAC [th]) >>
       REWRITE_TAC [stmt_exit_loop_ctl] >> NO_TAC) >>
  (* the outcome cases that do not go together *)
  TRY (rpt (qpat_x_assum `r2 = _` mp_tac) >>
       rpt (qpat_x_assum `_ <> ContinueException` mp_tac) >> simp[] >>
       NO_TAC) >>
  (* another exception exits *)
  TRY (qpat_assum `stmt_exit _ _ _ _` kall_tac >> disj2_tac >>
       qexists_tac `fuel` >> qexists_tac `rr` >>
       qpat_x_assum `es' = _` SUBST_ALL_TAC >>
       qpat_x_assum `res = _` SUBST_ALL_TAC >> simp[] >> NO_TAC) >>
  (* a break lands at the exit block *)
  TRY (qpat_assum `r2 = INR BreakException` kall_tac >>
       rename1 `stmt_state_rel func cenv cx _ s9` >> disj1_tac >>
       qexists_tac `s9` >> fs[] >> NO_TAC) >>
  (* the loop goes on from the incremented counter, where P holds again *)
  `P (es2 with scopes := rest)` by
    (qpat_assum `!ei j r2 es2 sc rest. P ei /\ _ ==> P _`
       (qspecl_then [`esk`, `k`, `r2`, `es2`, `sc`, `rest`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> gvs[]) >>
     simp[]) >>
  `ret_pc_ok cenv st cc'` by
    (qspecl_then [`cenv`, `cenv`, `st`, `st`, `cc`, `cc'`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  qpat_x_assum `!P ctx func. _`
    (qspecl_then [`P`, `ctx`, `func`, `cenv`, `bc`, `cx`, `lctx`, `RetQ`, `ty`,
                  `stmts`, `id`, `tyv`, `p`, `sz`, `ainst`, `cv`, `ev`, `dv`,
                  `nv`, `n1`, `n2`, `cond_lbl`, `exit_lbl`, `body_lbl`,
                  `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sb0`,
                  `sb1`, `sj`, `st`, `k + 1`, `es2 with scopes := rest`, `cc'`,
                  `w`, `res`, `es'`] mp_tac) >>
  (impl_tac
   >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
       TRY decide_tac >>
       TRY (simp[] >> irule lookup_scopes_none_map_fdom >>
            qexists_tac `esk.scopes` >> fs[] >> NO_TAC) >>
       metis_tac[])) >>
  (strip_tac
    >- (rename1 `stmt_state_rel func cenv cx es' s9` >> disj1_tac >>
        qexists_tac `s9` >> rpt conj_tac >>
        TRY (first_assum ACCEPT_TAC >> NO_TAC)
        >- (rpt strip_tac >>
            qpat_x_assum `!x v. not_fresh_at st x /\ lookup_var x cc' = SOME v ==> _`
              irule >> fs[] >>
            qpat_x_assum `!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> _`
              irule >> fs[])
        >- (rpt strip_tac >>
            qpat_x_assum `!a b. FLOOKUP cc'.vs_allocas a = SOME b ==> _` irule >>
            qpat_x_assum `!a b. FLOOKUP cc.vs_allocas a = SOME b ==> _` irule >>
            fs[]) >>
        rpt strip_tac >>
        qpat_x_assum `!fuel rr. run_from fuel ctx func s9 = rr /\ _ ==> _`
          (qspecl_then [`fuel`, `rr`] mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum `!fuel rr. run_from fuel ctx func cc' = rr /\ _ ==> _`
          (qspecl_then [`fuel'`, `rr`] mp_tac) >> simp[]) >>
    disj2_tac >> rename1 `run_from f9 ctx func cc' = r9` >>
    drule exit_result_not_error >> strip_tac >>
    qpat_x_assum `!fuel rr. run_from fuel ctx func cc' = rr /\ _ ==> _`
      (qspecl_then [`f9`, `r9`] mp_tac) >> simp[] >> strip_tac >>
    metis_tac[])
QED

(* A pointer variable handed out at or after st is no local's pointer. *)
Theorem reserved_fresh_not_local[local]:
  !cenv st n scs.
    local_ptrs_reserved cenv st /\ st.cs_next_var <= n ==>
    not_local_ptr cenv scs (STRING #"%" (toString n))
Proof
  rw[not_local_ptr_def] >> strip_tac >>
  fs[local_ptrs_reserved_def, not_fresh_at_def] >>
  qpat_x_assum `!n1 n2 p sz1 sz2. _`
    (qspecl_then [`name`, `name`, `STRING #"%" (toString n)`, `sz`, `sz`]
       mp_tac) >>
  simp[] >> qexists_tac `n` >> simp[]
QED

(* For over a range with literal ends: the loop variable's ALLOCA, the
   entry block, then the loop from the first counter value; on a normal
   finish the code ends at the start of the exit block.  The body's
   judgment is assumed for the environment declare_local gives, at the
   iteration states over source states where the invariant P holds; P
   holds at the start and again after each iteration that goes on.  Only for
   n1 <= n2 (not the source's "no range" error), a loop variable of one
   word, and ce_alloca_locals, which the lowering sets for external
   functions only. *)
Theorem compile_for_range_frag:
  !P ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es res es'
   tyv.
    eval_stmt cx
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P es /\
    (!st0 c st1 ex inc ei j r2 es2.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) r2 es2) /\
    (!ei j r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
            bound stmts)) es res es'
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [stmt_frag_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty
              (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
                 bound stmts) sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = (uu, sb)` >>
  `uu = ()` by simp[oneTheory.one] >> gvs[] >>
  (* the code and the source loop *)
  qspecl_then [`cenv`, `lctx`, `ty`, `id`, `fty`, `a1`, `n1`, `a2`, `n2`,
               `bound`, `stmts`, `sa`, `sb`, `func`]
    mp_tac compile_for_range_parts >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  drule_all eval_stmt_for_range_lit >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  (* the loop variable's ALLOCA *)
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb _ = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] lookup_block_fn_insts)) >>
     simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (simp[not_local_ptr_def] >> rpt strip_tac >>
     fs[local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = sa.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `step_inst_base A s0 = exec_alloca A s0 (n2w sz : bytes32)` by
    simp[Abbr `A`, step_inst_base_def, venomInstTheory.mk_inst_def] >>
  `?s1. exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (simp[exec_alloca_def] >> BasicProvers.every_case_tac >> simp[]) >>
  fs[] >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `A`, `p`,
               `n2w sz : bytes32`, `s1`] mp_tac stmt_state_rel_exec_alloca >>
  impl_tac >- fs[] >> strip_tac >>
  `s1.vs_current_bb = s0.vs_current_bb /\ s1.vs_inst_idx = s0.vs_inst_idx /\
   ~s1.vs_halted /\ (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
   (!a b. FLOOKUP s0.vs_allocas a = SOME b ==>
          FLOOKUP s1.vs_allocas a = SOME b)` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >> simp[exec_alloca_def] >>
     BasicProvers.every_case_tac >> rw[] >>
     fs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> rw[] >>
     fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `w2n (n2w sz : bytes32) = sz` by fs[] >> fs[] >>
  (* the start and entry blocks *)
  qspecl_then [`ctx`, `func`, `s0`, `s1`, `A`, `sa.cs_current_insts`,
               `sa.cs_current_bb`, `entry_lbl`, `sa.cs_next_id + 1`]
    mp_tac for_start_block >>
  impl_tac >- fs[] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `jump_to entry_lbl s1`, `cv`, `ev`, `i2w n1`,
               `i2w n2 - i2w n1`, `entry_lbl`, `cond_lbl`, `sa.cs_next_id + 2`,
               `sa.cs_next_id + 3`, `sa.cs_next_id + 4`]
    mp_tac for_entry_block >>
  impl_tac >- fs[jump_to_def] >>
  REWRITE_TAC [wordsTheory.WORD_SUB_ADD2] >> strip_tac >>
  (* the variables *)
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
   cv <> ev /\ cv <> p /\ ev <> p` by (fs[] >> rw[] >> fs[]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs ev) /\
   (!scs. not_local_ptr cenv scs dv) /\ (!scs. not_local_ptr cenv scs nv)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `ev = _` SUBST1_TAC >>
     qpat_assum `dv = _` SUBST1_TAC >> qpat_assum `nv = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `sa` >> fs[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >>
     `not_local_ptr cenv (FEMPTY::scs) p` by
       (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
        qexists_tac `sa` >> simp[]) >>
     fs[not_local_ptr_def] >> rpt strip_tac >>
     `name <> id` by (strip_tac >> fs[lookup_scopes_def]) >> metis_tac[]) >>
  (* the state at the condition block *)
  qabbrev_tac `cc = jump_to cond_lbl (update_var ev (i2w n2)
                  (update_var cv (i2w n1) (jump_to entry_lbl s1)))` >>
  `stmt_state_rel func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >>
     conj_tac >- (irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
     irule stmt_state_rel_update_var >>
     conj_tac >- (irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
     fs[stmt_state_rel_jump_to]) >>
  `lookup_var p cc = SOME w` by
    (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >>
     qpat_x_assum `lookup_var p s1 = _` mp_tac >>
     qpat_assum `p = _` (fn th => REWRITE_TAC [th]) >> simp[lookup_var_def]) >>
  `FLOOKUP cc.vs_allocas A.inst_id = SOME (w2n w, sz)` by
    (simp[Abbr `cc`, jump_to_def, update_var_def] >>
     qpat_x_assum `FLOOKUP s1.vs_allocas A.inst_id = _` mp_tac >>
     qpat_assum `A.inst_id = _` (fn th => REWRITE_TAC [th])) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x cc = SOME v` by
    (rpt strip_tac >>
     `x <> p /\ x <> cv /\ x <> ev` by
       (fs[not_fresh_at_def] >> rpt conj_tac >> first_x_assum irule >>
        simp[]) >>
     simp[Abbr `cc`, lookup_var_def, jump_to_def, update_var_def,
          FLOOKUP_UPDATE] >>
     fs[GSYM lookup_var_def] >> metis_tac[]) >>
  `ret_pc_ok cenv sa cc` by
    (qspecl_then [`cenv`, `cenv`, `sa`, `sa`, `s0`, `cc`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `!fuel rr. run_from fuel ctx func cc = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func s0 = rr` by
    (simp[Abbr `cc`] >> metis_tac[]) >>
  `!a b. FLOOKUP s0.vs_allocas a = SOME b ==> FLOOKUP cc.vs_allocas a = SOME b`
    by simp[Abbr `cc`, jump_to_def, update_var_def] >>
  `cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
   lookup_var cv cc = SOME (i2w (n1 + 0)) /\ lookup_var ev cc = SOME (i2w n2)`
    by (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
             FLOOKUP_UPDATE] >> fs[jump_to_def]) >>
  (* the loop *)
  qspecl_then [`Num (n2 - n1)`, `P`, `ctx`, `func`, `cenv`, `bc`, `cx`, `lctx`,
               `RetQ`, `ty`, `stmts`, `id`, `tyv`, `p`, `sz`, `A`, `cv`, `ev`,
               `dv`, `nv`, `n1`, `n2`, `cond_lbl`, `exit_lbl`, `body_lbl`,
               `incr_lbl`, `sa.cs_next_id + 5`, `sa.cs_next_id + 6`,
               `sa.cs_next_id + 7`, `bbb`, `sj.cs_next_id`, `sj.cs_next_id + 1`,
               `sj.cs_next_id + 2`, `sb0`, `sb1`, `sj`, `sa`, `0`, `es`, `cc`,
               `w`, `res`, `es'`] mp_tac for_loop >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
                is_terminator_def] >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      TRY (simp[not_fresh_at_def] >> NO_TAC) >>
      TRY (rw[not_fresh_at_def] >>
           TRY (first_x_assum (qspec_then `sj.cs_next_var` mp_tac)) >>
           simp[] >> NO_TAC) >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  strip_tac
  >- (rename1 `s9.vs_current_bb = exit_lbl` >> disj1_tac >>
      qexists_tac `s9` >> qexists_tac `cenv` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- simp[stmt_lands_def]
      >- simp[block_is_terminated_def]
      >- simp[cenv_top_ext_refl]
      >- metis_tac[]
      >- metis_tac[] >>
      rpt strip_tac >> metis_tac[]) >>
  disj2_tac >> rename1 `exit_result r9` >>
  drule exit_result_not_error >> strip_tac >> metis_tac[]
QED

(* The same with the body's judgment at every source state. *)
Theorem compile_for_range_frag_simple:
  !ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es res es'
   tyv.
    eval_stmt cx
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!st0 c st1 ex inc es1 r2 es2.
       declare_local cenv id fty st0 = (c, st1) /\
       eval_stmts cx stmts es1 = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) es1 r2 es2) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
            bound stmts)) es res es'
Proof
  rpt strip_tac >>
  MATCH_MP_TAC (BETA_RULE (Q.SPEC `\e. T` compile_for_range_frag)) >>
  qexists_tac `tyv` >> simp[] >> rpt strip_tac
  >- (qpat_x_assum `!c lc sa sb. _` drule >> simp[])
  >- (qpat_x_assum `!c lc sa sb. _` drule >> simp[]) >>
  qpat_x_assum `!st0 c st1 ex inc es1 r2 es2. _` irule >> metis_tac[]
QED
