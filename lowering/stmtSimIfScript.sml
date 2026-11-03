(*
 * Statement simulation: If, Raise and Assert (#637)
 *
 * Cases of stmt_frag (stmtSim).  A condition's fragment and its JNZ
 * (cond_jump_frag), then either branch as a statement list in a scope of
 * its own; Raise and Assert with no reason, whose aborts are exits.
 *
 * TOP-LEVEL:
 *   cond_jump_frag        — a condition and the jump on it
 *   compile_if_stmt_frag  — If, either branch, every outcome
 *   compile_raise_frag, compile_assert_frag
 *)

Theory stmtSimIf
Ancestors
  stmtSim
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* Source-level forcing boundary for conditions with arbitrary branches. *)
Theorem eval_expr_switch_forced:
  !cx e es kt kf.
    bind (eval_expr cx e) (\raw. switch_BoolV cx raw kt kf) es =
    (case (do raw <- eval_expr cx e; read_result cx raw od) es of
       (INR ex, s) => (INR ex, s)
     | (INL v, s) => if v = BoolV T then kt s
                    else if v = BoolV F then kf s
                    else raise (Error (TypeError "not BoolV")) s)
Proof
  rpt gen_tac >> simp[switch_BoolV_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, est)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `eval_expr cx e es = (INL captured, est)` >>
  Cases_on `read_result cx captured est` >> rename1 `_ = (forced, esf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem eval_assert_forced_parts[local]:
  !cx e ak es res es'.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') ==>
    ?r s. (do raw <- eval_expr cx e; read_result cx raw od) es = (r,s) /\
      (case r of INR ex => (INR ex,s)
       | INL v => if v = BoolV T then (INL (),s)
                  else if v = BoolV F then
                    (INR (AssertException
                      (if ak = AssertBare then "" else "UNREACHABLE")),s)
                  else (INR (Error (TypeError "not BoolV")),s)) = (res,es')
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, eval_expr_switch_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (forced,sf)` >>
  simp[return_def, raise_def] >> Cases_on `forced` >> simp[]
QED

Theorem eval_assert_forced_ok[local]:
  !cx e ak es res es' lctx.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') /\
    stmt_res_ok lctx res ==>
    ?r s. (do raw <- eval_expr cx e; read_result cx raw od) es = (r,s) /\
      expr_res_ok r /\ (!v. r = INL v ==> ?b. v = BoolV b) /\
      (case r of INR ex => (INR ex,s)
       | INL v => if v = BoolV T then (INL (),s)
                  else if v = BoolV F then
                    (INR (AssertException
                      (if ak = AssertBare then "" else "UNREACHABLE")),s)
                  else (INR (Error (TypeError "not BoolV")),s)) = (res,es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_at Any eval_assert_forced_parts >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!exc. r = INR exc ==> no_control_exc exc` by
    (rpt strip_tac >> gvs[] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  qexistsl_tac [`r`,`s`] >> simp[] >>
  Cases_on `r` >> gvs[expr_res_ok_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[stmt_res_ok_def, no_control_exc_def] >> metis_tac[]
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
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\ expr_res_ok r1 /\
    (!v. r1 = INL v ==> ?b. v = BoolV b) /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    emit_inst JNZ [op; Label lt; Label lf] [] s3 = ((), s4) /\
    lookup_block s4.cs_current_bb func.fn_blocks =
      SOME <| bb_label := s4.cs_current_bb;
              bb_instructions := s4.cs_current_insts |> /\
    fn_has_code sa s1 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?b s. r1 = INL (BoolV b) /\
           stmt_state_rel ctx func cenv cx es1 s /\ ~s.vs_halted /\
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
    rename1 `stmt_state_rel ctx func cenv cx es1 sv` >> qexists_tac `sv` >>
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

(* An if/else in the source, for every outcome: the condition's error,
   a condition that is not a bool (a type error), or the branch the
   condition selects run in a fresh scope, which is popped after it
   whatever its outcome; its declarations are new to the scopes below. *)
Theorem eval_stmt_if_all[local]:
  !cx c ss1 ss2 es res es'.
    eval_stmt cx (If c ss1 ss2) es = (res, es') ==>
    ?r1 es1. (do result <- eval_expr cx c; read_result cx result od) es = (r1, es1) /\
      ((?ex. r1 = INR ex /\ res = INR ex /\ es' = es1) \/
       (?tv. r1 = INL tv /\ (!b. tv <> BoolV b) /\
             ?m. res = INR (Error (TypeError m))) \/
       (?b es2 sc rest. r1 = INL (BoolV b) /\
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
  rename1 `switch_BoolV cx raw` >>
  Cases_on `read_result cx raw es1` >> rename1 `_ = (forced, esF)` >>
  `esF = es1` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `forced`
  >- (rename1 `read_result cx raw es1 = (INL tv, es1)` >>
      simp[switch_BoolV_def, bind_def, read_result_empty_scope] >>
      Cases_on `?b. tv = BoolV b`
  >- (
    gvs[] >>
    qabbrev_tac `esA = es1 with scopes := FEMPTY :: es1.scopes` >>
    Cases_on `eval_stmts cx (if b then ss1 else ss2) esA` >>
    rename1 `_ = (r2, es2)` >>
    `(if BoolV b = BoolV T then eval_stmts cx ss1
      else if BoolV b = BoolV F then eval_stmts cx ss2
      else raise (Error (TypeError "not BoolV"))) esA = (r2, es2)` by
      (Cases_on `b` >> gvs[]) >>
    `es2.scopes <> []` by
      (drule eval_stmts_preserves_scopes_dom >>
       simp[preserves_scopes_dom_def, Abbr `esA`]) >>
    Cases_on `es2.scopes` >> gvs[] >> rename1 `es2.scopes = top2 :: rest2` >>
    `!id. id IN FDOM top2 ==> lookup_scopes id rest2 = NONE` by
      (rpt strip_tac >> drule eval_stmts_new_in_head_not_in_tail >>
       simp[Abbr `esA`]) >>
    Cases_on `r2` >> simp[pop_scope_def, return_def, raise_def]) >>
  `tv <> BoolV T /\ tv <> BoolV F` by metis_tac[] >>
  simp[raise_def, pop_scope_def, return_def] >>
  strip_tac >> disj1_tac >> gvs[] >> metis_tac[]) >>
  simp[switch_BoolV_def, bind_def, read_result_empty_scope,
       raise_def, pop_scope_def, return_def]
QED

(* compile_if_parts (loweringSlice), with where the code ends when both
   branches end their blocks: no exit block follows. *)
Theorem compile_if_parts_all[local]:
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
Theorem if_branch_frag[local]:
  !ctx func cx lctx RetQ cenv ty ss esA res es2 sc rest sa sb sj sx lbl' x
   exit_lbl st' s0.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty ss)
      esA res es2 /\
    compile_stmts cenv lctx ty ss sa = ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    sa.cs_current_insts = [] /\ stmt_res_ok lctx res /\
    stmt_state_rel ctx func cenv cx esA s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = 0 /\
    es2.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
    (~block_is_terminated sb ==>
     emit_inst JMP [Label exit_lbl] [] sb = ((), sj) /\
     new_block lbl' sj = (x, sx) /\ fn_has_code sb sx func /\
     st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []) ==>
    (?s. stmt_lands lctx st' res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb) /\
         stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s /\
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
    rename1 `stmt_state_rel ctx func cenv2 cx es2 s1` >>
    `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s1` by
      (qspecl_then [`func`, `cenv`, `cenv2`, `cx`, `es2`, `s1`, `sc`, `rest`, `ctx`]
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
       (do result <- eval_expr cx c; read_result cx result od) es = (INL (BoolV b), es1) /\
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
      (gvs[] >>
       qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
       simp[bind_def] >> Cases_on `eval_expr cx c es` >>
       rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
       imp_res_tac read_result_no_control >>
       imp_res_tac (cj 1 eval_expr_no_control) >>
       gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
    qspecl_then [`ctx`, `func`, `cx`, `cenv`, `c`, `es`, `r1`, `es1`, `sa`,
                 `cond_op`, `s1`, `s4`, `s5`, `then_lbl`, `else_lbl`, `s0`]
      mp_tac cond_jump_frag >>
    impl_tac >- fs[] >> strip_tac >> fs[] >>
    disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >> disj1_tac >>
    metis_tac[expr_exit_INR_type])
  >- gvs[stmt_res_ok_def] >>
  (* the branch the condition selects *)
  fs[] >>
  qspecl_then [`ctx`, `func`, `cx`, `cenv`, `c`, `es`,
               `INL (BoolV b)`, `es1`, `sa`, `cond_op`, `s1`, `s4`,
               `s5`, `then_lbl`, `else_lbl`, `s0`] mp_tac cond_jump_frag >>
  impl_tac >- fs[expr_res_ok_def] >>
  strip_tac >> fs[] >>
  rename1 `stmt_state_rel ctx func cenv cx es1 sv` >>
  rename1 `jump_to (if bj then then_lbl else else_lbl) sv` >>
  `!st l. sa.cs_next_var <= st.cs_next_var ==>
          ret_pc_ok cenv st (jump_to l sv)` by
    (rpt strip_tac >> REWRITE_TAC [ret_pc_ok_jump_to] >>
     qspecl_then [`cenv`, `cenv`, `sa`, `st`, `s0`, `sv`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var` by
    decide_tac >>
  Cases_on `b` >> fs[] >|
  [qpat_x_assum `bj` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQT_INTRO th])) >>
   qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty`, `ss1`,
                `es1 with scopes := FEMPTY::es1.scopes`, `res`, `es2`, `sc`,
                `rest`, `s6`, `s7`, `s8`, `s9`, `else_lbl`, `x8`, `exit_lbl`,
                `sb`, `jump_to then_lbl sv`] mp_tac if_branch_frag,
   qpat_x_assum `~bj` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQF_INTRO th])) >>
   qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty`, `ss2`,
                `es1 with scopes := FEMPTY::es1.scopes`, `res`, `es2`, `sc`,
                `rest`, `s9`, `s10`, `s11`, `sb`, `exit_lbl`,
                `s11.cs_current_bb`, `exit_lbl`, `sb`, `jump_to else_lbl sv`]
     mp_tac if_branch_frag] >>
  (* the two branches go the same way from here *)
  (impl_tac
    >- (rpt conj_tac >>
        fs[stmt_state_rel_jump_to, stmt_state_rel_push_scope, jump_to_def]
        >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[]) >>
        strip_tac >>
        qpat_x_assum `_ \/ _ ==> ?x11. _` mp_tac >> fs[] >> strip_tac >>
        imp_res_tac new_block_props >> fs[]) >>
    strip_tac
    >- (
      disj1_tac >>
      rename1 `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) sz` >>
      qexistsl_tac [`sz`, `cenv`] >> fs[cenv_top_ext_refl] >> rpt conj_tac
      >- (strip_tac >> fs[] >>
          `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
          imp_res_tac new_block_props >> fs[block_is_terminated_def])
      >- (rpt strip_tac >>
          `lookup_var x sv = SOME w` by res_tac >>
          qpat_x_assum
            `!x w. not_fresh_at _ x /\ lookup_var x (jump_to _ sv) = SOME w ==> _`
            irule >>
          fs[lookup_var_def, jump_to_def] >>
          irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> fs[])
      >- (rpt strip_tac >> res_tac >>
          qpat_x_assum
            `!aid b. FLOOKUP (jump_to _ sv).vs_allocas aid = SOME b ==> _` irule >>
          fs[jump_to_def]) >>
      rpt strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func sz <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >> impl_tac >- fs[] >> strip_tac >>
      qpat_x_assum
        `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
    disj2_tac >>
    qpat_x_assum
      `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
      (qspec_then `fuel` mp_tac) >>
    impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
    qexists_tac `fuel'` >> gvs[])
QED

(* ===== Raise and Assert ===== *)

(* An emitted instruction that aborts where the run reaches it exits as
   the source outcome allows. *)
Theorem emit_abort_exit[local]:
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

Theorem step_revert_zero[local]:
  !id s.
    ?s'. step_inst_base (mk_inst id REVERT [Lit 0w; Lit 0w] []) s =
         Abort Revert_abort s'
Proof
  rpt gen_tac >> simp[venomInstTheory.mk_inst_def] >>
  irule_at Any step_revert_behavior >> simp[eval_operand_def]
QED

Theorem step_invalid[local]:
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
    drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
    disch_then (qspec_then `lctx` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    rename1 `(do raw <- eval_expr cx e; read_result cx raw od) es = (r1,es1)` >>
    qspecl_then [`ctx`, `func`, `cx`, `cenv`, `e`, `es`, `r1`, `es1`, `sa`,
                 `op`, `s1`, `s3`, `s4`, `ok`, `fl`, `s0`] mp_tac cond_jump_frag >>
    impl_tac >- fs[] >> strip_tac
    >- (
      Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def]
      >- (
        (* the condition holds: the ok block, where the code ends *)
        disj1_tac >> rename1 `stmt_state_rel ctx func cenv cx es' sv` >>
        qexists_tac `jump_to s7.cs_current_bb sv` >>
        gvs[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
            block_is_terminated_def] >>
        simp[jump_to_def, lookup_var_def] >> fs[lookup_var_def, jump_to_def]) >>
      (* it fails: the fail block aborts *)
      disj2_tac >> rename1 `stmt_state_rel ctx func cenv cx es' sv` >>
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
    metis_tac[expr_exit_INR_type])
QED

(* Integrity gate for forced condition consumers and their semantic boundary. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "IF_FORCE_AUDIT OK\n"
     else raise Fail "forced condition inherited admission"
  end) [eval_expr_switch_forced, eval_assert_forced_parts,
        eval_assert_forced_ok, cond_jump_frag, eval_stmt_if_all,
        compile_if_stmt_frag, compile_raise_frag, compile_assert_frag];
