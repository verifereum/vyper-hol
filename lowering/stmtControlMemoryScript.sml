(* Memory-safe conditional and direct control statements. *)
Theory stmtControlMemory
Ancestors
  bodyMemoryDefs stmtSimIf stmtSim fragExecMem exprSim exprSimHyps
  exprLoweringProps stmtLowering compileEnv venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem vyperState list finite_map
  fragExec memSafeRun venomInst emitHelperProps instMemFrontier venomExecProofs
  loweringSlice exprLowering emitHelper vyperExprNoControl
  vyperEvalPreservesScopes vyperStatePreservation
Libs
  monadsyntax

Theorem lower_value_bool_grows_mem[local]:
  !cenv e sa op sb.
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt strip_tac >> drule (cj 2 compile_expr_grows) >> simp[]
QED

Theorem eval_assert_forced_parts_mem[local]:
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

Theorem eval_assert_forced_ok_mem[local]:
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
  drule_at Any eval_assert_forced_parts_mem >>
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

Theorem eval_stmt_if_all_mem[local]:
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
      >- (gvs[] >>
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

Theorem compile_if_parts_all_mem[local]:
  !cenv lctx ty c ss1 ss2 st st'.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') ==>
    ?cond_op s1 s4 s5 s6 s7 s8 s9 s10 s11 then_lbl else_lbl exit_lbl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      cs_extends s1 s4 /\ s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      s4.cs_next_var = s1.cs_next_var /\
      emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] s4 = ((), s5) /\
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
  rename1 `compile_stmts _ _ _ ss2 s9 = ((), s10)` >> strip_tac >>
  rename1 `(if block_is_terminated s10 then _ else _) s10 = ((), s11)` >>
  qexistsl_tac [`s4`, `s5`, `s6`, `s7`, `s8`, `s9`, `s10`, `s11`,
                `then_lbl`, `else_lbl`, `exit_lbl`, `x5`, `x8`] >>
  imp_res_tac fresh_label_props >>
  `cs_extends s1 s4` by
    metis_tac[cs_extends_fresh_label, cs_extends_trans] >>
  Cases_on `block_is_terminated s7` >>
  Cases_on `block_is_terminated s10` >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compile_if_layout_mem[local]:
  !cenv lctx ty c ss1 ss2 sa sb func.
    compile_stmt cenv lctx ty (If c ss1 ss2) sa = ((), sb) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\ fn_has_code sa sb func ==>
    ?op s1 s4 s5 s6 s7 s8 s9 s10 s11 lt lf le x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c sa = (op, s1) /\
      s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      emit_inst JNZ [op; Label lt; Label lf] [] s4 = ((), s5) /\
      new_block lt s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label le] [] s7 = ((), s8)) /\
      new_block lf s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label le] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block le s11 = (x11, sb)) /\
      (block_is_terminated s7 /\ block_is_terminated s10 ==> sb = s11) /\
      fn_has_code sa s1 func /\ fn_has_code s6 s7 func /\
      fn_has_code s9 s10 func /\ fn_has_code s7 s9 func /\
      fn_has_code s10 sb func /\
      lookup_block s5.cs_current_bb func.fn_blocks =
        SOME <| bb_label := s5.cs_current_bb;
                bb_instructions := s5.cs_current_insts |> /\
      cs_extends sa s6 /\ cs_extends sa s9 /\
      sa.cs_next_var <= s6.cs_next_var /\
      s6.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_var <= s9.cs_next_var /\
      s9.cs_next_var <= sb.cs_next_var
Proof
  rpt strip_tac >> drule compile_if_parts_all_mem >> strip_tac >>
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
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends s7 s8 /\ s7.cs_next_var = s8.cs_next_var /\
   cs_extends s10 s11 /\ s10.cs_next_var = s11.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s8 s9` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `cs_extends s11 sb /\ s11.cs_next_var = sb.cs_next_var` by
    (Cases_on `block_is_terminated s7 /\ block_is_terminated s10`
     >- (fs[] >> simp[cs_extends_refl]) >>
     `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
     metis_tac[cs_extends_new_block, new_block_props]) >>
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
  qexistsl_tac [`cond_op`, `s1`, `s4`, `s5`, `s6`, `s7`, `s8`, `s9`,
                `s10`, `s11`, `then_lbl`, `else_lbl`, `exit_lbl`, `x5`, `x8`] >>
  simp[] >> metis_tac[cs_extends_trans]
QED

Theorem run_from_jump_result_mem[local]:
  !fuel ctx fn s bb inst lbl r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    inst_mem_below_frontier inst s /\
    run_from fuel ctx fn (jump_to lbl s) = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn (jump_to lbl s) ==>
       mem_safe_run fuel' ctx fn s)
Proof
  rpt strip_tac >> qexists_tac `SUC fuel` >> conj_tac
  >- (irule run_from_jump_result >> metis_tac[]) >>
  strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- gvs[run_from_def, jump_to_def] >>
  rename1 `lookup_block lbl _ = SOME bb'` >>
  Cases_on `phi_prefix_length bb'.bb_instructions = 0`
  >- (`eval_phis (jump_to lbl s) bb'.bb_instructions = OK (jump_to lbl s)` by
        (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
         rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >>
         gvs[phi_prefix_length_def, eval_phis_def]) >>
      simp[mem_safe_run_def, Once mem_safe_block_def,
           mem_safe_step_non_invoke, step_inst_non_invoke,
           Once exec_block_def, jump_to_def] >>
      mp_tac mem_safe_blocks_run >>
      disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `jump_to lbl s`,
                             `bb'`, `jump_to lbl s`] mp_tac) >>
      simp[jump_to_def] >> gvs[jump_to_def]) >>
  `?phi rest. bb'.bb_instructions = phi :: rest /\ phi.inst_opcode = PHI` by
    (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
     rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
  simp[run_from_def, jump_to_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def]
QED

Theorem run_from_jump_end_mem[local]:
  !ctx func sa sb ss inst lbl.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
    fn_has_code sa sb func /\
    ss.vs_current_bb = sa.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sa.cs_current_insts /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst ss = OK (jump_to lbl ss) /\ ~ss.vs_halted /\
    inst_mem_below_frontier inst ss ==>
    !fuel r. run_from fuel ctx func (jump_to lbl ss) = r /\
      (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ss = r /\
        (mem_safe_run fuel ctx func (jump_to lbl ss) ==>
         mem_safe_run fuel' ctx func ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> irule run_from_jump_result_mem >> gvs[] >> metis_tac[]
QED

Theorem emit_abort_exit_mem[local]:
  !ctx func opc ops st st' s0 RetQ es' res.
    emit_inst opc ops [] st = ((), st') /\ fn_has_code st st' func /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s0.vs_halted /\
    opc <> INVOKE /\ inst_mem_below_frontier (mk_inst st.cs_next_id opc ops []) s0 /\
    (?a s'. step_inst_base (mk_inst st.cs_next_id opc ops []) s0 =
              Abort a s' /\ expr_exit res (Abort a s')) ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             stmt_exit RetQ es' res r /\ mem_safe_run fuel ctx func s0
Proof
  rpt strip_tac >> drule emit_inst_extends >> strip_tac >>
  `frag_exec_mem ctx st st' (\s. s = s0) (\s. F) (stmt_exit RetQ es' res)` by
    (irule frag_exec_mem_step_abort >> fs[] >> qexists_tac `0` >>
     fs[step_inst_non_invoke, mk_inst_def, stmt_exit_def,
        mem_safe_step_non_invoke]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >> simp[frag_exec_mem_def]
QED

Theorem control_abort_frontier[local]:
  !id s.
    inst_mem_below_frontier (mk_inst id REVERT [Lit 0w; Lit 0w] []) s /\
    inst_mem_below_frontier (mk_inst id INVALID [] []) s
Proof
  rpt gen_tac >> conj_tac
  >- simp[below_frontier_REVERT, eval_operand_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem step_revert_zero_mem[local]:
  !id s.
    ?s'. step_inst_base (mk_inst id REVERT [Lit 0w; Lit 0w] []) s =
         Abort Revert_abort s'
Proof
  rpt gen_tac >> simp[mk_inst_def] >>
  irule_at Any step_revert_behavior >> simp[eval_operand_def]
QED

Theorem step_invalid_mem[local]:
  !id s.
    ?s'. step_inst_base (mk_inst id INVALID [] []) s = Abort ExHalt_abort s'
Proof
  simp[mk_inst_def, step_inst_base_def]
QED

Theorem compile_break_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break) es (INR BreakException) es
Proof
  rw[stmt_frag_mem_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  disj1_tac >> qexistsl_tac [`jump_to ex s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  `return_buf_frame d cenv sj (jump_to ex s0)` by
    (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `!fuel r. run_from fuel ctx func (jump_to ex s0) = r /\
       (!e. r <> Error e) ==>
       ?fuel'. run_from fuel' ctx func s0 = r /\
         (mem_safe_run fuel ctx func (jump_to ex s0) ==>
          mem_safe_run fuel' ctx func s0)` by
    (match_mp_tac run_from_jump_end_mem >>
     qexistsl_tac [`sa`, `sj`, `mk_inst sa.cs_next_id JMP [Label ex] []`] >>
     simp[mk_inst_def, is_terminator_def, step_jmp_behavior] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to] >>
  simp[jump_to_def, lookup_var_def] >> metis_tac[]
QED

Theorem compile_continue_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue) es (INR ContinueException)
      es
Proof
  rw[stmt_frag_mem_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  disj1_tac >> qexistsl_tac [`jump_to inc s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  `return_buf_frame d cenv sj (jump_to inc s0)` by
    (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `!fuel r. run_from fuel ctx func (jump_to inc s0) = r /\
       (!e. r <> Error e) ==>
       ?fuel'. run_from fuel' ctx func s0 = r /\
         (mem_safe_run fuel ctx func (jump_to inc s0) ==>
          mem_safe_run fuel' ctx func s0)` by
    (match_mp_tac run_from_jump_end_mem >>
     qexistsl_tac [`sa`, `sj`, `mk_inst sa.cs_next_id JMP [Label inc] []`] >>
     simp[mk_inst_def, is_terminator_def, step_jmp_behavior] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to] >>
  simp[jump_to_def, lookup_var_def] >> metis_tac[]
QED

Theorem compile_if_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty c ss1 ss2 es res es'.
    eval_stmt cx (If c ss1 ss2) es = (res, es') /\
    expr_type c = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!b es1 res2 es2.
       (do result <- eval_expr cx c; read_result cx result od) es = (INL (BoolV b), es1) /\
       eval_stmts cx (if b then ss1 else ss2)
         (es1 with scopes := FEMPTY :: es1.scopes) = (res2, es2) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes) res2 es2) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      es res es'
Proof
  cheat
QED

Theorem compile_raise_frag_mem:
  !d ctx func cx lctx RetQ cenv ty rk es res es'.
    (rk = RaiseBare \/ rk = RaiseUnreachable) /\
    eval_stmt cx (Raise rk) es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_abort_exit_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `s0`, `RetQ`, `es'`, `res`] mp_tac) >>
  (impl_tac
   >- (fs[markerTheory.Abbrev_def] >>
       qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, raise_def] >> strip_tac >>
       gvs[expr_exit_def, control_abort_frontier] >>
       metis_tac[step_revert_zero_mem, step_invalid_mem])) >>
  metis_tac[]
QED

Theorem compile_assert_frag_mem:
  !d ctx func cx lctx RetQ cenv ty e ak es res es'.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      es res es'
Proof
  cheat
QED
