(* Memory-safe conditional and direct control statements. *)
Theory stmtControlMemory
Ancestors
  bodyMemoryDefs stmtSimIf stmtSim fragExecMem exprSim exprSimHyps
  exprLoweringProps stmtLowering compileEnv venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem vyperState list finite_map
  fragExec memSafeRun venomInst emitHelperProps instMemFrontier venomExecProofs
Libs
  monadsyntax

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
