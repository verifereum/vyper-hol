(* The constructor body with the pointer ghost, in the deployment's dead
 * bytes and bound: from the body start s0 with deploy_ptr_inv and the body's
 * ghost invariant at (deploy_dead, imm_len), given that every return's exit
 * block (unlock and epilogue) halts pointer-safely, the body either falls
 * off its end at sb with both invariants, pointer safety from there giving
 * it from s0, or exits pointer-safely from s0.  The deploy counterpart of
 * body_stmts_sim_ptr: the (D, lo) body induction body_stmts_sim_ptr_at at
 * deploy's dead bytes and bound, with the constructor's returns lowered to
 * a jump into the exit block (constructor_frame_ret_ok_ptr).
 * TOP-LEVEL: deploy_ctor_body_ptr.
 *)
Theory ctorDeployMemoryRunPtrBody
Ancestors
  ctorDeployMemoryRunPtrDefs ctorDeployMemoryRunPtrFallthrough
  ctorDeployLoweringDefs ctorDeployLoweringFrame ctorDeployLoweringEntry
  ctorDeployLoweringSource ctorDeployLoweringSourceOk ctorDeployShape
  ctorDeployDefs o1PipelineCorrect
  bodySimPtrMainAt bodyPtrDefs bodySim bodyAbiDecodeTarget
  fragGasSeqPtr fragGasPathPtr gasPathPtrExec ptrSafeRun ptrDiscipline
  fragExec stmtSimDefs stmtSimProps loweringPosts gasSummary gasContext
  gasExemptCert exprSimDefs exprLoweringProps e2eDeployDefs
  immutableDeployExecution loweringHalt moduleLowering stmtLowering
  emitHelper compileEnv venomExecSemantics venomInst venomState gasCount
  vyperInterpreter vyperContext vyperTypeSystem vyperState list rich_list

val _ = Parse.hide "body";

(* The constructor's Return NONE: a jump into the exit block, whose run
   (the theorem's premise) halts pointer-safely; as a counted path, zero
   GAS reads, since the exit block is the unlock's TSTORE and the epilogue's
   ALLOCA, ADD, MCOPY, CODECOPY and RETURN. *)
Theorem constructor_return_none_frag_ptr:
  cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
  cenv.ce_ctor_exit_label = SOME exit_lbl /\ same_frame cenv body_cenv /\
  st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
    st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ (nr ==> ut) /\
  (imm_len tops <> 0 ==> cenv.ce_imm_alloca = SOME imm) /\
  (imm_len tops = 0 ==> imm = Lit 0w) /\
  cx_tops cx = tops /\
  (!body_cenv ee s G tn.
     same_frame cenv body_cenv /\
     stmt_state_rel ctx func body_cenv cx ee s /\
     ~s.vs_halted /\ s.vs_current_bb = st_exit.cs_current_bb /\
     s.vs_inst_idx = 0 /\
     deploy_ptr_inv tops runtime_bc am tx imm G tn s ==>
     ?fuel final.
       run_from fuel ctx func s = Halt final /\
       ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
         ctx func [] G tn s) ==>
  stmt_frag_ptr_at (deploy_dead tops runtime_bc am tx) (imm_len tops) NONE
    ctx [] func cx lctx (\v es gt r. T) body_cenv
    (stmt_env body_cenv lctx NoneT (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >>
  `body_cenv.ce_is_ctor /\ body_cenv.ce_return_pc = NONE /\
   body_cenv.ce_ctor_exit_label = SOME exit_lbl /\
   body_cenv.ce_imm_alloca = cenv.ce_imm_alloca` by
    gvs[same_frame_def, compile_env_component_equality] >>
  pure_rewrite_tac[stmt_frag_ptr_at_def] >> rpt gen_tac >> strip_tac >>
  `sb = sa with <|cs_next_id := sa.cs_next_id + 1;
     cs_current_insts := sa.cs_current_insts ++
       [mk_inst sa.cs_next_id JMP [Label exit_lbl] []]|>` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `allocas_from (imm_len tops) s0` by fs[ghost_inv_at_def] >>
  `gas_path_ptr (deploy_dead tops runtime_bc am tx) (imm_len tops) ctx func []
     G0 tn0 s0 0 G0 tn0 (OK (jump_to exit_lbl s0))` by
    (irule emit_jump_path_ptr >> simp[] >>
     qexistsl_tac [`sa`, `sb`] >> simp[]) >>
  `stmt_state_rel ctx func body_cenv cx es (jump_to exit_lbl s0)` by
    simp[stmt_state_rel_jump_to] >>
  `~(jump_to exit_lbl s0).vs_halted /\
   (jump_to exit_lbl s0).vs_current_bb = st_exit.cs_current_bb /\
   (jump_to exit_lbl s0).vs_inst_idx = 0` by simp[jump_to_def] >>
  `deploy_ptr_inv tops runtime_bc am tx imm G0 tn0 (jump_to exit_lbl s0)` by
    (simp[deploy_ptr_inv_jump_to] >> irule ghost_inv_at_deploy_ptr_inv >>
     simp[] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  (* the exit block's code: the unlock, then the epilogue to its RETURN *)
  drule optional_unlock_code >> simp[] >> strip_tac >>
  `~block_is_terminated st_epilogue` by
    (Cases_on `nr` >>
     gvs[block_is_terminated_def, mk_inst_def, is_terminator_def]) >>
  drule_all compile_constructor_epilogue_append >> strip_tac >>
  drule compile_constructor_epilogue_terminal_shape >> strip_tac >>
  `?bb. lookup_block exit_lbl func.fn_blocks = SOME bb /\
        isPREFIX st_final.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> Cases_on `nr` >> gvs[] >> metis_tac[]) >>
  `?pre'. st_final.cs_current_insts = pre' ++ [mk_inst id RETURN [dst; szop] []] /\
          EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                     ~is_terminator i.inst_opcode) pre'` by
    (Cases_on `nr` >> gvs[] >> simp[is_terminator_def] >>
     fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  `?G' tn'. gas_path_ptr (deploy_dead tops runtime_bc am tx) (imm_len tops)
              ctx func [] G0 tn0 (jump_to exit_lbl s0) 0 G' tn' (Halt final)` by
    (irule halting_tail_gas_path_ptr >> simp[mk_inst_def] >>
     conj_tac
     >- (qexistsl_tac [`pre'`, `mk_inst id RETURN [dst; szop] []`] >>
         conj_tac >- simp[mk_inst_def] >>
         conj_tac >- simp[] >>
         metis_tac[]) >>
     qexists_tac `fuel` >> simp[]) >>
  `gas_path_ptr (deploy_dead tops runtime_bc am tx) (imm_len tops) ctx func []
     G0 tn0 s0 (0 + 0) G' tn' (Halt final)` by
    (irule gas_path_ptr_then >> metis_tac[]) >>
  fs[] >>
  pure_rewrite_tac[gas_outcome_ptr_lo_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_ptr_lo_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `G'`, `tn'`,
                `Halt final`] >>
  simp[Once evaluate_def, stmt_exit_def, exit_result_def,
       vyperStateTheory.raise_def, stmt_exit_ptr_def]
QED

Theorem constructor_frame_ret_ok_ptr:
  !ctx func cenv cx tops runtime_bc am tx imm nr nkey ut exit_lbl
   st_exit st_epilogue st_final.
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    cenv.ce_ctor_exit_label = SOME exit_lbl /\
    st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
    (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
    compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_epilogue = ((), st_final) /\
    fn_has_code st_exit st_final func /\ (nr ==> ut) /\
    (imm_len tops <> 0 ==> cenv.ce_imm_alloca = SOME imm) /\
    (imm_len tops = 0 ==> imm = Lit 0w) /\
    cx_tops cx = tops /\
    (!body_cenv ee s G tn.
       same_frame cenv body_cenv /\
       stmt_state_rel ctx func body_cenv cx ee s /\
       ~s.vs_halted /\ s.vs_current_bb = st_exit.cs_current_bb /\
       s.vs_inst_idx = 0 /\
       deploy_ptr_inv tops runtime_bc am tx imm G tn s ==>
       ?fuel final.
         run_from fuel ctx func s = Halt final /\
         ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
           ctx func [] G tn s) ==>
    frame_ret_ok_ptr_at (deploy_dead tops runtime_bc am tx) (imm_len tops)
      NONE ctx [] func cx (\v es gt r. T) cenv NoneT
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[frame_ret_ok_ptr_at_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- (irule constructor_return_none_frag_ptr >> simp[] >>
      qexistsl_tac [`cenv`, `imm`, `nkey`, `nr`, `st_epilogue`, `st_exit`,
                    `st_final`, `ut`] >>
      simp[] >> gvs[]) >>
  gvs[vyperTypeSystemTheory.type_stmt_def]
QED

Theorem deploy_ctor_body_ptr:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 s0 G0 tn0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    stmt_state_rel dunit.cu_context func cenv
      (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
    s0.vs_gas_readings = vs.vs_gas_readings /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    deploy_ptr_inv tops runtime_bc am tx imm G0 tn0 s0 /\
    ghost_inv_at (deploy_dead tops runtime_bc am tx) (imm_len tops) NONE cenv
      (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes) G0 tn0 s0 /\
    (!body_cenv ee s G tn.
       same_frame cenv body_cenv /\
       stmt_state_rel dunit.cu_context func body_cenv
         (deploy_evaluation_context tops am tx) ee s /\
       ~s.vs_halted /\ s.vs_current_bb = st_exit.cs_current_bb /\
       s.vs_inst_idx = 0 /\
       deploy_ptr_inv tops runtime_bc am tx imm G tn s ==>
       ?fuel final.
         run_from fuel dunit.cu_context func s = Halt final /\
         ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
           dunit.cu_context func [] G tn s) ==>
    (?s G tn cenv' ee.
       ~s.vs_halted /\ ~block_is_terminated sb /\
       s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts /\
       cenv_top_ext cenv cenv' ee.scopes /\
       stmt_state_rel dunit.cu_context func cenv'
         (deploy_evaluation_context tops am tx) ee s /\
       deploy_ptr_inv tops runtime_bc am tx imm G tn s /\
       ghost_inv_at (deploy_dead tops runtime_bc am tx) (imm_len tops) NONE
         cenv' (deploy_evaluation_context tops am tx) ee G tn s /\
       !fuel r. run_from fuel dunit.cu_context func s = r /\
                (!e. r <> Error e) ==>
         ?fuel'. run_from fuel' dunit.cu_context func s0 = r /\
           (ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
              fuel dunit.cu_context func [] G tn s ==>
            ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
              fuel' dunit.cu_context func [] G0 tn0 s0)) \/
    (?fuel r. run_from fuel dunit.cu_context func s0 = r /\ exit_result r /\
              ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
                fuel dunit.cu_context func [] G0 tn0 s0)
Proof
  rpt gen_tac >> strip_tac >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `local_ptrs_reserved cenv sa /\ ~block_is_terminated sa` by
    (drule_all deploy_ctor_entry_reaches_body >> strip_tac >> simp[]) >>
  `call_outcomes_ok am tx (MAP SND (call_trace es))` by
    fs[deploy_state_rel_def] >>
  drule_all deploy_ctor_body_frame >> strip_tac >>
  `cenv.ce_return_buf = NONE` by metis_tac[deploy_ctor_return_buf] >>
  `~ctx_has_dalloca dunit.cu_context` by
    (drule_all ctorDeployShapeTheory.deploy_unit_shape_ok >> strip_tac >>
     simp[o1PipelineCorrectTheory.o1_source_unit_ok_no_dalloca]) >>
  `cenv.ce_ctor_exit_label = SOME exit_lbl /\
   st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
   (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
     st_exit = ((), st_epilogue) /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
     st_epilogue = ((), st_final) /\
   fn_has_code st_exit st_final func /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\
   compile_stmts cenv NoLoop NoneT body sa = ((), sb) /\
   (imm_len tops = 0 ==> imm = Lit 0w)` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[deploy_ctor_code_def, new_block_def] >> strip_tac >> gvs[] >>
     strip_tac >> gvs[comp_return_def]) >>
  `?args. lookup_function NONE tx.function_name Deploy tops =
            SOME (mut, nr, args, [], NoneT, body)` by
    (qpat_x_assum `deploy_ctor_start _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [deploy_ctor_start_def]) >>
     metis_tac[]) >>
  `cx_tops (deploy_evaluation_context tops am tx) = tops` by
    (irule cx_tops_module >>
     simp[deploy_evaluation_context_def, initial_evaluation_context_def,
          get_module_code_def]) >>
  qabbrev_tac `cx = deploy_evaluation_context tops am tx` >>
  qabbrev_tac `D = deploy_dead tops runtime_bc am tx` >>
  `dead_lo_ok D (imm_len tops) cenv cx` by
    (simp[dead_lo_ok_def, Abbr `D`, Abbr `cx`, dead_sub_cx_dead_deploy_dead] >>
     simp[deploy_dead_def]) >>
  `frame_ret_ok_ptr_at D (imm_len tops) NONE dunit.cu_context [] func cx
     (\v es gt r. T) cenv NoneT` by
    (qspecl_then [`dunit.cu_context`, `func`, `cenv`, `cx`, `tops`,
                  `runtime_bc`, `am`, `tx`, `imm`, `nr`, `nkey`, `ut`,
                  `exit_lbl`, `st_exit`, `st_epilogue`, `st_final`] mp_tac
       constructor_frame_ret_ok_ptr >>
     impl_tac >- (simp[Abbr `D`] >> gvs[]) >> simp[Abbr `D`]) >>
  `stmt_frag_ptr_at D (imm_len tops) NONE dunit.cu_context [] func cx NoLoop
     (\v es gt r. T) cenv (stmts_env cenv NoLoop NoneT body)
     (eval_stmts cx body) (es0 with outcomes := SOME vs.vs_outcomes)` by
    (qspecl_then [`D`, `imm_len tops`, `NONE`, `[]`, `tops`, `bindings`,
                  `dunit.cu_context`, `func`, `cenv`, `cx`, `env_t`, `env'`,
                  `NoneT`, `NoLoop`, `\v es gt r. T`, `body`,
                  `es0 with outcomes := SOME vs.vs_outcomes`]
       mp_tac body_stmts_sim_ptr_at >>
     impl_tac >- (simp[] >> metis_tac[lookup_function_abi_decode_target_occurs]) >>
     simp[]) >>
  `!gs res ee.
     eval_stmts cx body
       (es0 with <| gas_obs := gs; outcomes := SOME vs.vs_outcomes |>) =
       (res, ee) ==> stmt_res_ok NoLoop res` by
    (simp[Abbr `cx`] >>
     metis_tac[SIMP_RULE (srw_ss()) [] deploy_ctor_body_source_ok]) >>
  `SND (stmts_env cenv NoLoop NoneT body sa) = sb` by
    metis_tac[compile_stmts_env, pairTheory.PAIR_EQ] >>
  Cases_on `stmts_env cenv NoLoop NoneT body sa` >> fs[] >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  rename1 `stmts_env _ _ _ _ _ = (cenv', sb)` >>
  qpat_x_assum `stmt_frag_ptr_at _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [stmt_frag_ptr_at_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `G0`, `tn0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (simp[ret_pc_ok_def, gas_admissible_def] >> metis_tac[]) >>
  simp[gas_outcome_ptr_lo_def] >> strip_tac
  >- ((* the body runs along a pointer-checked path *)
      qpat_x_assum `gas_summary_ptr_lo _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_ptr_lo_def]) >>
      drule gas_path_ptr_exec >> strip_tac >> gvs[exit_result_def]
      >- ((* the body falls off its end *)
          gvs[stmt_lands_def] >> disj1_tac >>
          qexistsl_tac [`t`, `G`, `tn`, `cenv'`, `es_end with gas_obs := []`] >>
          simp[] >>
          `cenv'.ce_imm_alloca = cenv.ce_imm_alloca` by
            (drule cenv_top_ext_same_frame >> simp[same_frame_def] >>
             strip_tac >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
             simp[]) >>
          conj_tac
          >- (irule ghost_inv_at_deploy_ptr_inv >> simp[Abbr `D`] >>
              metis_tac[]) >>
          metis_tac[]) >>
      (* the body exits *)
      disj2_tac >> metis_tac[]) >>
  (* an exempt error: excluded *)
  drule gas_exempt_cert_execution >> strip_tac >>
  qabbrev_tac `gx = gas_explicit marks s0.vs_gas_readings` >>
  `?ee'. eval_stmts cx body
           (es0 with <| gas_obs := gx; outcomes := SOME vs.vs_outcomes |>) =
         (INR (Error err), ee')` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def] >>
     Cases_on `eval_stmts cx body
                 (es0 with <| outcomes := SOME vs.vs_outcomes; gas_obs := gx |>)` >>
     Cases_on `q` >> simp[]) >>
  `load_contract NONE gx am tx [(NONE, tops)] [] =
     deploy_ctor_finish tops tx cx nr mut am_c (INR (Error err)) ee'` by
    (qspecl_then [`tops`, `am`, `tx`, `mut`, `nr`, `body`, `am_c`, `es0`,
                  `gx`, `SOME vs.vs_outcomes`, `INR (Error err)`, `ee'`]
       mp_tac deploy_ctor_source_run >>
     impl_tac >- fs[Abbr `cx`] >> simp[Abbr `cx`]) >>
  qpat_x_assum `!marks. ~deploy_source_exempt _ _` (qspec_then `marks` mp_tac) >>
  `gas_explicit marks vs.vs_gas_readings = gx` by
    (qpat_assum `s0.vs_gas_readings = _` (fn th => simp[Abbr `gx`, th])) >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  gvs[deploy_ctor_finish_def, deploy_source_exempt_def]
QED
