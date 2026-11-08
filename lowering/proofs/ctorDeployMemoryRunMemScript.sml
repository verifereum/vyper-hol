(* The raw deployment unit's run is memory-safe: every instruction it
 * executes, callee frames included, reads and writes memory below the
 * allocation frontier (or is a revert forwarding).  The deploy twin of
 * lower_vyper_runtime_unit_run_mem_safe, composed like the constructor's S1
 * (ctorDeployLowering): without a constructor (RunMemNoCtor); a source that
 * fails before the body (RunMemPrefix); otherwise the prefix reaches the body
 * start (RunMemEntry), the body runs by body_stmts_sim_mem, whose body_inv
 * (S1's deploy_ctor_body_frame) covers the constructor's internal callees,
 * and it either returns (RunMemFrameRet) or falls off its end
 * (RunMemFallthrough) into the unlock and the epilogue.  An exempt source
 * error contradicts the excluded exemption.  The body frame's call outcomes
 * come from deploy_state_rel.
 * TOP-LEVEL: deploy_unit_run_mem_safe.
 *)
Theory ctorDeployMemoryRunMem
Ancestors
  ctorDeployDefs gasSummary memSafeRun venomInst
  ctorDeployLoweringDefs ctorDeployLoweringCode ctorDeployLoweringEntry
  ctorDeployLoweringFrame ctorDeployLoweringSource ctorDeployLoweringSourceOk
  ctorDeployMemoryRunMemNoCtor ctorDeployMemoryRunMemPrefix
  ctorDeployMemoryRunMemEntry ctorDeployMemoryRunMemFrameRet
  ctorDeployMemoryRunMemFallthrough
  bodyMemory bodyAbiDecodeTarget stmtSimDefs stmtSimProps loweringPosts
  gasOutcome gasContext gasExemptCert fragGasMode fragGasPathMem fragExecMem
  fragExec exprSimDefs compileEnv e2eDeployDefs vyperContext vyperInterpreter

val _ = Parse.hide "body";

Theorem deploy_unit_run_mem_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  `?exts ints fb cfo. classify_functions tops = (exts, ints, fb, cfo)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  Cases_on `cfo`
  >- (drule_all deploy_no_ctor_run_mem_safe >> simp[]) >>
  drule_all deploy_ctor_code_exists >> strip_tac >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  reverse (Cases_on `?mut nr' body' am_c es0.
                       deploy_ctor_start tops am tx (mut, nr', body', am_c, es0)`)
  >- (fs[] >> drule_all deploy_ctor_prefix_fail_run_mem_safe >> simp[]) >>
  pop_assum strip_assume_tac >>
  `nr' = nr /\ body' = body /\ local_ptrs_reserved cenv sa /\
   ~block_is_terminated sa` by
    (drule_all deploy_ctor_entry_reaches_body >> strip_tac >> simp[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all deploy_ctor_entry_run_mem >> strip_tac >>
  `call_outcomes_ok am tx (MAP SND (call_trace es))` by
    fs[deploy_state_rel_def] >>
  drule_all deploy_ctor_body_frame >> strip_tac >>
  `cenv.ce_ctor_exit_label = SOME exit_lbl /\
   st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
   (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
     st_exit = ((), st_epilogue) /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
     st_epilogue = ((), st_final) /\
   fn_has_code st_exit st_final func /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\
   compile_stmts cenv NoLoop NoneT body sa = ((), sb)` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[deploy_ctor_code_def, new_block_def] >> strip_tac >> gvs[]) >>
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
  `frame_ret_ok_mem NONE dunit.cu_context func cx (\v es r. T) cenv NoneT` by
    (qspecl_then [`dunit.cu_context`, `func`, `cenv`, `cx`, `LENGTH runtime_bc`,
                  `imm_len tops`, `imm`, `nr`, `nkey`, `ut`, `exit_lbl`,
                  `st_exit`, `st_epilogue`, `st_final`] mp_tac
       constructor_frame_ret_ok_mem >>
     impl_tac >- simp[] >> simp[]) >>
  `stmt_frag_mem NONE dunit.cu_context func cx NoLoop (\v es r. T) cenv
     (stmts_env cenv NoLoop NoneT body) (eval_stmts cx body)
     (es0 with outcomes := SOME vs.vs_outcomes)` by
    (qspecl_then [`NONE`, `tops`, `bindings`, `dunit.cu_context`, `func`,
                  `cenv`, `cx`, `env_t`, `env'`, `NoneT`, `NoLoop`,
                  `\v es r. T`, `body`,
                  `es0 with outcomes := SOME vs.vs_outcomes`]
       mp_tac body_stmts_sim_mem >>
     impl_tac >- (simp[] >> metis_tac[lookup_function_abi_decode_target_occurs]) >>
     simp[]) >>
  `!gs res ee.
     eval_stmts cx body
       (es0 with <| gas_obs := gs; outcomes := SOME vs.vs_outcomes |>) =
       (res, ee) ==> stmt_res_ok NoLoop res` by
    (simp[Abbr `cx`] >>
     metis_tac[SIMP_RULE (srw_ss()) [] deploy_ctor_body_source_ok]) >>
  `SND (stmts_env cenv NoLoop NoneT body sa) = sb` by
    (qpat_x_assum `compile_stmts _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmts_env]) >>
  Cases_on `stmts_env cenv NoLoop NoneT body sa` >> fs[] >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  rename1 `stmts_env _ _ _ _ _ = (cenv', sb)` >>
  qpat_x_assum `(!fuel. mem_safe_run _ _ _ _) ==> _` irule >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (simp[ret_pc_ok_def, gas_admissible_def, return_buf_frame_def] >>
      metis_tac[]) >>
  simp[gas_outcome_def] >> strip_tac
  >- ((* the body runs along a memory-safe target path *)
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
      `gas_path_mem dunit.cu_context func s0 (LENGTH marks) r` by
        FIRST [fs[gas_marked_exec_def, gas_marked_path_def]] >>
      drule gas_path_mem_exec >> strip_tac >> FIRST [fs[exit_result_def]]
      >- ((* the body falls off its end *)
          gvs[stmt_lands_def] >>
          drule_all deploy_ctor_fallthrough_mem_safe >> strip_tac >>
          qpat_x_assum `!fuel. (!e. run_from _ _ _ _ <> Error e) ==> _`
            (qspec_then `fuel` mp_tac) >>
          simp[] >> strip_tac >>
          metis_tac[mem_safe_run_all_fuel]) >>
      (* the body exits *)
      metis_tac[mem_safe_run_all_fuel, exit_result_not_error]) >>
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
