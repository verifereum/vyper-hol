(* Constructor lowering correctness (deploy S1): load_contract against a run of
 * the raw deployment unit from the creation frame's entry state, up to the
 * gas readings the O1 pipeline may vary. The source reads msg.gas from the
 * readings the Venom run consumes (gas_explicit marks vs.vs_gas_readings).
 * TOP-LEVEL: deploy_unit_execution_correct (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployLowering
Ancestors
  ctorDeployDefs o1PassContract gasSummary ctorDeployLoweringDefs
  ctorDeployLoweringNoCtor ctorDeployLoweringCode ctorDeployLoweringPrefix
  ctorDeployLoweringSource ctorDeployLoweringSourceOk ctorDeployLoweringEntry
  ctorDeployLoweringFrame ctorDeployLoweringFallthrough
  ctorDeployLoweringReturn ctorDeployLoweringHaltCode
  ctorDeployLoweringFrameRet ctorReturnFrame bodySimMain bodyAbiDecodeTarget stmtSimDefs stmtSimProps
  loweringPosts gasOutcome gasContext gasExemptCert fragGasMode fragGasPath
  fragExec exprSimDefs compileEnv e2eDeployDefs vyperContext vyperInterpreter

val _ = Parse.hide "body";

Theorem deploy_cx_tops[local]:
  cx_tops (deploy_evaluation_context tops am tx) = tops
Proof
  irule cx_tops_module >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def,
       get_module_code_def]
QED

Theorem deploy_expr_exit_result[local]:
  expr_exit (INR e : unit + exception) r ==>
  deploy_venom_result_rel tops runtime_bc tx (INR e) r
Proof
  Cases_on `r` >> simp[expr_exit_def] >>
  Cases_on `e` >> simp[expr_exit_def, deploy_venom_result_rel_def] >>
  rw[] >> simp[]
QED

Theorem deploy_ctor_code_facts[local]:
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
     st_epilogue, st_final, func) ==>
  cenv.ce_ctor_exit_label = SOME exit_lbl /\
  st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
    st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\
  compile_stmts cenv NoLoop NoneT body sa = ((), sb)
Proof
  simp[deploy_ctor_code_def, new_block_def] >> strip_tac >> gvs[]
QED

Theorem deploy_unit_execution_correct:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es)
    ==>
    ?marks.
      deploy_source_exempt tops
        (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
           [(NONE, tops)] []) \/
      ?fuel. deploy_venom_result_rel tops runtime_bc tx
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])
               (run_context fuel dunit.cu_context vs)
Proof
  rpt strip_tac >>
  `?exts ints fb cfo. classify_functions tops = (exts, ints, fb, cfo)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  Cases_on `cfo`
  >- (drule_all deploy_no_ctor_correct >> simp[]) >>
  drule_all deploy_ctor_code_exists >> strip_tac >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  reverse (Cases_on `?mut nr' body' am_c es0.
                       deploy_ctor_start tops am tx (mut, nr', body', am_c, es0)`)
  >- (fs[] >> drule_all deploy_ctor_prefix_fail >> strip_tac >>
      qexists_tac `[]` >> disj2_tac >> qexists_tac `fuel` >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule_all deploy_ctor_entry_reaches_body >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `call_outcomes_ok am tx (MAP SND (call_trace es))` by
    fs[deploy_state_rel_def] >>
  drule_all deploy_ctor_body_frame >> strip_tac >>
  drule deploy_ctor_code_facts >> strip_tac >>
  `?args. lookup_function NONE tx.function_name Deploy tops =
            SOME (mut, nr, args, [], NoneT, body)` by
    (qpat_x_assum `deploy_ctor_start _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [deploy_ctor_start_def]) >>
     metis_tac[]) >>
  qabbrev_tac `cx = deploy_evaluation_context tops am tx` >>
  qabbrev_tac `RetQ = constructor_return_q func cenv cx (LENGTH runtime_bc)
                        (imm_len tops) nr nkey` >>
  `frame_ret_ok dunit.cu_context func cx RetQ cenv NoneT` by
    (qspecl_then [`dunit.cu_context`, `func`, `cenv`, `cx`, `LENGTH runtime_bc`,
                  `imm_len tops`, `imm`, `nr`, `nkey`, `ut`, `exit_lbl`,
                  `st_exit`, `st_epilogue`, `st_final`] mp_tac
       constructor_frame_ret_ok >>
     impl_tac >- simp[] >> simp[Abbr `RetQ`]) >>
  `stmt_frag dunit.cu_context func cx NoLoop RetQ cenv
     (stmts_env cenv NoLoop NoneT body) (eval_stmts cx body)
     (es0 with outcomes := SOME vs.vs_outcomes)` by
    (qspecl_then [`tops`, `bindings`, `dunit.cu_context`, `func`, `cenv`, `cx`,
                  `env_t`, `env'`, `NoneT`, `NoLoop`, `RetQ`, `body`,
                  `es0 with outcomes := SOME vs.vs_outcomes`, `ARB`, `ARB`]
       mp_tac body_stmts_sim >>
     impl_tac >- (simp[] >> metis_tac[lookup_function_abi_decode_target_occurs]) >>
     simp[]) >>
  `!gs res ee.
     eval_stmts cx body
       (es0 with <| gas_obs := gs; outcomes := SOME vs.vs_outcomes |>) =
       (res, ee) ==> stmt_res_ok NoLoop res` by
    metis_tac[deploy_ctor_body_source_ok] >>
  `SND (stmts_env cenv NoLoop NoneT body sa) = sb` by
    metis_tac[compile_stmts_env, pairTheory.PAIR_EQ] >>
  Cases_on `stmts_env cenv NoLoop NoneT body sa` >> fs[] >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  rename1 `stmts_env _ _ _ _ _ = (cenv', sb)` >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (simp[ret_pc_ok_def, gas_admissible_def] >> metis_tac[]) >>
  simp[gas_outcome_def] >> strip_tac
  >- ((* the body runs along a target path *)
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
      qabbrev_tac `gx = gas_explicit marks s0.vs_gas_readings` >>
      `eval_stmts cx body
         (es0 with <| gas_obs := gx; outcomes := SOME vs.vs_outcomes |>) =
         (res, es_end with gas_obs := []) /\
       gas_path dunit.cu_context func s0 (LENGTH marks) r` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
         conj_tac
         >- (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
               (qspec_then `[]` mp_tac) >> simp[]) >>
         metis_tac[gas_marked_path_exec]) >>
      qabbrev_tac `es' = es_end with gas_obs := []` >>
      `load_contract NONE gx am tx [(NONE, tops)] [] =
         deploy_ctor_finish tops tx cx nr mut am_c res es'` by
        metis_tac[deploy_ctor_source_run] >>
      qexists_tac `marks` >> disj2_tac >>
      `gas_explicit marks vs.vs_gas_readings = gx` by
        (qpat_assum `s0.vs_gas_readings = _`
           (fn th => simp[Abbr `gx`, th])) >>
      pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
      fs[]
      >- ((* the body falls off its end *)
          gvs[stmt_post_def, stmt_lands_def] >>
          drule_all deploy_ctor_fallthrough >> strip_tac >>
          `?fuel1. run_from fuel1 dunit.cu_context func s0 = Halt final` by
            metis_tac[gas_path_normal, venomExecSemanticsTheory.exec_result_distinct] >>
          `?fuel2. run_context fuel2 dunit.cu_context vs = Halt final` by
            (qpat_x_assum `!fuel. (!e. run_from _ _ _ s0 <> _) ==> _`
               (qspec_then `fuel1` mp_tac) >> simp[]) >>
          drule run_from_halt_code >> strip_tac >>
          qexists_tac `fuel2` >> simp[] >>
          qunabbrev_tac `cx` >> irule deploy_ctor_return >> simp[] >> metis_tac[]) >>
      (* the body exits *)
      drule_all gas_path_exit >> disch_then (qx_choose_then `fuel` assume_tac) >>
      `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
      qpat_x_assum `!fuel. (!e. run_from _ _ _ s0 <> _) ==> _`
        (qspec_then `fuel` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qx_choose_then `fuel2`
                    (fn th => qexists_tac `fuel2` >> SUBST1_TAC th)) >>
      asm_rewrite_tac[] >>
      qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
      simp[stmt_exit_def] >> strip_tac
      >- ((* an error or an assertion *)
          Cases_on `res` >> fs[expr_exit_def] >> rename1 `expr_exit (INR e) _` >>
          `e <> ReturnException NoneV` by
            (strip_tac >> Cases_on `r` >> gvs[expr_exit_def]) >>
          simp[deploy_ctor_finish_def] >> irule deploy_expr_exit_result >>
          first_assum ACCEPT_TAC) >>
      (* a return *)
      `v = NoneV /\ ?final. r = Halt final` by
        fs[Abbr `RetQ`, constructor_return_q_def] >>
      gvs[] >>
      drule run_from_halt_code >> strip_tac >>
      `constructor_return_q func cenv cx (LENGTH runtime_bc) (imm_len tops)
         nr nkey NoneV (es' with scopes := []) (Halt final)` by
        (`es' with <| scopes := []; gas_obs := [] |> = es' with scopes := []` by
           simp[Abbr `es'`] >>
         fs[Abbr `RetQ`]) >>
      qunabbrev_tac `cx` >> irule deploy_ctor_return >> simp[] >> metis_tac[]) >>
  (* the body fails with an exempt error *)
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
    metis_tac[deploy_ctor_source_run] >>
  qexists_tac `marks` >> disj1_tac >>
  `gas_explicit marks vs.vs_gas_readings = gx` by
    (qpat_assum `s0.vs_gas_readings = _`
       (fn th => simp[Abbr `gx`, th])) >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  gvs[deploy_ctor_finish_def, deploy_source_exempt_def, Abbr `cx`,
      deploy_cx_tops]
QED
