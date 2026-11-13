(*
 * S3 piece: the external frame's returns halt memory-safely (#640).
 * loweringMemCorrect composes S3 from this and the other leaves.
 *)
Theory loweringMemFrameRet
Ancestors
  returnValueTyped
  stmtSimDefs exprSimDefs
  loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect fragExecMem bodyMemoryDefs
  entryHaltMem bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs
  externalReturnFrameMem runFromGasPathMem gasOutcome gasSummary
  gasSummaryCompose gasContext fragGasMode fragGasPath fragGasPathMem
  exprSimMemDefs stmtSimReturn stmtSimProps stmtLoweringMono
  gasStorage vyperStorageTrace vyperStorageFootprint

val _ = Parse.hide "body";

(* ===== The counted contract from run-level return sequences ===== *)

(* A return sequence that exits memory-safely from its start is a counted
   memory path; its steps read no source GAS observation. *)
Theorem return_none_counted_mem[local]:
  (!(H : (bool # bytes32 # type_value) list # num list) sa sb s0 cenv''.
     stmt_env cenv lctx ty (Return NONE) sa = (cenv'', sb) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
     stmt_state_rel H ctx func cenv cx es s0 /\ alloca_history func s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
     s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
     ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
              mem_safe_run fuel ctx func s0) ==>
  stmt_frag_mem d ctx func cx lctx (\H v es r. T) cenv
    (stmt_env cenv lctx ty (Return NONE)) (eval_stmt cx (Return NONE)) es
Proof
  rw[stmt_frag_mem_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  first_x_assum (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`H0`, `s0`] mp_tac) >> simp[] >> strip_tac >>
  qspecl_then [`fuel`, `ctx`, `func`, `s0`, `run_from fuel ctx func s0`]
    mp_tac run_from_gas_path_mem >> simp[] >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `REPLICATE n F` >>
  disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `run_from fuel ctx func s0`] >>
  simp[Once evaluate_def, raise_def, stmt_exit_def]
QED

Theorem return_value_raise_exec[local]:
  gas_path_mem ctx func t n r ==>
  gas_marked_exec T (ctx,func)
    (raise (ReturnException v) : evaluation_state -> unit evaluation_result)
    (es_end with gas_obs := [], t) (REPLICATE n F)
    (INR (ReturnException v)) es_end r
Proof
  simp[gas_marked_exec_def, gas_marked_path_def, raise_def]
QED

Theorem eval_return_value_bind[local]:
  eval_stmt cx (Return (SOME e)) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. raise (ReturnException v))
Proof
  simp[FUN_EQ_THM, eval_return_forced] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[]
QED

Theorem return_value_source_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED

(* The value ran out of the storage domain: so does the whole return. *)
val ret_bad_tac =
  qexists_tac `marks` >> disj1_tac >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >> conj_tac
  >- (irule gasStorageTheory.gas_bad_storage_at_counted_prefix >> metis_tac[])
  >- simp[vyperStorageTraceTheory.storage_trace_frame_raise];

(* The value's summary, then the run-level rest of the sequence. *)
Theorem return_value_summary_mem[local]:
  gas_summary_at T (ctx,func) marks
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==>
       ?v. res = INL v /\
       expr_post H ctx func cenv cx e es sa s1 s0 ee v op t /\
       expr_store_bound cx (expr_type e) v op t /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_exit res r) /\
  (!(H : (bool # bytes32 # type_value) list # num list) ee v t.
     valid_horizon cx st0 H es.storage_trace /\
     expr_post H ctx func cenv cx e es sa s1 s0 ee v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     (?gs ee'. bind (eval_expr cx e) (read_result cx)
                 (es with gas_obs := gs) = (INL v, ee')) /\
     t.vs_current_bb = s1.cs_current_bb /\
     t.vs_inst_idx = LENGTH s1.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted ==>
     ?fuel r. run_from fuel ctx func t = r /\ exit_result r /\
              mem_safe_run fuel ctx func t) ==>
  !Q. ?marks'.
    gas_bad_storage_at cx st0 (eval_stmt cx (Return (SOME e))) es s0 marks' \/
    gas_summary_at T (ctx,func) marks'
      (eval_stmt cx (Return (SOME e))) (es,s0) Q
      (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
         !tail. stmt_exit (\v es r. T) (ee with gas_obs := tail) res r)
Proof
  strip_tac >> gen_tac >> pure_rewrite_tac[eval_return_value_bind] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`
      >- (`?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
            metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
          qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (qspec_then `H0` mp_tac) >>
          impl_tac >- gs[] >> strip_tac >> gvs[] >>
          `valid_horizon cx st0 H0 es.storage_trace` by
            (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                     gas_marked_exec_valid_prefix)) >>
             impl_tac >- simp[return_value_source_frame] >>
             disch_then (qspecl_then [`cx`, `st0`, `H0`] mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >>
             metis_tac[gas_marked_path_exec, gas_path_normal]) >>
          drule marked_exec_source_eq >> strip_tac >>
          first_x_assum (drule_all o Ho_Rewrite.PURE_REWRITE_RULE [PULL_EXISTS]) >>
          strip_tac >>
          qspecl_then [`fuel`, `ctx`, `func`, `t`, `run_from fuel ctx func t`]
            mp_tac run_from_gas_path_mem >> simp[] >> strip_tac >>
          qexists_tac `marks ++ REPLICATE n F` >> disj2_tac >>
          qexistsl_tac [`INR (ReturnException v)`, `es_end`,
                        `run_from fuel ctx func t`] >>
          simp[stmt_exit_def] >>
          irule gas_marked_exec_bind_normal >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[return_value_raise_exec]) >>
      ret_bad_tac)
  >- (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`
      >- (`?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
            metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
          `?ex. res = INR ex` by
            (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
               (qspec_then `H0` mp_tac) >>
             impl_tac >- gs[] >> strip_tac >>
             Cases_on `res` >> gvs[expr_exit_def]) >>
          gvs[] >>
          qexists_tac `marks` >> disj2_tac >>
          qexistsl_tac [`INR ex`, `es_end`, `r`] >>
          conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
          simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
      ret_bad_tac)
QED

Theorem return_value_counted_mem[local]:
  (!ty'. expr_sim_mem ctx func cenv cx ty' e es /\
         expr_vv_sim_mem ctx func cenv cx ty' e es) /\
  (!sa sb cenv'' op s1.
     stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'', sb) /\
     lower_value compile_expr cenv ty e sa = (op, s1) ==> cs_extends s1 sb) /\
  (!(H : (bool # bytes32 # type_value) list # num list)
    sa sb cenv'' s0 op s1 ee v t.
     stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'', sb) /\
     lower_value compile_expr cenv ty e sa = (op, s1) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
     stmt_state_rel H ctx func cenv cx es s0 /\ alloca_history func s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
     s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
     expr_post H ctx func cenv cx e es sa s1 s0 ee v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     (?gs ee'. bind (eval_expr cx e) (read_result cx)
                 (es with gas_obs := gs) = (INL v, ee')) /\
     (!ty'. expr_sim_mem ctx func cenv cx ty' e es /\
            expr_vv_sim_mem ctx func cenv cx ty' e es) /\
     t.vs_current_bb = s1.cs_current_bb /\
     t.vs_inst_idx = LENGTH s1.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ~t.vs_halted ==>
     ?fuel r. run_from fuel ctx func t = r /\ exit_result r /\
              mem_safe_run fuel ctx func t) ==>
  stmt_frag_mem d ctx func cx lctx (\H v es r. T) cenv
    (stmt_env cenv lctx ty (Return (SOME e))) (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  `cs_extends s1 sb` by metis_tac[] >>
  `cs_extends sa s1` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `expr_sim_mem ctx func cenv cx ty e es` by fs[] >>
  drule (GEN_ALL return_forced_admissible) >> strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      pure_rewrite_tac[eval_return_value_bind] >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> conj_tac
      >- first_assum ACCEPT_TAC
      >- simp[vyperStorageTraceTheory.storage_trace_frame_raise])
  >- (drule return_value_summary_mem >> impl_tac
      >- (map_every qx_gen_tac [`HH`, `ee`, `v`, `t`] >> strip_tac >>
          `stmt_state_rel HH ctx func cenv cx es s0` by metis_tac[] >>
          qpat_x_assum `!H sa sb cenv'' s0 op s1 ee v t. _`
            (qspecl_then [`HH`, `sa`, `sb`, `cenv'`, `s0`, `op`, `s1`, `ee`, `v`, `t`] mp_tac) >>
          asm_rewrite_tac[] >>
          impl_tac >- (qexistsl [`gs`, `ee'`] >> first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC) >>
      strip_tac >>
      qpat_x_assum `!Q. _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule (GEN_ALL return_forced_exempt) >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >> goal_assum (drule_at Any)
QED

(* ===== The frame's returns (#640) ===== *)

(* ADMITTED (#640): external_frame_ret_ok with memory, for any outcome of
   the return: every return sequence halts memory-safely, by entryHaltMem's
   return leaves after the returned expression's memory simulation. *)
Theorem external_frame_ret_ok_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_mem NONE unit.cu_context func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\H v es r. T) cenv ret
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`, `vs`, `mut`,
               `args`, `fbody`, `env`, `lbl`, `cenv0`, `pos_args`, `min_cds`,
               `is_payable`, `nkey`, `ut'`, `iv`, `rt`, `st`, `cenv`, `sa`,
               `func`] mp_tac external_frame_ret_run_mem >>
  asm_rewrite_tac[] >> strip_tac >>
  simp[frame_ret_ok_mem_def] >>
  map_every qx_gen_tac [`cenv'`, `env'`, `lctx`, `eo`, `es`] >> strip_tac >>
  Cases_on `eo`
  >- (irule return_none_counted_mem >>
      map_every qx_gen_tac [`H`, `sa'`, `sb`, `s0`, `cenv''`] >> strip_tac >>
      qpat_x_assum `!H cenv' env lctx es sa sb cenv'' s0. _`
        (qspecl_then [`H`, `cenv'`, `env'`, `lctx`, `es`, `sa'`, `sb`, `cenv''`, `s0`] mp_tac) >>
      asm_rewrite_tac[]) >>
  rename1 `Return (SOME e)` >> match_mp_tac return_value_counted_mem >>
  rpt conj_tac
  >- simp[]
  >- (map_every qx_gen_tac [`sa'`, `sb`, `cenv''`, `op`, `s1`] >> strip_tac >>
      qpat_x_assum `!cenv' lctx e sa sb cenv'' op s1. _`
        (qspecl_then [`cenv'`, `lctx`, `e`, `sa'`, `sb`, `cenv''`, `op`, `s1`] mp_tac) >>
      asm_rewrite_tac[])
  >> map_every qx_gen_tac [`H`, `sa'`, `sb`, `cenv''`, `s0`, `op`, `s1`, `ee`, `v`, `t`] >>
     strip_tac >>
     qpat_x_assum `!H cenv' env lctx e es sa sb cenv'' s0 op s1 ee v t. _`
       (qspecl_then [`H`, `cenv'`, `env'`, `lctx`, `e`, `es`, `sa'`, `sb`, `cenv''`,
                     `s0`, `op`, `s1`, `ee`, `v`, `t`] mp_tac) >>
     asm_rewrite_tac[] >>
     impl_tac >- (qexistsl [`gs`, `ee'`] >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC
QED
