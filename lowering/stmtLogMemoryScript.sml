(* The log statement under the memory-counted statement judgment
   (stmt_frag_mem): the arguments as stmtLogArgsMemory evaluates them,
   then the suffix as S1 runs it (log_success_suffix_actual_run), whose
   memory checks and frontier growth stmtLogSuffixMemory gives. *)
Theory stmtLogMemory
Ancestors
  stmtLogArgsMemory stmtLogSuffixMemory whitelistLogWiden
  exprSimMemDefs exprSimDefs exprSimProps loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgs stmtSimLogArgsGrowth stmtSimLogSource stmtSimLogCompose
  stmtSimLogSuffixActual stmtSimLogSuffixCode stmtSimLogTrace exprSimWordArgs
  bodyMemoryDefs allocaHistory allocaHistoryFragment fragExecMem fragGasSeqMem
  freshWrites compileEnv loweringStateRelDefs stmtLowering fragExec loweringSlice exprLoweringProps
  emitHelperProps emitHelper context venomInst venomState
  vyperInterpreter vyperState vyperTyping list rich_list
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasPathMem
Libs
  monadsyntax logWidenTacticsLib

(* Outside a static frame the static-write check passes. *)
Theorem log_mem_eval_bind[local]:
  ~cx.txn.is_static ==>
  eval_stmt cx (Log id args) =
    bind (eval_exprs cx args)
      (\vs. bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                                 cx.txn.target id vs) "Log encode event")
                 push_log)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def] >> rpt gen_tac >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem log_mem_args_admissible[local]:
  ~cx.txn.is_static /\
  gas_admissible (eval_stmt cx (Log id args)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_exprs cx args)
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es
Proof
  rw[gas_admissible_def] >>
  `eval_stmt cx (Log id args) (es with gas_obs := gs) = (INR exc, ee)` by
    simp[log_eval_outcome] >>
  first_x_assum drule >> strip_tac >> metis_tac[log_argument_error_ok]
QED

Theorem log_mem_ignore_bind_bind[local]:
  ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
  Cases_on `a x` >> rename1 `a x = (r1, st1)` >> Cases_on `r1` >> simp[]
QED

(* A non-word scalar log argument is a bytestring, which the store bound
   covers with its data rounded up to whole words. *)
Theorem log_arg_store_bound[local]:
  expr_store_bound cx ty v op t /\ supported_scalar_type ty /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ eval_operand op t = SOME w /\
  ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
   (?str. v = StringV str /\ n = LENGTH str)) ==>
  w2n w + (32 * ((n + 31) DIV 32) + 32) <= t.vs_alloca_next
Proof
  rw[expr_store_bound_def] >> first_x_assum drule_all >>
  Cases_on `ty` >>
  gvs[supportedTypesTheory.supported_scalar_type_def,
      supportedTypesTheory.supported_word_type_def,
      supportedTypesTheory.supported_string_type_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supportedTypesTheory.supported_word_type_def,
      supportedTypesTheory.supported_string_type_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def, value_has_type_def,
      val_store_size_def, vfmConstantsTheory.word_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[supportedTypesTheory.supported_word_type_def,
      supportedTypesTheory.supported_string_type_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def, value_has_type_def,
      val_store_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem compile_log_ready_stmt_frag_mem:
  (!e tail s. R (e::tail) s ==>
    expr_sim_mem ctx func cenv cx (expr_type e) e s /\
    !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
      R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  (!tail s gs. R tail s ==> R tail (s with gas_obs := gs)) /\
  R args es /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) < dimword (:256) /\
  abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags tys)) < dimword (:256) /\
  ~exprs_can_mutate cenv args /\
  EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >>
  qpat_x_assum `!e tail s. _` (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  (* A static frame has no related target state. *)
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule_all log_compile_structure >> strip_tac >>
  `gas_admissible (eval_exprs cx args)
     (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es` by
    metis_tac[log_mem_args_admissible] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `R`, `es`, `sa`, `xs`, `sm`,
               `s0`, `env`, `env`, `es`, `ys`] mp_tac compile_log_eval_all_gas_mem >>
  impl_tac
  >- (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> simp[] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `~cx.txn.is_static` (rewrite_tac o single o MATCH_MP log_mem_eval_bind) >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "args_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[log_mem_ignore_bind_bind] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_ready_stmt_frag_mem[args_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def, Excl "enc_def"] >> strip_tac
  >- suspend "args_value" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexists_tac `marks` >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_log_ready_stmt_frag_mem[args_value]:
  gvs[Excl "enc_def"] >>
  qabbrev_tac `xs = ZIP (MAP FST ys,MAP expr_type args)` >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, Excl "enc_def"] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  drule_all (SRULE [] (Q.INST [`tys` |-> `MAP expr_type args`]
    log_source_event_encoded)) >> strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    (`EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
     gvs[EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"]) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs` by
    (fs[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
        combinTheory.o_DEF, Excl "enc_def"] >>
     rpt strip_tac >>
     `SND (EL n xs) = expr_type (EL n args)` by
       (qpat_x_assum `MAP SND xs = _` (mp_tac o Q.AP_TERM `EL n`) >>
        simp[EL_MAP, Excl "enc_def"]) >>
     qpat_x_assum `!n. n < LENGTH args ==> _` (qspec_then `n` mp_tac) >>
     simp[Excl "enc_def"]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[log_args_post_state] >>
  `local_ptrs_reserved cenv sm` by
    (drule_all compile_log_eval_all_grows >> strip_tac >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `LENGTH flags = LENGTH xs` by
    (qpat_assum `MAP SND xs = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (irule stmtSimLogTopicsTheory.split_log_ops_data_rel >> simp[]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
      ?aty tv. supported_scalar_type aty /\
        log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t (FST arg,aty) v /\
        evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
        (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
        encode_event_topic aty v = encode_event_topic (SND arg) v) xs vs` by
    (irule listTheory.LIST_REL_mono >>
     qexists_tac `\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
       supported_scalar_type (SND arg) /\
       ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v` >>
     simp[] >> qx_gen_tac `arg` >> qx_gen_tac `v` >> strip_tac >> simp[] >>
     qexistsl_tac [`SND arg`, `tv`] >> simp[]) >>
  qpat_assum `MAP SND xs = MAP expr_type args`
    (fn th => drule_all (REWRITE_RULE [th] log_success_suffix_actual_run)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `LIST_REL (\arg v. !w n.
     ~is_word_type (SND arg) /\ eval_operand (FST arg) t = SOME w /\
     ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
      (?str. v = StringV str /\ n = LENGTH str)) ==>
     w2n w + 32 + 32 * ((n + 31) DIV 32) <= t.vs_alloca_next) xs vs` by
    (qpat_x_assum `LIST_REL (\p v. expr_store_bound _ _ _ _ _) xs vs` mp_tac >>
     qpat_x_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ arg v /\ _) xs vs`
       mp_tac >>
     simp[LIST_REL_EL_EQN, Excl "enc_def"] >> rpt strip_tac >>
     qpat_x_assum `!n. _ ==> log_arg_rel _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `n` mp_tac) >>
     qpat_x_assum `!n. _ ==> expr_store_bound _ _ _ _ _`
       (qspec_then `n` mp_tac) >>
     simp[Excl "enc_def"] >> rpt strip_tac >>
     irule log_arg_store_bound >> metis_tac[]) >>
  qpat_assum `MAP SND xs = MAP expr_type args`
    (fn th => drule_all (REWRITE_RULE [th] log_success_suffix_mem_ok)) >>
  strip_tac >>
  `t.vs_alloca_next <= u.vs_alloca_next` by metis_tac[] >>
  suspend "suffix"
QED

Resume compile_log_ready_stmt_frag_mem[suffix]:
  rename1 `compile_stmt _ _ _ (Log _ _) sa = ((),sb)` >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions) /\
        t.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def,
         IS_PREFIX_APPEND, Excl "enc_def"] >>
     qexists_tac `l` >>
     REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qspecl_then [`emitted_insts sm sb`, `t`, `u`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_gas_path_mem >>
  impl_tac >- simp[Excl "enc_def"] >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qspecl_then [`emitted_insts sm sb`, `t`, `0`, `ctx`, `bb`]
       mp_tac exec_block_run_inst_seq >>
     impl_tac >- simp[Excl "enc_def"] >> simp[Excl "enc_def"]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`?rest. DROP t.vs_inst_idx bb.bb_instructions =
             emitted_insts sm sb ++ rest` by
       fs[IS_PREFIX_APPEND, Excl "enc_def"] >>
     `alloca_inv t` by fs[stmt_state_rel_def, Excl "enc_def"] >>
     qspecl_then [`func`, `bb`, `t`, `emitted_insts sm sb`, `rest`, `u`]
       mp_tac alloca_history_run_inst_seq >>
     impl_tac >- fs[EVERY_MEM, Excl "enc_def"] >>
     simp[Excl "enc_def"]) >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))` >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types flags (MAP expr_type args)))) (ListV avs)|>` >>
  `gas_marked_exec T (ctx,func)
     (bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                          cx.txn.target id vs) "Log encode event") push_log)
     (es_end with gas_obs := [], t) (REPLICATE n F) (INL ())
     (es_end with logs := es_end.logs ++ [ev])
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule gas_marked_exec_no_source_read >>
     simp[gas_marked_path_def, Excl "enc_def"] >>
     conj_tac
     >- (simp[bind_def, lift_option_def, return_def, push_log_def, Abbr `ev`,
              wordsTheory.w2w_id, Excl "enc_def"] >>
         simp[Once contractABITheory.enc_def]) >>
     metis_tac[]) >>
  qexists_tac `marks ++ REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def, Excl "enc_def"] >>
  qexistsl_tac [`INL ()`, `es_end with logs := es_end.logs ++ [ev]`,
                `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `vs`] >> simp[Excl "enc_def"] >>
      qpat_x_assum `gas_marked_exec _ _ (bind (lift_option _ _) push_log) _ _ _ _ _`
        mp_tac >>
      qpat_assum `encode_source_event _ _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
      simp[Excl "enc_def"]) >>
  suspend "post"
QED

Resume compile_log_ready_stmt_frag_mem[post]:
  drule log_args_post_frame >> simp[wb_frame_def, Excl "enc_def"] >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule_all compile_log_eval_all_grows >> simp[]) >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_path_mem _ _ _ _ (OK _)`
       (mp_tac o CONJUNCT1 o MATCH_MP gas_path_mem_exec) >>
     strip_tac >> drule gas_path_normal >> simp[Excl "enc_def"]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  simp[stmt_lands_def, stmt_state_rel_inst_idx, Excl "enc_def"] >>
  simp[cenv_top_ext_refl, Excl "enc_def"] >>
  disj1_tac >> rpt conj_tac
  >- fs[same_blocks_def]
  >- (drule_all log_stmt_open >> simp[Excl "enc_def"])
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) u` mp_tac >>
      qmatch_goalsub_abbrev_tac
        `stmt_state_rel _ _ _ _ E1 u ==> stmt_state_rel _ _ _ _ E2 u` >>
      `E1 = E2 with gas_obs := []` by
        simp[Abbr `E1`, Abbr `E2`, Abbr `ev`, wordsTheory.w2w_id,
             evaluation_state_component_equality, Excl "enc_def"] >>
      simp[Excl "enc_def"])
  >- fs[lookup_var_def, Excl "enc_def"] >>
  qspecl_then [`d`, `cenv`, `cenv`, `sa`, `sb`, `s0`,
               `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
    mp_tac return_buf_frame_frame >>
  impl_tac >- fs[lookup_var_def, Excl "enc_def"] >>
  simp[Excl "enc_def"]
QED

Finalise compile_log_ready_stmt_frag_mem

(* Field metadata may use wider scalar bounds than the argument buffers. *)

Theorem compile_log_ready_stmt_frag_mem_widen:
  (!e tail s. R (e::tail) s ==>
    expr_sim_mem ctx func cenv cx (expr_type e) e s /\
    !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
      R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  (!tail s gs. R tail s ==> R tail (s with gas_obs := gs)) /\
  R args es /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  LIST_REL event_arg_compatible tys (MAP expr_type args) /\
  LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  ~exprs_can_mutate cenv args /\
  EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args /\
  SUM (MAP (type_memory_bytes cenv)
    (log_non_indexed_types flags tys)) < dimword (:256) /\
  abi_size_bound cenv.ce_struct_fields
    (TupleT (log_non_indexed_types flags tys)) < dimword (:256) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >>
  `EVERY supported_scalar_type (MAP expr_type args)` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >>
     metis_tac[scalar_event_arg_compatible]) >>
  `LENGTH flags = LENGTH args` by
    (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  qpat_x_assum `!e tail s. _` (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  `LENGTH flags = LENGTH args` by simp[] >>
  `LIST_REL (\fty e. is_bytestring_type fty <=>
       is_bytestring_type (lowered_value_type cenv e)) tys args` by
    logWidenTacticsLib.with_cases logWidenTacticsLib.physical_tags >>
  `?ys xs sm ops st. compile_log_eval_all cenv args sa = (ys,sm) /\
    MAP SND ys = MAP (lowered_value_type cenv) args /\
    xs = ZIP (MAP FST ys,tys) /\ log_eval_view cenv args sa xs sm /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = tys /\ LENGTH flags = LENGTH xs /\
    inst_extends sm cs' /\ same_blocks sm cs' /\ sm.cs_next_var <= cs'.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm cs') /\ cs_extends sa sm /\ cs_extends sm cs' /\
    fn_has_code sa sm func /\ fn_has_code sm cs' func` by
    (rename1 `compile_stmt _ _ _ (Log _ _) sa = ((),sb)` >>
     qpat_x_assum `cenv.ce_event_info _ = _` mp_tac >>
     qpat_x_assum `LENGTH flags = LENGTH args` mp_tac >>
     qpat_x_assum `EVERY supported_scalar_type tys` mp_tac >>
     qpat_x_assum `~exprs_can_mutate cenv args` mp_tac >>
     qpat_x_assum `LIST_REL (\fty e. is_bytestring_type fty <=> _) tys args` mp_tac >>
     qpat_x_assum `compile_stmt _ _ _ (Log _ _) sa = _` mp_tac >>
     qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     logWidenTacticsLib.declared_structure) >>
  qabbrev_tac `axs = ZIP (MAP FST ys,MAP expr_type args)` >>
  `gas_admissible (eval_exprs cx args)
     (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es` by
    metis_tac[log_mem_args_admissible] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `R`, `es`, `sa`, `axs`, `sm`,
               `s0`, `env`, `env`, `es`, `ys`] mp_tac compile_log_eval_all_gas_mem >>
  impl_tac
  >- (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> simp[Abbr `axs`] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `~cx.txn.is_static` (rewrite_tac o single o MATCH_MP log_mem_eval_bind) >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "args_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[log_mem_ignore_bind_bind] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_ready_stmt_frag_mem_widen[args_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def, Excl "enc_def"] >> strip_tac
  >- suspend "args_value" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexists_tac `marks` >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_log_ready_stmt_frag_mem_widen[args_value]:
  gvs[Excl "enc_def"] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, Excl "enc_def"] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `LENGTH flags = LENGTH tys` by simp[] >>
  drule_all log_source_event_encoded_widen >> strip_tac >>
  qabbrev_tac `ds = ZIP (MAP FST ys,tys)` >>
  `LENGTH ys = LENGTH args` by
    (mp_tac (Q.SPECL [`cenv`,`args`,`sa`]
       eventLoweringStructureTheory.compile_log_eval_all_length) >> simp[]) >>
  `MAP SND ds = tys /\ LENGTH ds = LENGTH args` by simp[Abbr `ds`, MAP_ZIP] >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. event_arg_compatible (SND arg) aty /\ supported_scalar_type aty /\
      log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) ds vs` by
    logWidenTacticsLib.source_witness scalar_event_arg_compatible >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops ds flags)) (log_non_indexed_values flags vs)` by
    logWidenTacticsLib.with_cases logWidenTacticsLib.selected_data >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    (drule log_args_post_state >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> drule compile_log_eval_all_grows >> simp[]) >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
                    (!lab. FST p <> Label lab)) ds` by
    (gvs[EVERY_EL, Abbr `ds`, Abbr `axs`, EL_ZIP, Excl "enc_def"] >>
     metis_tac[]) >>
  `encode_indexed_event_topics flags (MAP expr_type args) vs =
      encode_indexed_event_topics flags tys vs /\
   vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags (MAP expr_type args)) =
      vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags tys) /\
   vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP expr_type args))
      (log_non_indexed_values flags vs) =
   vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vs)` by
    logWidenTacticsLib.encoding_facts scalar_event_arg_compatible >>
  `encode_indexed_event_topics flags tys vs = SOME topics /\
   vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vs) = SOME avs` by metis_tac[] >>
  `LENGTH flags = LENGTH ds` by simp[] >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
    ?aty tv. supported_scalar_type aty /\
      log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t (FST arg,aty) v /\
      evaluate_type (get_tenv cx) aty = SOME tv /\ value_has_type tv v /\
      (is_bytestring_type aty <=> is_bytestring_type (SND arg)) /\
      encode_event_topic aty v = encode_event_topic (SND arg) v) ds vs` by
    (irule LIST_REL_mono >> first_assum (irule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_assum `MAP SND ds = tys`
    (fn th => drule_all (REWRITE_RULE [th]
      (Q.INST [`xs` |-> `ds`] log_success_suffix_actual_run))) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `LIST_REL (\arg v. !w n.
     ~is_word_type (SND arg) /\ eval_operand (FST arg) t = SOME w /\
     ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
      (?str. v = StringV str /\ n = LENGTH str)) ==>
     w2n w + 32 + 32 * ((n + 31) DIV 32) <= t.vs_alloca_next) ds vs` by
    (qpat_x_assum `LIST_REL (\p v. expr_store_bound _ _ _ _ _) axs vs` mp_tac >>
     qpat_x_assum `LIST_REL (\ty v. ?tv. evaluate_type _ ty = _ /\ _) (MAP expr_type args) vs` mp_tac >>
     qpat_x_assum `LIST_REL event_arg_compatible tys (MAP expr_type args)` mp_tac >>
     qpat_x_assum `EVERY supported_scalar_type (MAP expr_type args)` mp_tac >>
     qpat_x_assum `EVERY supported_scalar_type tys` mp_tac >>
     simp[LIST_REL_EL_EQN, EVERY_EL, Abbr `ds`, Abbr `axs`, EL_ZIP, EL_MAP,
          Excl "enc_def"] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `!n. _ ==> ?tv. _` (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >>
     `supported_scalar_type (expr_type (EL n args)) /\
      supported_scalar_type (EL n tys) /\
      event_arg_compatible (EL n tys) (expr_type (EL n args))` by metis_tac[] >>
     `~is_word_type (expr_type (EL n args))` by
       (qpat_x_assum `event_arg_compatible (EL n tys) _` mp_tac >>
        qpat_x_assum `supported_scalar_type (EL n tys)` mp_tac >>
        qpat_x_assum `~is_word_type (EL n tys)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        logWidenTacticsLib.with_cases (fn cases =>
          drule cases >> strip_tac >>
          gvs[supportedTypesTheory.supported_scalar_type_def,
              supportedTypesTheory.supported_word_type_def,
              supportedTypesTheory.supported_string_type_def,
              is_word_type_def])) >>
     irule log_arg_store_bound >> metis_tac[]) >>
  qpat_assum `MAP SND ds = tys`
    (fn th => drule_all (REWRITE_RULE [th]
      (Q.INST [`xs` |-> `ds`] log_success_suffix_mem_ok))) >>
  strip_tac >>
  `t.vs_alloca_next <= u.vs_alloca_next` by metis_tac[] >>
  suspend "suffix"
QED

Resume compile_log_ready_stmt_frag_mem_widen[suffix]:
  rename1 `compile_stmt _ _ _ (Log _ _) sa = ((),sb)` >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions) /\
        t.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def,
         IS_PREFIX_APPEND, Excl "enc_def"] >>
     qexists_tac `l` >>
     REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qspecl_then [`emitted_insts sm sb`, `t`, `u`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_gas_path_mem >>
  impl_tac >- simp[Excl "enc_def"] >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qspecl_then [`emitted_insts sm sb`, `t`, `0`, `ctx`, `bb`]
       mp_tac exec_block_run_inst_seq >>
     impl_tac >- simp[Excl "enc_def"] >> simp[Excl "enc_def"]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`?rest. DROP t.vs_inst_idx bb.bb_instructions =
             emitted_insts sm sb ++ rest` by
       fs[IS_PREFIX_APPEND, Excl "enc_def"] >>
     `alloca_inv t` by fs[stmt_state_rel_def, Excl "enc_def"] >>
     qspecl_then [`func`, `bb`, `t`, `emitted_insts sm sb`, `rest`, `u`]
       mp_tac alloca_history_run_inst_seq >>
     impl_tac >- fs[EVERY_MEM, Excl "enc_def"] >>
     simp[Excl "enc_def"]) >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))` >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types flags (MAP expr_type args)))) (ListV avs)|>` >>
  `gas_marked_exec T (ctx,func)
     (bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                          cx.txn.target id vs) "Log encode event") push_log)
     (es_end with gas_obs := [], t) (REPLICATE n F) (INL ())
     (es_end with logs := es_end.logs ++ [ev])
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule gas_marked_exec_no_source_read >>
     simp[gas_marked_path_def, Excl "enc_def"] >>
     conj_tac
     >- (simp[bind_def, lift_option_def, return_def, push_log_def, Abbr `ev`,
              wordsTheory.w2w_id, Excl "enc_def"] >>
         simp[Once contractABITheory.enc_def]) >>
     metis_tac[]) >>
  qexists_tac `marks ++ REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def, Excl "enc_def"] >>
  qexistsl_tac [`INL ()`, `es_end with logs := es_end.logs ++ [ev]`,
                `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `vs`] >> simp[Excl "enc_def"] >>
      qpat_x_assum `gas_marked_exec _ _ (bind (lift_option _ _) push_log) _ _ _ _ _`
        mp_tac >>
      qpat_assum `encode_source_event _ _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
      simp[Excl "enc_def"]) >>
  suspend "post"
QED

Resume compile_log_ready_stmt_frag_mem_widen[post]:
  drule log_args_post_frame >> simp[wb_frame_def, Excl "enc_def"] >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_path_mem _ _ _ _ (OK _)`
       (mp_tac o CONJUNCT1 o MATCH_MP gas_path_mem_exec) >>
     strip_tac >> drule gas_path_normal >> simp[Excl "enc_def"]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  simp[stmt_lands_def, stmt_state_rel_inst_idx, Excl "enc_def"] >>
  simp[cenv_top_ext_refl, Excl "enc_def"] >>
  disj1_tac >> rpt conj_tac
  >- fs[same_blocks_def]
  >- (`EVERY (supported_scalar_type o SND) ds` by
        (gvs[EVERY_MAP, combinTheory.o_DEF]) >>
      drule_all log_stmt_open >> simp[Excl "enc_def"])
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) u` mp_tac >>
      qmatch_goalsub_abbrev_tac
        `stmt_state_rel _ _ _ _ E1 u ==> stmt_state_rel _ _ _ _ E2 u` >>
      `E1 = E2 with gas_obs := []` by
        simp[Abbr `E1`, Abbr `E2`, Abbr `ev`, wordsTheory.w2w_id,
             evaluation_state_component_equality, Excl "enc_def"] >>
      simp[Excl "enc_def"])
  >- fs[lookup_var_def, Excl "enc_def"] >>
  qspecl_then [`d`, `cenv`, `cenv`, `sa`, `sb`, `s0`,
               `u with vs_inst_idx := LENGTH sb.cs_current_insts`]
    mp_tac return_buf_frame_frame >>
  impl_tac >- fs[lookup_var_def, Excl "enc_def"] >>
  simp[Excl "enc_def"]
QED

Finalise compile_log_ready_stmt_frag_mem_widen
