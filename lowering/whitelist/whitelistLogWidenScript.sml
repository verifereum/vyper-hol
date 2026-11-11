(*
 * Whitelist removal: log arguments that widen to the event field type.
 *
 * supported_log asks each log argument's type to equal its event field's
 * type (MAP expr_type es = MAP (SND o FST) fields); the type checker asks
 * only event_arg_compatible (a String[5] argument for a String[10] field,
 * a shorter Bytes[...]).  The lowering never reads the field types: its
 * Log case types the topics and the data tuple by the arguments
 * (data_types = MAP SND data_ops, compile_log_eval_all_types), and
 * log_alloc_ok bounds the buffers at the argument types too.  The source
 * encodes by the field types (encode_source_event via
 * lookup_event_metadata).  For the scalar fields a supported event has,
 * event_arg_compatible leaves only a bytestring's bound free, and neither
 * the ABI type (vyper_base_to_abi_type), the ABI value (vyper_to_abi_base)
 * nor a topic (encode_event_topic hashes any bytestring) looks at the
 * bound, so the source event is the one the argument types give.
 *
 * Survey: lemmas of the log family whose statement or proof uses the
 * exact-type equation.
 *   stmtSimLogCompose:122 compile_log_ready_stmt_frag — premise
 *     MAP expr_type args = tys.  It is used only to instantiate
 *     log_source_event_encoded (stmtSimLogSource:116) at the argument
 *     types, whose lookup_event_metadata premise then names them.  Needs:
 *     LIST_REL event_arg_compatible tys (MAP expr_type args), with the
 *     buffer bounds at the argument types
 *       -> compile_log_ready_stmt_frag_widen, by
 *          log_source_event_encoded_widen.
 *     Its [local] log_compile_structure (:44) states ce_event_info at the
 *     argument types, though its proof (log_success_suffix_code) takes any
 *       -> log_compile_structure_widen.
 *   stmtSimLog:76 compile_log_stmt_frag — passes the equation on
 *       -> compile_log_stmt_frag_widen.
 *   bodySimLog:178 body_log_case — reads the equation out of supported_log
 *       -> body_log_widen_case, under the type checker's
 *          LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e))
 *          es fields (type_stmt's Log clause) for the event's fields.
 *   The S3 twins have the same single use: stmtLogMemory:143
 *     compile_log_ready_stmt_frag_mem (log_source_event_encoded at the
 *     argument types, and [local] log_mem_compile_structure) and
 *     bodyMemLog:96 body_log_mem_case; not this piece (S1).
 *     bodyPtrLogCases:20 body_log_case_ptr is admitted at the branch head.
 *
 * Already general (argument types only, no field types):
 *   compile_log_eval_all_gas, compile_log_eval_all_types and the rest of
 *   stmtSimLogArgs*/stmtLogArgsMemory; log_success_suffix_code,
 *   log_success_suffix_actual_run, compile_log_data_trace,
 *   compile_log_empty_trace (any tys in ce_event_info); stmtSimLogSource's
 *   log_scalar_* lemmas; body_log_metadata, body_log_args_ready.
 *
 * TOP-LEVEL:
 *   scalar_event_arg_compatible  — a compatible argument type of a scalar
 *                                  field is scalar and encodes like it
 *   log_source_event_encoded_widen
 *                                — the source event, from the field types'
 *                                  metadata, is the argument types' one
 *   compile_log_ready_stmt_frag_widen, compile_log_stmt_frag_widen,
 *   body_log_widen_case          — the log simulation with compatible
 *                                  argument types
 *)
Theory whitelistLogWiden
Ancestors
  allocLimits allocLimitsProps
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource
  exprSimWordArgs stmtSimLogSuffixActual stmtSimLogSuffixFrame
  stmtSimLogSuffixCode stmtSimLogArgs freshWrites
  compileEnv loweringStateRelDefs stmtLowering fragExec loweringSlice exprLoweringProps
  emitHelperProps vyperInterpreter vyperState vyperTyping list
  stmtSimLogTrace emitHelper context venomInst
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq rich_list
  stmtSimLogCompose stmtSimLog bodySimLogArgs e2eDefs vyperEvent vyperABI
  vyperTypeSystem supportedTypes supportedDecls supportedStmts
  supportedExprs supportedExprTraverse supportedStmtTraverse
  exprSimSource bodyExprPreFacts exprSimHypsDefs bodySim exprSimHyps
  compileVyper vyperTypeInvariants supportedProgram supportedNames vyperContext
  vyperTypeExprSoundness vyperTypeCallGraph vyperTypeCallStackSoundness
Libs
  monadsyntax

(* ===== The source encoding ignores a bytestring argument's bound ===== *)

Theorem event_arg_compatible_cases[local]:
  (!fty aty. event_arg_compatible fty aty ==>
     aty = fty \/
     (?n m. fty = BaseT (StringT n) /\ aty = BaseT (StringT m)) \/
     (?n m. fty = BaseT (BytesT (Dynamic n)) /\
            aty = BaseT (BytesT (Dynamic m))) \/
     (?t b. fty = ArrayT t b) \/ (?ts. fty = TupleT ts)) /\
  (!fs ats. event_arg_compatible_list fs ats ==> T)
Proof
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def]
QED

Theorem scalar_event_arg_compatible:
  !fty aty tenv.
    supported_scalar_type fty /\ event_arg_compatible fty aty ==>
    supported_scalar_type aty /\
    vyper_to_abi_type tenv aty = vyper_to_abi_type tenv fty /\
    (!v. vyper_to_abi tenv aty v = vyper_to_abi tenv fty v) /\
    (!v. encode_event_topic aty v = encode_event_topic fty v)
Proof
  rpt gen_tac >> strip_tac >>
  drule (CONJUNCT1 event_arg_compatible_cases) >> strip_tac >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
  rw[supported_string_type_def, encode_event_topic_def,
     is_event_bytestring_type_def] >>
  Cases_on `v` >> simp[]
QED

Theorem compatible_topics_eq[local]:
  !tys atys flags vals.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    encode_indexed_event_topics flags atys vals =
    encode_indexed_event_topics flags tys vals
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS1] >>
  Cases_on `flags` >> Cases_on `vals` >>
  simp[encode_indexed_event_topics_def] >>
  rename1 `encode_indexed_event_topics (flg::_) _ _` >>
  Cases_on `flg` >> simp[encode_indexed_event_topics_def] >>
  drule_all scalar_event_arg_compatible >> simp[]
QED

Theorem compatible_non_indexed[local]:
  !flags tys atys.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    EVERY supported_scalar_type (log_non_indexed_types flags tys) /\
    LIST_REL event_arg_compatible (log_non_indexed_types flags tys)
      (log_non_indexed_types flags atys)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (Cases_on `tys` >> gvs[log_non_indexed_types_def]) >>
  Cases_on `tys` >> gvs[log_non_indexed_types_def, LIST_REL_CONS1] >>
  rename1 `log_non_indexed_types (flg::_) _` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `flg` >> simp[log_non_indexed_types_def]
QED

Theorem compatible_abi_eq[local]:
  !tys atys vals.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    vyper_to_abi_types tenv atys = vyper_to_abi_types tenv tys /\
    vyper_to_abi_list tenv atys vals = vyper_to_abi_list tenv tys vals
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS1] >>
  drule_all scalar_event_arg_compatible >>
  disch_then (qspec_then `tenv` strip_assume_tac) >>
  Cases_on `vals` >> simp[]
QED

(* log_source_event_encoded with the metadata at the field types tys and
   the values typed at compatible argument types atys. *)
Theorem log_source_event_encoded_widen:
  lookup_event_metadata tenv sources target id = SOME (h, tys, flags) /\
  EVERY supported_scalar_type tys /\
  LIST_REL event_arg_compatible tys atys /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                            value_has_type tv v) atys vals /\
  LENGTH flags = LENGTH tys ==>
  ?topics avs.
    encode_indexed_event_topics flags atys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags atys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <| logger := target; topics := n2w h :: topics;
              data := enc (Tuple (vyper_to_abi_types tenv
                                  (log_non_indexed_types flags atys)))
                          (ListV avs) |>
Proof
  strip_tac >>
  `EVERY supported_scalar_type atys` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >>
     metis_tac[scalar_event_arg_compatible]) >>
  `LENGTH atys = LENGTH tys /\ LENGTH vals = LENGTH atys` by
    metis_tac[LIST_REL_LENGTH] >>
  qspecl_then [`atys`, `flags`, `vals`] mp_tac log_scalar_topics_exist >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`flags`, `atys`, `vals`] mp_tac log_non_indexed_scalars_typed >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all log_scalar_abi_list_exists >> strip_tac >>
  qspecl_then [`flags`, `tys`, `atys`] mp_tac compatible_non_indexed >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`log_non_indexed_types flags tys`,
               `log_non_indexed_types flags atys`,
               `log_non_indexed_values flags vals`] mp_tac compatible_abi_eq >>
  impl_tac >- simp[] >> strip_tac >>
  `encode_indexed_event_topics flags tys vals = SOME topics` by
    metis_tac[compatible_topics_eq] >>
  `LENGTH flags = LENGTH vals` by simp[] >>
  mp_tac (Q.INST [`flags` |-> `flags`, `tys` |-> `tys`, `vals` |-> `vals`]
            (SPEC_ALL non_indexed_event_args_exists)) >>
  impl_tac >- simp[] >> strip_tac >>
  gvs[encode_source_event_def, encode_vyper_event_metadata_def]
QED

(* ===== Statement simulation ===== *)

Theorem log_emit_open_widen[local]:
  emit_inst LOG ops [] sa = ((),sb) ==> ~block_is_terminated sb
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  Cases_on `sa.cs_current_insts` >>
  simp[block_is_terminated_def, rich_listTheory.LAST_APPEND, LAST_CONS_cond,
       mk_inst_def, is_terminator_def]
QED

(* stmtSimLogCompose's log_compile_structure, with any field types in
   ce_event_info. *)
Theorem log_compile_structure_widen[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  LENGTH flags = LENGTH args /\ EVERY supported_scalar_type (MAP expr_type args) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?xs sm ops st. compile_log_eval_all cenv args sa = (xs,sm) /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = MAP expr_type args /\ LENGTH flags = LENGTH xs /\
    inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (xs,sm)` >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops xs flags)) sm` >>
  rename1 `compile_log_topic_ops _ sm = (ops,st)` >>
  `MAP SND xs = MAP expr_type args` by
    (drule compile_log_eval_all_types >> simp[]) >>
  `LENGTH xs = LENGTH args` by metis_tac[listTheory.LENGTH_MAP] >>
  `EVERY (supported_scalar_type o SND) xs` by
    (`EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
     gvs[EVERY_MAP, combinTheory.o_DEF]) >>
  `LENGTH flags = LENGTH xs` by decide_tac >>
  drule_all log_success_suffix_code >> strip_tac >>
  `cs_extends sa sm` by (drule compile_log_eval_all_grows >> simp[]) >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[]) >>
  map_every qexists_tac [`xs`, `sm`, `ops`, `st`] >> simp[] >>
  metis_tac[fn_has_code_mid, cs_extends_refl]
QED

Theorem log_stmt_open_widen[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all cenv args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >>
  Cases_on `SND (split_log_ops xs flags) = []`
  >- (drule_all compile_log_empty_trace >> strip_tac >>
      qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
      metis_tac[log_emit_open_widen]) >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  strip_tac >> drule log_emit_open_widen >> simp[]
QED

Theorem eval_log_bind_widen[local]:
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

Theorem log_args_admissible_widen[local]:
  ~cx.txn.is_static /\
  gas_admissible (eval_stmt cx (Log id args)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_exprs cx args) log_args_res_ok es
Proof
  rw[gas_admissible_def, log_args_res_ok_def] >>
  `eval_stmt cx (Log id args) (es with gas_obs := gs) = (INR exc, ee)` by
    simp[log_eval_outcome] >>
  first_x_assum drule >> strip_tac >> metis_tac[log_argument_error_ok]
QED

(* compile_log_ready_stmt_frag with argument types compatible with the
   field types tys, instead of equal to them; the buffer bounds are at the
   argument types, which is what log_alloc_ok checks. *)
Theorem compile_log_ready_stmt_frag_widen:
  (!e tail s. R (e::tail) s ==>
    expr_sim ctx func cenv cx (expr_type e) e s /\
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
  SUM (MAP (type_memory_bytes cenv)
         (log_non_indexed_types flags (MAP expr_type args))) < dimword (:256) /\
  abi_size_bound cenv.ce_struct_fields
    (TupleT (log_non_indexed_types flags (MAP expr_type args))) < dimword (:256) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >>
  `EVERY supported_scalar_type (MAP expr_type args)` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >>
     metis_tac[scalar_event_arg_compatible]) >>
  `LENGTH flags = LENGTH args` by
    (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  qpat_x_assum `!e tail s. _` (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  `LENGTH flags = LENGTH args` by simp[] >>
  drule_all log_compile_structure_widen >> strip_tac >>
  `gas_admissible (eval_exprs cx args) log_args_res_ok es` by
    metis_tac[log_args_admissible_widen] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `R`, `es`, `sa`, `xs`, `sm`,
               `s0`, `env`, `env`, `es`] mp_tac compile_log_eval_all_gas >>
  impl_tac
  >- (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> simp[] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `~cx.txn.is_static` (rewrite_tac o single o MATCH_MP eval_log_bind_widen) >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "args_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_ready_stmt_frag_widen[args_summary]:
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

Resume compile_log_ready_stmt_frag_widen[args_value]:
  gvs[Excl "enc_def"] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, Excl "enc_def"] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `LENGTH flags = LENGTH tys` by simp[] >>
  drule_all log_source_event_encoded_widen >> strip_tac >>
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
    (drule compile_log_eval_all_grows >> strip_tac >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `LENGTH flags = LENGTH xs` by simp[] >>
  qpat_assum `MAP SND xs = MAP expr_type args`
    (fn th => drule_all (REWRITE_RULE [th] log_success_suffix_actual_run)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  suspend "suffix"
QED

Resume compile_log_ready_stmt_frag_widen[suffix]:
  rename1 `compile_stmt _ _ _ (Log _ _) sa = ((),sb)` >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions) /\
        t.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def,
         IS_PREFIX_APPEND, Excl "enc_def"] >>
     qexists_tac `l` >>
     REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qspecl_then [`emitted_insts sm sb`, `t`, `u`, `ctx`, `func`, `bb`]
    mp_tac tuple_run_inst_seq_gas_path >>
  impl_tac >- simp[Excl "enc_def"] >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qspecl_then [`emitted_insts sm sb`, `t`, `0`, `ctx`, `bb`]
       mp_tac exec_block_run_inst_seq >>
     impl_tac >- simp[Excl "enc_def"] >> simp[Excl "enc_def"]) >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))` >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types flags (MAP expr_type args)))) (ListV avs)|>` >>
  `gas_marked_exec F (ctx,func)
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

Resume compile_log_ready_stmt_frag_widen[post]:
  drule log_args_post_frame >> simp[wb_frame_def, Excl "enc_def"] >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  `~u.vs_halted` by
    (drule gas_path_normal >> simp[Excl "enc_def"]) >>
  disj1_tac >>
  simp[stmt_post_def, stmt_lands_def, stmt_state_rel_inst_idx, Excl "enc_def"] >>
  simp[cenv_top_ext_refl, Excl "enc_def"] >>
  rpt conj_tac
  >- fs[same_blocks_def]
  >- metis_tac[log_stmt_open_widen]
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) u` mp_tac >>
      simp[Abbr `ev`, wordsTheory.w2w_id, Excl "enc_def"])
  >- (rpt strip_tac >>
      `lookup_var x t = SOME w` by metis_tac[] >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def])
  >> metis_tac[]
QED

Finalise compile_log_ready_stmt_frag_widen

(* compile_log_stmt_frag with compatible argument types. *)
Theorem compile_log_stmt_frag_widen:
  !ctx func cx lctx RetQ cenv ty id args es Inv h tys flags env.
    cenv.ce_event_info (nsid_to_string id) = SOME (h, tys, flags) /\
    lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
      SOME (h, tys, flags) /\
    LIST_REL event_arg_compatible tys (MAP expr_type args) /\
    LENGTH flags = LENGTH tys /\
    LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
    SUM (MAP (type_memory_bytes cenv)
           (log_non_indexed_types flags (MAP expr_type args))) <
      dimword (:256) /\
    abi_size_bound cenv.ce_struct_fields
      (TupleT (log_non_indexed_types flags (MAP expr_type args))) <
      dimword (:256) /\
    log_args_ready ctx func cenv cx Inv args /\ Inv es /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`R` |-> `\tail s. log_args_ready ctx func cenv cx Inv tail /\ Inv s`]
           compile_log_ready_stmt_frag_widen) >>
  impl_tac >- (
    simp[] >> rpt conj_tac
    >~ [`expr_sim`]
    >- (rpt gen_tac >> simp[Once log_args_ready_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> simp[] >>
        rpt gen_tac >> strip_tac >>
        `Inv s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                          value_has_type tv v` by metis_tac[] >>
        simp[] >> first_x_assum irule >>
        qpat_x_assum `(do r <- eval_expr cx e; read_result cx r od) s = _` mp_tac >>
        simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
    gvs[] >> metis_tac[]) >>
  simp[]
QED

(* ===== The body case ===== *)

Theorem event_fields_compatible[local]:
  !args fields.
    LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields ==>
    LIST_REL event_arg_compatible (MAP (SND o FST) fields) (MAP expr_type args)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS2] >> rename1 `UNCURRY _ fld` >>
  PairCases_on `fld` >> gvs[]
QED

(* body_log_case with supported_log's exact-type equation replaced by the
   type checker's event_arg_compatible (type_stmt's Log clause) for the
   event's fields.  The premises are body_stmt_ok's that the case uses. *)
Theorem body_log_widen_case:
  !cx id args tops ctx func cenv env env' ret_ty lctx RetQ es fields.
    body_stmt_safe tops (Log id args) /\
    body_exprs_ok cx args /\ body_inv tops ctx cenv cx /\
    supported_pure_exprs tops args /\
    supported_event_fields tops id = SOME fields /\
    LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  rpt strip_tac >>
  drule_all body_log_metadata >> strip_tac >>
  drule event_fields_compatible >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields) (MAP expr_type args))) <
     dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields) (MAP expr_type args))) <
     dimword (:256)` by
    (gvs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
         allocLimitsTheory.log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env args /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv args` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ret_ty`, `id`,
               `args`, `es`, `\s. expr_sim_inv cenv cx env s`, `h`,
               `MAP (SND o FST) fields`, `MAP SND fields`, `env`]
    mp_tac compile_log_stmt_frag_widen >>
  impl_tac >- (
    simp[] >>
    irule body_log_args_ready >>
    gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
        int_calls_stmt_def, AllCaseEqs()] >>
    metis_tac[]) >>
  simp[]
QED
