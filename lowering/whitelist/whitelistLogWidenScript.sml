(* Log arguments may have smaller scalar bounds than their declared fields.
   Argument evaluation retains its physical operand types. The suffix uses
   a log_eval_view at the declared field types, whose non-indexed layouts
   determine both allocation limits. Scalar compatibility preserves topic
   encoding, ABI encoding and each value's occupied memory footprint.
   An indexed declared StringT (2 ** 256), paired with a StringT 1 argument,
   can satisfy the helper premises while the declared type does not evaluate.
   Indexed hashing ignores that capacity. The helpers therefore do not imply
   that every declared indexed field has an evaluated type. *)
Theory whitelistLogWiden
Ancestors
  allocLimits allocLimitsProps eventLoweringStructure
  valueCopyBytes valueTypingMemoryProps vyperEventCompatibility
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource
  exprSimWordArgs stmtSimLogSuffixActual stmtSimLogSuffixFrame
  stmtSimLogSuffixCode stmtSimLogArgs freshWrites logComposeFacts
  compileEnv loweringStateRelDefs stmtLowering fragExec loweringSlice exprLoweringProps
  emitHelperProps vyperInterpreter vyperState vyperTyping list
  stmtSimLogTrace emitHelper context venomInst
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq rich_list
  stmtSimLogCompose stmtSimLog bodySimLogArgs e2eDefs vyperEvent vyperEventArgCompat vyperABI
  vyperTypeSystem supportedTypes supportedDecls supportedStmts
  supportedExprs supportedExprTraverse supportedStmtTraverse
  exprSimSource bodyExprPreFacts exprSimHypsDefs bodySim exprSimHyps
  compileVyper vyperTypeInvariants supportedProgram supportedNames vyperContext
  vyperTypeExprSoundness vyperTypeCallGraph vyperTypeCallStackSoundness
Libs
  monadsyntax logWidenTacticsLib

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
  logWidenTacticsLib.compatible_cases
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
  logWidenTacticsLib.topics_eq scalar_event_arg_compatible
QED

Theorem compatible_non_indexed[local]:
  !flags tys atys.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    EVERY supported_scalar_type (log_non_indexed_types flags tys) /\
    LIST_REL event_arg_compatible (log_non_indexed_types flags tys)
      (log_non_indexed_types flags atys)
Proof
  logWidenTacticsLib.non_indexed
QED

Theorem compatible_abi_eq[local]:
  !tys atys vals.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    vyper_to_abi_types tenv atys = vyper_to_abi_types tenv tys /\
    vyper_to_abi_list tenv atys vals = vyper_to_abi_list tenv tys vals
Proof
  logWidenTacticsLib.abi_eq scalar_event_arg_compatible
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

(* stmtSimLogCompose's log_compile_structure, with any field types in
   ce_event_info. *)
Theorem log_compile_structure_widen[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  LENGTH flags = LENGTH args /\ EVERY supported_scalar_type tys /\
  ~exprs_can_mutate cenv args /\
  LIST_REL (\fty e. is_bytestring_type fty <=>
    is_bytestring_type (lowered_value_type cenv e)) tys args /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?ys xs sm ops st. compile_log_eval_all cenv args sa = (ys,sm) /\
    MAP SND ys = MAP (lowered_value_type cenv) args /\
    xs = ZIP (MAP FST ys,tys) /\ log_eval_view cenv args sa xs sm /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = tys /\ LENGTH flags = LENGTH xs /\
    inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  logWidenTacticsLib.declared_structure
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
  ~exprs_can_mutate cenv args /\
  EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args /\
  SUM (MAP (type_memory_bytes cenv)
         (log_non_indexed_types flags tys)) < dimword (:256) /\
  abi_size_bound cenv.ce_struct_fields
    (TupleT (log_non_indexed_types flags tys)) < dimword (:256) ==>
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
  `LIST_REL (\fty e. is_bytestring_type fty <=>
       is_bytestring_type (lowered_value_type cenv e)) tys args` by
    logWidenTacticsLib.physical_tags (CONJUNCT1 event_arg_compatible_cases) >>
  drule_all log_compile_structure_widen >> strip_tac >>
  qabbrev_tac `axs = ZIP (MAP FST ys,MAP expr_type args)` >>
  `gas_admissible (eval_exprs cx args) log_args_res_ok es` by
    (simp[log_args_res_ok_def] >>
     irule log_arguments_admissible >> simp[]) >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `R`, `es`, `sa`, `axs`, `sm`,
               `s0`, `env`, `env`, `es`, `ys`] mp_tac compile_log_eval_all_gas >>
  impl_tac
  >- (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> simp[Abbr `axs`] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `~cx.txn.is_static` (rewrite_tac o single o MATCH_MP eval_log_nonstatic_bind) >>
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
  qabbrev_tac `ds = ZIP (MAP FST ys,tys)` >>
  `LENGTH ys = LENGTH args` by
    (mp_tac (Q.SPECL [`cenv`,`args`,`sa`] compile_log_eval_all_length) >> simp[]) >>
  `MAP SND ds = tys /\ LENGTH ds = LENGTH args` by simp[Abbr `ds`, MAP_ZIP] >>
  `EVERY (supported_scalar_type o SND) ds` by
    (gvs[EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"]) >>
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
    logWidenTacticsLib.selected_data (CONJUNCT1 event_arg_compatible_cases) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    (drule log_args_post_state >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> drule compile_log_eval_all_grows >> simp[]) >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
                    (!lab. FST p <> Label lab)) ds` by
    (gvs[EVERY_EL, Abbr `ds`, Abbr `axs`, EL_ZIP, Excl "enc_def"] >>
     metis_tac[]) >>
  `encode_indexed_event_topics flags tys vs = SOME topics` by
    metis_tac[compatible_topics_eq] >>
  `EVERY supported_scalar_type (log_non_indexed_types flags tys) /\
   LIST_REL event_arg_compatible (log_non_indexed_types flags tys)
      (log_non_indexed_types flags (MAP expr_type args))` by
    (irule compatible_non_indexed >> simp[]) >>
  drule_all compatible_abi_eq >>
  disch_then (qspecl_then [`get_tenv cx`, `log_non_indexed_values flags vs`]
    strip_assume_tac) >>
  `vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
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
  >- (drule_all log_stmt_open >> simp[])
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) u` mp_tac >>
      simp[Abbr `ev`, wordsTheory.w2w_id, Excl "enc_def"])
  >- (rpt strip_tac >>
      `lookup_var x t = SOME w` by metis_tac[] >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def])
  >> irule alloca_frame_of_mem_frame >>
  fs[locals_kept_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `lookup_var x t = SOME w` by metis_tac[] >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  reverse conj_tac
  >- (qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (drule_all compile_log_eval_all_grows >> simp[]) >>
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by simp[] >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory` by
    (qpat_x_assum `!aid a k. _` irule >> qexists_tac `aid` >> simp[]) >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >> simp[] >> metis_tac[]
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
    ~exprs_can_mutate cenv args /\
    EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
               is_bytestring_type (expr_type e)) args /\
    SUM (MAP (type_memory_bytes cenv)
           (log_non_indexed_types flags tys)) <
      dimword (:256) /\
    abi_size_bound cenv.ce_struct_fields
      (TupleT (log_non_indexed_types flags tys)) <
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
          (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) <
     dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) <
     dimword (:256)` by
    (gvs[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def,
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
    conj_tac >- metis_tac[supported_pure_expr_no_mutate] >>
    conj_tac >- metis_tac[supported_pure_exprs_bytestring_iff] >>
    irule body_log_args_ready >>
    gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, AllCaseEqs()] >>
    metis_tac[]) >>
  simp[]
QED
