(* Successful declared-type Log suffix, starting at the captured endpoint. *)
Theory stmtSimLogDeclaredSuffix
Ancestors
  bodySim bodySimLogArgs stmtSimLogSource stmtSimLogTrace stmtSimLogSuffixActual
  stmtSimLogTopics stmtSimLogAllocate stmtSimLogDataRun stmtSimLogDataInput
  stmtSimLogDataFrame stmtSimLogEmit stmtSimLogCompose whitelistLogWiden logTopicsRunPtr
  eventTopicCode eventLoweringStructure stmtLoweringMono abiBuiltinAllocation
  abiEncoderCounters exprSimAbiGasBridge exprSimAbiEncodeFramedBody
  exprSimAbiEncodeStateTransport exprSimAbiEncodeChargeTransfer abiEncoderWindowContract
  exprSimAbiEncodeRelabelContext exprSimAbiEncodeRelabelResources abiEncoderExitPhi
  exprSimAbiEncodeConcreteBody exprSimAbiEncodeConcreteWrappers exprSimAbiEncodeNoBlockFrame
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousLabels typedLogSplitComplete abiLogSourceEncoding exprSimHyps
  exprSimHypsDefs exprLoweringProps exprSimDefs exprSimWordArgs abiDecoderContract
  venomMemDefs localPtrsProps loweringSlice valueEncodingProps abiTypeBoundProps vyperTypeABI
  vyperABI compileEnv stmtSimDefs stmtLowering emitHelperProps context venomState venomInst
  venomExecSemantics list rich_list words finite_map pred_set fragGasPath fragGasSeq abiDecoderReentry
  exprSimAbiEncodeSourceRoom exprSimAbiEncodeExecFrame exprSimAbiEncodeCallerFrame
  exprSimAbiEncodeSuffixOwnership exprSimAbiEncodeRelabelBoundary abiEncoderRegisteredEffect
  stmtSimProps loweringHalt abiEncoderAppend emitHelper fragExec abiEncoderAllocationShape
  exprSimAbiEncodeObliviousContext exprSimAbiEncodeObliviousSimulation loweringPosts
  abiEncoderProps fragGasMode exprSimHashBoundary loweringStateRelDefs allocLimits
  stmtSimLogArgs stmtSimLogSuffix valueEncodingDefs freshWrites eventLogSplitProps
  supportedTypes stmtSimLogSuffixCode logComposeFacts placeMemoryCodeLayout

Theorem log_declared_suffix_path:
body_inv tops ctx cenv cx /\
supported_event_fields tops id = SOME fields /\
expr_sim_inv cenv cx env es0 /\
supported_pure_exprs tops args /\ well_typed_exprs env args /\
log_alloc_ok cenv id args /\
compile_log_eval_all cenv args sa = (ops,sm) /\
compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
local_ptrs_reserved cenv sm /\
stmt_state_rel ctx func cenv cx es s /\
~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
s.vs_inst_idx = LENGTH sm.cs_current_insts /\
LENGTH ops = LENGTH args /\ LENGTH args = LENGTH fields /\
MAP SND ops = MAP (lowered_value_type cenv) args /\
EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
           (!lab. FST p <> Label lab)) ops /\
LIST_REL (\((op,sty),(e,((name,dty),indexed))) v.
  event_arg_compatible dty (expr_type e) /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = expr_type e) /\
  (?ltv. evaluate_type (get_tenv cx) (expr_type e) = SOME ltv /\
    value_has_type ltv v /\ val_wf ltv v) /\
  expr_val_rel cx (expr_type e) v op s /\
  expr_val_at cenv cx (expr_type e) sa sm es v op s /\
  (!w tv. ~is_word_type (expr_type e) /\
    ~is_bytestring_type (expr_type e) /\ eval_operand op s = SOME w /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    w2n w + type_memory_size tv < dimword (:256)) /\
  (~indexed ==> type_widens_to (get_tenv cx) (expr_type e) dty /\
    ?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
      value_has_type dtv v /\ val_wf dtv v))
  (ZIP (ops,ZIP (args,fields))) vs /\
lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
  SOME (h,MAP (SND o FST) fields,MAP SND fields) /\
encode_indexed_event_topics (MAP SND fields) (MAP expr_type args) vs = SOME topics /\
vyper_to_abi_list (get_tenv cx)
  (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))
  (log_non_indexed_values (MAP SND fields) vs) = SOME avs ==>
?t. gas_path ctx func s 0 (OK t) /\
  stmt_post ctx func cx lctx cenv cenv sm sb es s (INL ())
    (es with logs := es.logs ++
      [<|logger := cx.txn.target; topics := n2w h::topics;
         data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
           (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))))
           (ListV avs)|>]) t
Proof
  strip_tac >>
  drule_all body_log_aggregate_metadata >> strip_tac >>
  `cenv.ce_event_info (nsid_to_string id) =
    SOME (h,MAP (SND o FST) fields,MAP SND fields)` by metis_tac[optionTheory.SOME_11] >>
  `SUM (MAP (type_memory_bytes cenv)
     (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) < 2 ** 64 /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) < 2 ** 64` by
    fs[log_alloc_ok_def] >>
  qabbrev_tac `flags = MAP SND fields` >>
  qabbrev_tac `dtys = MAP (SND o FST) fields` >>
  qabbrev_tac `ltys = MAP expr_type args` >>
  qabbrev_tac `xs = ZIP (MAP FST ops,ltys)` >>
  `LENGTH vs = LENGTH ops` by
    (imp_res_tac LIST_REL_LENGTH >> fs[LENGTH_ZIP, arithmeticTheory.MIN_DEF]) >>
  `LENGTH flags = LENGTH ops /\ LENGTH dtys = LENGTH ops /\
   LENGTH ltys = LENGTH ops /\ LENGTH xs = LENGTH ops /\
   LENGTH vs = LENGTH ops /\ MAP SND xs = ltys` by
    (fs[LIST_REL_EL_EQN, Abbr `flags`, Abbr `dtys`, Abbr `ltys`, Abbr `xs`, MAP_ZIP]) >>
  `EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
              is_bytestring_type (expr_type e)) args` by
    (drule_all supported_pure_exprs_bytestring_iff >> simp[]) >>
  `log_eval_view cenv args sa xs sm` by
    (simp[log_eval_view_def, LIST_REL_EL_EQN, Abbr `xs`, Abbr `ltys`, EL_ZIP, EL_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `MAP SND ops = _` (mp_tac o Q.AP_TERM `EL n`) >>
     fs[EVERY_EL, EL_MAP]) >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops ops flags)) sm` >>
  rename1 `compile_log_topic_ops _ sm = (topic_ops,st)` >>
  `compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (topic_ops,st)` by
    (qpat_assum `log_eval_view _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [log_eval_view_def]) >>
     gvs[] >> drule split_log_ops_view >>
     disch_then (qspec_then `flags` strip_assume_tac) >>
     metis_tac[]) >>
  suspend "indexed_topics"
QED

Resume log_declared_suffix_path[indexed_topics]:
  `EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
               (!lab. FST p <> Label lab)) xs` by
    (fs[EVERY_EL, Abbr `xs`, EL_ZIP, EL_MAP] >> metis_tac[]) >>
  `LIST_REL (\arg v. expr_val_rel cx (SND arg) v (FST arg) s /\
      expr_val_at cenv cx (SND arg) sa sm es v (FST arg) s /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
        value_has_type tv v) xs vs` by
    (fs[LIST_REL_EL_EQN, Abbr `xs`, Abbr `ltys`, EL_ZIP, EL_MAP,
        pairTheory.UNCURRY] >> rpt strip_tac >>
     qpat_x_assum `!n. _ ==> event_arg_compatible _ _ /\ _`
       (qspec_then `n` mp_tac) >>
     simp[EL_ZIP, LENGTH_ZIP, arithmeticTheory.MIN_DEF, pairTheory.UNCURRY] >>
     metis_tac[]) >>
  `EVERY (\p. SND p ==> supported_scalar_type (SND (FST p))) (ZIP (xs,flags))` by
    (fs[EVERY_EL, LIST_REL_EL_EQN, Abbr `xs`, Abbr `ltys`, Abbr `flags`,
        EL_ZIP, EL_MAP, pairTheory.UNCURRY] >> rpt strip_tac >>
     qpat_x_assum `!n. _ ==> event_arg_compatible _ _ /\ _`
       (qspec_then `n` mp_tac) >>
     simp[EL_ZIP, LENGTH_ZIP, arithmeticTheory.MIN_DEF, pairTheory.UNCURRY] >>
     strip_tac >> metis_tac[scalar_event_arg_compatible]) >>
  qabbrev_tac `indexed = MAP FST (FILTER SND (ZIP (xs,flags)))` >>
  qabbrev_tac `ivs = MAP FST (FILTER SND (ZIP (vs,flags)))` >>
  `EVERY (supported_scalar_type o SND) indexed` by
    fs[Abbr `indexed`, EVERY_MAP, EVERY_FILTER, combinTheory.o_DEF] >>
  `LIST_REL (\arg v. expr_val_rel cx (SND arg) v (FST arg) s /\
      expr_val_at cenv cx (SND arg) sa sm es v (FST arg) s /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
        value_has_type tv v) indexed ivs` by
    (simp[Abbr `indexed`, Abbr `ivs`] >>
     irule log_indexed_selection_rel >> simp[]) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
        value_has_type tv v) indexed ivs` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     qpat_x_assum `LIST_REL _ indexed ivs` mp_tac >>
     qpat_x_assum `EVERY _ indexed` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[LIST_REL_EL_EQN, EVERY_EL, combinTheory.o_DEF] >>
     rpt strip_tac >>
     `supported_scalar_type (SND (EL n indexed))` by metis_tac[] >>
     qpat_x_assum `!n. _ ==> expr_val_rel _ _ _ _ _ /\ _`
       (qspec_then `n` mp_tac) >>
     Cases_on `EL n indexed` >>
     simp[log_arg_rel_def] >> strip_tac >>
     Cases_on `SND (EL n indexed)` >>
     gvs[supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
     irule log_arg_clear_base >> metis_tac[]) >>
  `EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
               (!lab. FST p <> Label lab)) indexed` by
    (simp[Abbr `indexed`] >> irule log_indexed_selection_every >> simp[]) >>
  `compile_log_topic_ops
     (MAP (\p. (FST p,is_bytestring_type (SND p))) indexed) sm = (topic_ops,st)` by
    (qspecl_then [`xs`, `flags`] mp_tac stmtSimLogTopicsTheory.split_log_ops_select >>
     simp[] >> strip_tac >>
     fs[Abbr `indexed`, MAP_MAP_o, combinTheory.o_DEF]) >>
  `encode_indexed_event_topics (REPLICATE (LENGTH indexed) T)
     (MAP SND indexed) ivs = SOME topics` by
    (qspecl_then [`xs`, `vs`, `flags`] mp_tac log_indexed_encoding_select >>
     simp[Abbr `indexed`, Abbr `ivs`, Abbr `ltys`]) >>
  drule_all compile_log_topic_ops_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  suspend "topics_frame"
QED

Resume log_declared_suffix_path[topics_frame]:
  `EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
               (!lab. FST p <> Label lab))
    (MAP (\p. (FST p,is_bytestring_type (SND p))) indexed)` by
    fs[EVERY_MAP] >>
  drule_all compile_log_topic_ops_frontier >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `wb_frame cenv es es sm s u` by
    (irule log_readonly_frame >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
   u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `u with vs_vars := s.vs_vars = s`
       (mp_tac o Q.AP_TERM `\v. (v.vs_memory,v.vs_allocas,v.vs_alloca_next,
         v.vs_labels,v.vs_halted,v.vs_current_bb,v.vs_inst_idx)`) >> simp[]) >>
  `!arg v. MEM arg xs /\ expr_val_rel cx (SND arg) v (FST arg) s /\
       expr_val_at cenv cx (SND arg) sa sm es v (FST arg) s ==>
     expr_val_rel cx (SND arg) v (FST arg) u /\
       expr_val_at cenv cx (SND arg) sa st es v (FST arg) u` by
    (rpt gen_tac >> strip_tac >>
     `(!x. FST arg = Var x ==> not_fresh_at sm x) /\
      (!lab. FST arg <> Label lab)` by (fs[EVERY_MEM] >> metis_tac[]) >>
     `eval_operand (FST arg) u = eval_operand (FST arg) s` by
       (Cases_on `FST arg` >> fs[eval_operand_def]) >>
     conj_tac
     >- fs[expr_val_rel_def] >>
     irule (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `es` |-> `es`,
       `ee` |-> `es`, `sb` |-> `sm`, `s` |-> `s`] log_frame_placement) >> simp[] >>
     qexistsl_tac [`ctx`, `es`, `func`, `s`, `sm`] >> simp[]) >>
  drule log_topics_straight >> strip_tac >>
  `same_blocks sm st /\ st.cs_current_bb = sm.cs_current_bb` by
    fs[inst_extends_def, same_blocks_def] >>
  Cases_on `SND (split_log_ops ops flags) = []`
  >- suspend "empty_suffix" >>
  `?src s1 s2 dst s3 len s4.
    compile_alloc_buffer
      (MAX 32 (SUM (MAP (type_memory_bytes cenv)
        (log_non_indexed_types flags dtys)))) st = (src,s1) /\
    compile_log_store_data cenv (SND (split_log_ops ops flags))
      (log_non_indexed_types flags dtys) src.buf_operand 0 s1 = ((),s2) /\
    compile_alloc_buffer
      (MAX 32 (abi_size_bound cenv.ce_struct_fields
        (TupleT (log_non_indexed_types flags dtys)))) s2 = (dst,s3) /\
    compile_abi_encode_to_buf dst.buf_operand src.buf_operand
      (type_to_abi_enc_info cenv.ce_struct_fields cenv
        (TupleT (log_non_indexed_types flags dtys))) s3 = (len,s4) /\
    emit_inst LOG
      (Lit (n2w (LENGTH (Lit (n2w h)::topic_ops))) ::
        REVERSE (Lit (n2w h)::topic_ops) ++ [len;dst.buf_operand]) [] s4 = ((),sb)` by
    (mp_tac (Q.INST [`ys` |-> `ops`, `topics` |-> `topic_ops`,
       `data_ops` |-> `SND (split_log_ops ops flags)`] compile_log_data_trace_declared) >>
     simp[]) >>
  pop_assum strip_assume_tac >>
  drule_all log_declared_data_stage_code >> strip_tac >>
  drule_all log_declared_data_allocation_sites >> strip_tac >>
  drule_all log_declared_data_encoder_sites >> strip_tac >>
  suspend "source_allocation"
QED

Resume log_declared_suffix_path[empty_suffix]:
  `LENGTH (FILTER ($~) flags) = 0` by
    (drule_all split_log_ops_lengths >> simp[]) >>
  `log_non_indexed_types flags dtys = [] /\
   log_non_indexed_values flags vs = []` by
    (qspecl_then [`flags`, `dtys`, `vs`] mp_tac log_non_indexed_lengths >> simp[]) >>
  `avs = []` by fs[Once vyper_to_abi_def] >>
  `SND (split_log_ops xs flags) = []` by
    (qspecl_then [`xs`, `flags`] mp_tac split_log_ops_lengths >> simp[]) >>
  `emit_inst LOG
    (Lit (n2w (LENGTH (Lit (n2w h)::topic_ops))) ::
      REVERSE (Lit (n2w h)::topic_ops) ++ [Lit 0w;Lit 0w]) [] st = ((),sb)` by
    (drule_all compile_log_empty_trace >> strip_tac >>
     qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `LENGTH (Lit (n2w h)::topic_ops) < dimword (:256)` by
    (drule_all log_emitted_topic_count_exact >>
     simp[dimword_def]) >>
  `eval_operands (Lit (n2w h)::topic_ops) u = SOME (n2w h::topics)` by
    (drule log_operands_values >> simp[eval_operands_def, eval_operand_def]) >>
  `eval_operand (Lit 0w) u = SOME (0w:bytes32)` by simp[eval_operand_def] >>
  drule_all compile_log_emit_run >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `inst_extends st sb` by metis_tac[inst_extends_emit_inst] >>
  `run_inst_seq (emitted_insts sm sb) s = OK v` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `st`] >>
     simp[] >> metis_tac[inst_extends_emit_inst]) >>
  `inst_extends sm sb /\ same_blocks sm sb` by
    (drule inst_extends_emit_inst >> strip_tac >>
     drule emit_inst_extends >> strip_tac >>
     `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
     fs[inst_extends_def,same_blocks_def]) >>
  `emitted_insts sm sb = emitted_insts sm st ++ emitted_insts st sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sm sb)` by
    (drule log_topics_opcode_shape >> strip_tac >>
     drule emitted_insts_emit_inst >>
     simp[mk_inst_def, is_terminator_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `fn_has_code sm sb func`
       (qx_choose_then `prefix_bb` strip_assume_tac o CONJUNCT2 o
        REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `prefix_bb` >>
     gvs[same_blocks_def,inst_extends_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1,DROP_LENGTH_NIL,APPEND_ASSOC] >>
     REWRITE_TAC [GSYM LENGTH_APPEND] >> simp[DROP_LENGTH_NIL]) >>
  pop_assum strip_assume_tac >>
  `gas_path ctx func s 0 (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qspecl_then [`emitted_insts sm sb`, `s`, `v`, `ctx`, `func`, `bb`]
       mp_tac tuple_run_inst_seq_gas_path >>
     impl_tac >- fs[EVERY_MEM] >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
       fs[FILTER_EQ_NIL, EVERY_MEM] >> simp[]) >>
  suspend "empty_post"
QED

Resume log_declared_suffix_path[empty_post]:
  `~block_is_terminated sb` by metis_tac[logComposeFactsTheory.log_emit_not_terminated] >>
  `v.vs_memory = s.vs_memory /\ v.vs_allocas = s.vs_allocas /\
   v.vs_halted = s.vs_halted /\ v.vs_current_bb = s.vs_current_bb /\
   v.vs_vars = u.vs_vars` by
    (qpat_x_assum `v with vs_logs := u.vs_logs = u`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas,z.vs_halted,
         z.vs_current_bb,z.vs_vars)`) >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x v = lookup_var x s` by
    (rpt strip_tac >> fs[lookup_var_def]) >>
  `stmt_state_rel ctx func cenv cx
    (es with logs := es.logs ++
      [<|logger := cx.txn.target; topics := n2w h::topics;
         data := []|>]) v` by
    fs[mem_bytes_at_def, wordsTheory.w2w_id] >>
  `alloca_frame cenv es sm s cenv
    (es with logs := es.logs ++
      [<|logger := cx.txn.target; topics := n2w h::topics;
         data := []|>]) v` by
    (`!op w. (!z. op = Var z ==> not_fresh_at sm z) /\
        (!lab. op <> Label lab) /\ eval_operand op s = SOME w ==>
        eval_operand op v = SOME w` by
       (rpt strip_tac >> Cases_on `op` >> fs[eval_operand_def] >> metis_tac[]) >>
     irule (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `cx` |-> `cx`,
       `s` |-> `s`, `es` |-> `es`, `sm` |-> `sm`] log_suffix_alloca_frame) >>
     simp[] >> metis_tac[]) >>
  `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `enc (Tuple []) (ListV []) = []` by
    simp[contractABITheory.enc_def, listTheory.REV_DEF] >>
  qexists_tac `v with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_post_def, stmt_lands_def,
       stmt_state_rel_inst_idx, cenv_top_ext_refl, wordsTheory.w2w_id,
       Once vyper_to_abi_def, Excl "enc_def"] >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  irule alloca_frame_same_state >> qexists_tac `v` >> simp[]
QED

Resume log_declared_suffix_path[source_allocation]:
  qabbrev_tac `tys = log_non_indexed_types flags dtys` >>
  qabbrev_tac `cap = MAX 32 (SUM (MAP (type_memory_bytes cenv) tys))` >>
  imp_res_tac compile_alloc_buffer_extends >>
  `same_blocks st s1` by
    (qpat_assum `compile_alloc_buffer cap st = (src,s1)`
       (strip_assume_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA [Lit(n2w cap)] st = (src.buf_operand,s1)`
       (mp_tac o MATCH_MP emit_op_extends) >> simp[]) >>
  `ci_mono s1 s2` by
    (qspecl_then [`cenv`, `SND (split_log_ops ops flags)`,
       `tys`, `src.buf_operand`, `0`, `s1`]
       mp_tac compile_log_store_data_ci_mono >> simp[]) >>
  `cs_extends s3 s4` by metis_tac[cs_extends_abi_encode] >>
  `cs_extends s4 sb` by
    (drule emit_inst_extends >> strip_tac >>
     irule cs_extends_same_block >>
     simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  `cs_extends st s2` by
    (irule cs_extends_trans >> qexists_tac `s1` >> fs[ci_mono_def]) >>
  `cs_extends st s3` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends st sb` by
    (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends sm st` by
    (irule cs_extends_same_block >>
     fs[same_blocks_def,inst_extends_def,IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sm st func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sm`] >>
     simp[cs_extends_refl]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm st) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm st) = LENGTH st.cs_current_insts` by
    (qpat_assum `fn_has_code sm st func`
       (qx_choose_then `prefix_bb` strip_assume_tac o CONJUNCT2 o
        REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `prefix_bb` >>
     gvs[same_blocks_def,inst_extends_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1,DROP_LENGTH_NIL,APPEND_ASSOC] >>
     REWRITE_TAC [GSYM LENGTH_APPEND] >> simp[DROP_LENGTH_NIL]) >>
  pop_assum strip_assume_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sm st)` by
    metis_tac[log_topics_opcode_shape] >>
  `gas_path ctx func s 0 (OK (u with vs_inst_idx := LENGTH st.cs_current_insts))` by
    (qspecl_then [`emitted_insts sm st`, `s`, `u`, `ctx`, `func`, `bb`]
       mp_tac tuple_run_inst_seq_gas_path >>
     impl_tac >- fs[EVERY_MEM] >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm st) = []` by
       fs[FILTER_EQ_NIL, EVERY_MEM] >> simp[]) >>
  qabbrev_tac `ut = u with vs_inst_idx := LENGTH st.cs_current_insts` >>
  `cap < dimword (:256)` by
    (fs[Abbr `cap`, arithmeticTheory.MAX_DEF, dimword_def] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es ut` by
    simp[Abbr `ut`, stmt_state_rel_inst_idx] >>
  qspecl_then [`ut`, `s1`] strip_assume_tac log_fresh_limit_exists >>
  `?a p. run_inst_seq (emitted_insts st s1) ut = OK a /\
    eval_operand src.buf_operand a = SOME (n2w p) /\ src.buf_size = cap /\
    p+cap < dimword (:256) /\ FLOOKUP a.vs_allocas st.cs_next_id = SOME (p,cap) /\
    stmt_state_rel ctx func cenv cx es a /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op a = eval_operand op ut) /\
    a.vs_memory = ut.vs_memory /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap ut a /\
    inst_extends st s1` by
    (drule_all log_buffer_allocate >> strip_tac >>
     qexistsl_tac [`t`, `p`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  suspend "source_ready"
QED

Resume log_declared_suffix_path[source_ready]:
  `!aid row. FLOOKUP ut.vs_allocas aid = SOME row ==>
    FLOOKUP a.vs_allocas aid = SOME row` by
    (qpat_assum `abi_builtin_allocation_frame _ _ _ ut a` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_builtin_allocation_frame_def, abi_builtin_allocate_state_def] >>
     strip_tac >> Cases_on `FLOOKUP ut.vs_allocas st.cs_next_id = NONE` >>
     fs[FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `aid = st.cs_next_id` >> fs[]) >>
  `!x. not_fresh_at st x ==> lookup_var x a = lookup_var x ut` by
    (rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _`
       (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  `wb_frame cenv es es st ut a` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`st`, `ut`] >>
     simp[wb_frame_refl]) >>
  `!arg v. MEM arg xs /\ expr_val_rel cx (SND arg) v (FST arg) s /\
      expr_val_at cenv cx (SND arg) sa sm es v (FST arg) s ==>
    expr_val_rel cx (SND arg) v (FST arg) a /\
      expr_val_at cenv cx (SND arg) sa st es v (FST arg) a` by
    (rpt gen_tac >> strip_tac >>
     `expr_val_rel cx (SND arg) v (FST arg) u /\
      expr_val_at cenv cx (SND arg) sa st es v (FST arg) u` by metis_tac[] >>
     `(!x. FST arg = Var x ==> not_fresh_at st x) /\ (!lab. FST arg <> Label lab)` by
       (fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
     `eval_operand (FST arg) a = eval_operand (FST arg) u` by
       (Cases_on `FST arg` >> fs[Abbr `ut`, eval_operand_def, lookup_var_def] >>
        metis_tac[]) >>
     conj_tac >- (fs[expr_val_rel_def, Abbr `ut`] >> metis_tac[]) >>
     irule (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `es` |-> `es`,
       `ee` |-> `es`, `sb` |-> `st`, `s` |-> `ut`] log_frame_placement) >> simp[] >>
     qexistsl_tac [`ctx`, `es`, `func`, `st`, `ut`] >>
     fs[Abbr `ut`, expr_val_at_def, eval_operand_def, local_region_def,
        lookup_var_def] >> rpt strip_tac >>
     qpat_x_assum `!tv. evaluate_type _ (SND arg) = _ /\ _ ==> val_wf _ v /\ _`
       (qspec_then `tv` mp_tac) >> simp[]) >>
  `allocas_non_overlapping a` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `cs_extends s2 sb` by
    (irule cs_extends_trans >> qexists_tac `s3` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s1 sb` by
    (irule cs_extends_trans >> qexists_tac `s2` >> fs[ci_mono_def]) >>
  `fn_has_code st s1 func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sm`] >>
     simp[cs_extends_refl]) >>
  `!name lo sz. local_region cenv es.scopes a name lo sz ==>
    lo+sz <= p \/ p+cap <= lo` by
    (rpt strip_tac >> drule_all log_buffer_clear_of_locals >> decide_tac) >>
  `!arg v. MEM arg xs /\ expr_val_rel cx (SND arg) v (FST arg) s /\
      expr_val_at cenv cx (SND arg) sa sm es v (FST arg) s ==>
    log_source_apart cx p (SUM (MAP (type_memory_bytes cenv) tys)) arg v a` by
    (rpt gen_tac >> strip_tac >>
     `expr_val_at cenv cx (SND arg) sa st es v (FST arg) a` by metis_tac[] >>
     `log_source_apart cx p cap arg v a` by
       (Cases_on `arg` >>
        irule (Q.INST [`cenv` |-> `cenv`, `dest` |-> `st.cs_next_id`, `es` |-> `es`,
          `sa` |-> `sa`, `sm` |-> `st`] log_allocated_source_apart) >> simp[] >>
         qexistsl_tac [`cenv`, `es`, `sa`, `st`] >> fs[] >>
         qpat_x_assum `!name lo sz. local_region cenv es.scopes a name lo sz ==> _` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
     `SUM (MAP (type_memory_bytes cenv) tys) <= cap` by
       simp[Abbr `cap`, arithmeticTheory.MAX_LE] >>
     Cases_on `arg` >> fs[log_source_apart_def] >>
     rpt strip_tac >> first_x_assum drule_all >> decide_tac) >>
  suspend "packing_selection"
QED

Resume log_declared_suffix_path[packing_selection]:
  `!fl os ls ds.
    LENGTH fl = LENGTH os /\ LENGTH ls = LENGTH os /\ LENGTH ds = LENGTH os ==>
    select_log_args F fl (ZIP (os,ZIP (ls,ds))) =
      ZIP (SND (split_log_ops os fl),
        ZIP (log_non_indexed_types fl ls,log_non_indexed_types fl ds))` by
    (rpt (pop_assum kall_tac) >> Induct_on `fl`
     >- (rpt gen_tac >> Cases_on `os` >>
         simp[select_log_args_def, log_non_indexed_types_def, split_log_ops_def]) >>
     rpt gen_tac >> rename1 `LENGTH (flag::fl)` >>
     Cases_on `os` >- simp[] >>
     rename1 `select_log_args F (flag::fl) (ZIP (arg::orest,_))` >>
     Cases_on `ls` >- simp[] >> Cases_on `ds` >- simp[] >>
     strip_tac >> Cases_on `flag` >> Cases_on `arg` >>
     simp[select_log_args_def, log_non_indexed_types_def, split_log_ops_def,
          pairTheory.UNCURRY] >> first_x_assum irule >> fs[]) >>
  `LIST_REL (\(flag,((op,sty),(lty,dty))) v. ~flag ==>
      event_arg_compatible dty lty /\ type_widens_to (get_tenv cx) lty dty /\
      (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
      (?ltv dtv. evaluate_type (get_tenv cx) lty = SOME ltv /\
        evaluate_type (get_tenv cx) dty = SOME dtv /\
        value_has_type ltv v /\ value_has_type dtv v /\
        val_wf ltv v /\ val_wf dtv v) /\
      expr_val_rel cx lty v op a /\
      (!w tv. ~is_word_type lty /\ ~is_bytestring_type lty /\
        eval_operand op a = SOME w /\ evaluate_type (get_tenv cx) lty = SOME tv ==>
        w2n w + type_memory_size tv < dimword (:256)) /\
      log_source_apart cx p (SUM (MAP (type_memory_bytes cenv) tys)) (op,lty) v a)
    (ZIP (flags,ZIP (ops,ZIP (ltys,dtys)))) vs` by
    (simp[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, LENGTH_ZIP, arithmeticTheory.MIN_DEF,
          pairTheory.UNCURRY, Abbr `flags`, Abbr `ltys`, Abbr `dtys`] >>
     rpt strip_tac >>
     qpat_assum `LIST_REL _ (ZIP (ops,ZIP (args,fields))) vs`
       (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[EL_ZIP,LENGTH_ZIP,arithmeticTheory.MIN_DEF,pairTheory.UNCURRY] >>
     Cases_on `EL n ops` >> rename1 `EL n ops = (argop,sty)` >>
     Cases_on `EL n fields` >> rename1 `EL n fields = (decl_arg,flag_n)` >>
     Cases_on `decl_arg` >> rename1 `decl_arg = (name,dty)` >>
     simp[] >> strip_tac >>
     `MEM (argop,expr_type (EL n args)) xs` by
       (simp[Abbr `xs`, MEM_EL] >> qexists_tac `n` >> simp[EL_ZIP,EL_MAP]) >>
     `expr_val_rel cx (expr_type (EL n args)) (EL n vs) argop a /\
      log_source_apart cx p (SUM (MAP (type_memory_bytes cenv) tys))
        (argop,expr_type (EL n args)) (EL n vs) a` by
       (conj_tac
        >- (qpat_assum `!arg v. MEM arg xs /\ _ ==> expr_val_rel _ _ _ _ a /\ _`
              (fn th => if free_in ``a:venom_state`` (concl th) then
                (qspecl_then [`(argop,expr_type (EL n args))`, `EL n vs`]
                   (drule_all o SRULE [])) th
                else NO_TAC) >> strip_tac >> simp[]) >>
        qpat_assum `!arg v. _ ==> log_source_apart _ _ _ arg v a`
          (qspecl_then [`(argop,expr_type (EL n args))`, `EL n vs`]
            (drule_all o SRULE [])) >> simp[]) >>
     `(!x. argop = Var x ==> not_fresh_at sm x) /\ (!lab. argop <> Label lab)` by
       (qpat_assum `EVERY _ ops`
          (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `eval_operand argop a = eval_operand argop s` by
       (pop_assum mp_tac >>
        qpat_assum `!x. argop = Var x ==> not_fresh_at sm x` mp_tac >>
        qpat_assum `!x. not_fresh_at st x ==> _`
          (fn th => if free_in ``a:venom_state`` (concl th) then mp_tac th else NO_TAC) >>
        qpat_assum `!z. not_fresh_at sm z ==> _`
          (fn th => if free_in ``s:venom_state`` (concl th) then mp_tac th else NO_TAC) >>
        qpat_assum `sm.cs_next_var <= st.cs_next_var` mp_tac >>
        qunabbrev_tac `ut` >> rpt (pop_assum kall_tac) >>
        rpt strip_tac >> Cases_on `argop` >>
        fs[eval_operand_def,lookup_var_def] >> metis_tac[not_fresh_at_mono]) >>
     fs[]) >>
  `LIST_REL (\((op,sty),(lty,dty)) v.
      event_arg_compatible dty lty /\ type_widens_to (get_tenv cx) lty dty /\
      (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
      (?ltv dtv. evaluate_type (get_tenv cx) lty = SOME ltv /\
        evaluate_type (get_tenv cx) dty = SOME dtv /\
        value_has_type ltv v /\ value_has_type dtv v /\
        val_wf ltv v /\ val_wf dtv v) /\
      expr_val_rel cx lty v op a /\
      (!w tv. ~is_word_type lty /\ ~is_bytestring_type lty /\
        eval_operand op a = SOME w /\ evaluate_type (get_tenv cx) lty = SOME tv ==>
        w2n w + type_memory_size tv < dimword (:256)) /\
      log_source_apart cx p (SUM (MAP (type_memory_bytes cenv) tys)) (op,lty) v a)
    (ZIP (SND (split_log_ops ops flags),
      ZIP (log_non_indexed_types flags ltys,tys)))
    (log_non_indexed_values flags vs)` by
    (simp[Abbr `tys`,log_non_indexed_values_select] >>
     qpat_assum `!fl os ls ds. _ ==> select_log_args F fl _ = _`
       (qspecl_then [`flags`, `ops`, `ltys`, `dtys`] mp_tac) >>
     impl_tac >- simp[Abbr `flags`,Abbr `ltys`,Abbr `dtys`] >>
     disch_then (fn th => rewrite_tac [GSYM th]) >>
     irule select_log_args_rel >>
     simp[LENGTH_ZIP,arithmeticTheory.MIN_DEF,Abbr `flags`,Abbr `ltys`,Abbr `dtys`] >>
     pop_assum mp_tac >>
     simp[LIST_REL_EL_EQN,EL_ZIP,EL_MAP,LENGTH_ZIP,
          arithmeticTheory.MIN_DEF,pairTheory.UNCURRY] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >> metis_tac[]) >>
  suspend "packing_run"
QED

Resume log_declared_suffix_path[packing_run]:
  `s1.cs_next_var = st.cs_next_var + 1` by
    (qpat_assum `compile_alloc_buffer cap st = (src,s1)`
       (strip_assume_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA [Lit(n2w cap)] st = (src.buf_operand,s1)`
       (mp_tac o MATCH_MP placeMemoryCodeLayoutTheory.emit_op_next_var) >> simp[]) >>
  `!x. src.buf_operand = Var x ==> not_fresh_at s1 x` by
    fs[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  `sm.cs_next_var <= s1.cs_next_var` by decide_tac >>
  `EVERY (\arg. (!x. FST arg = Var x ==> not_fresh_at s1 x) /\
      (!lab. FST arg <> Label lab)) (SND (split_log_ops ops flags))` by
    (irule log_split_data_every >> simp[] >>
     qpat_assum `EVERY _ ops` mp_tac >>
     qpat_assum `sm.cs_next_var <= s1.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >>
     metis_tac[not_fresh_at_mono]) >>
  `LENGTH (SND (split_log_ops ops flags)) = LENGTH tys /\
   LENGTH (log_non_indexed_types flags ltys) = LENGTH tys` by
    (drule_all split_log_ops_lengths >> strip_tac >>
     qspecl_then [`flags`, `dtys`, `vs`] mp_tac log_non_indexed_lengths >>
     qspecl_then [`flags`, `ltys`, `vs`] mp_tac log_non_indexed_lengths >>
     simp[Abbr `tys`]) >>
  `p + cap <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ a` mp_tac >>
     qpat_assum `FLOOKUP a.vs_allocas st.cs_next_id = SOME (p,cap)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def,alloca_inv_def,alloca_next_valid_def] >>
     strip_tac >> strip_tac >> conj_tac
     >- (first_x_assum drule_all >> simp[]) >>
     drule_all alloca_room_next_lt >> simp[]) >>
  `p < dimword (:256) /\ s1.cs_current_bb = st.cs_current_bb` by
    (fs[inst_extends_def,same_blocks_def] >> decide_tac) >>
  `emitted_insts st s1 =
    [mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)]
      [STRING #"%" (toString st.cs_next_var)]]` by
    (qpat_assum `compile_alloc_buffer cap st = (src,s1)`
       (strip_assume_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA [Lit(n2w cap)] st = (src.buf_operand,s1)`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `?alloc_bb. lookup_block ut.vs_current_bb func.fn_blocks = SOME alloc_bb /\
    isPREFIX (emitted_insts st s1) (DROP ut.vs_inst_idx alloc_bb.bb_instructions) /\
    ut.vs_inst_idx + LENGTH (emitted_insts st s1) = LENGTH s1.cs_current_insts` by
    (qpat_assum `fn_has_code st s1 func`
       (qx_choose_then `prefix_bb` strip_assume_tac o CONJUNCT2 o
        REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `prefix_bb` >>
     gvs[Abbr `ut`,inst_extends_def,same_blocks_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1,DROP_LENGTH_NIL,APPEND_ASSOC] >>
     REWRITE_TAC [GSYM LENGTH_APPEND] >> simp[DROP_LENGTH_NIL]) >>
  pop_assum strip_assume_tac >>
  `a.vs_current_bb = st.cs_current_bb /\ ~a.vs_halted` by
    (qspecl_then [`emitted_insts st s1`, `ut`, `0`, `ctx`, `alloc_bb`]
       mp_tac exec_block_run_inst_seq >>
     impl_tac >- simp[mk_inst_def,is_terminator_def] >>
     fs[Abbr `ut`, abi_builtin_allocation_frame_def]) >>
  `gas_path ctx func ut 0 (OK (a with vs_inst_idx := LENGTH s1.cs_current_insts))` by
    (qspecl_then [`emitted_insts st s1`, `ut`, `a`, `ctx`, `func`, `alloc_bb`]
       mp_tac tuple_run_inst_seq_gas_path >>
     simp[mk_inst_def,is_terminator_def,Abbr `ut`]) >>
  qabbrev_tac `a1 = a with vs_inst_idx := LENGTH s1.cs_current_insts` >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name flds. FLOOKUP cenv.ce_struct_fields name = SOME flds ==>
     ALL_DISTINCT (MAP FST flds) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) flds) /\
   acyclic_struct_metadata cenv.ce_struct_fields` by
    (qpat_assum `expr_sim_inv cenv cx env es0`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     qpat_assum `body_inv tops ctx cenv cx`
       (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "packing_execute"
QED

Resume log_declared_suffix_path[packing_execute]:
  mp_tac (Q.INST [`cenv` |-> `cenv`, `ops` |-> `SND (split_log_ops ops flags)`,
    `dtys` |-> `tys`, `ltys` |-> `log_non_indexed_types flags ltys`,
    `buf` |-> `src.buf_operand`, `off` |-> `0`, `sa` |-> `s1`, `sb` |-> `s2`,
    `vs` |-> `log_non_indexed_values flags vs`, `s` |-> `a1`, `bw` |-> `n2w p`]
      compile_log_store_data_declared_path) >>
  impl_tac
  >- (simp[Abbr `a1`, w2n_n2w] >> rpt conj_tac
      >~ [`LIST_REL _ _ _ (* g *)`]
      >- (qpat_x_assum `LIST_REL _ (ZIP (SND (split_log_ops ops flags),_)) _` mp_tac >>
          simp[LIST_REL_EL_EQN,EL_ZIP,LENGTH_ZIP,arithmeticTheory.MIN_DEF,
               pairTheory.UNCURRY,expr_val_rel_def,eval_operand_def,log_source_apart_def] >>
          rpt (pop_assum kall_tac) >> rpt strip_tac >>
          first_x_assum (qspec_then `n` mp_tac) >> fs[] >> metis_tac[])
      >~ [`p + SUM _ <= _ (* g *)`]
      >- fs[Abbr `cap`,arithmeticTheory.MAX_DEF]
      >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `packed` strip_assume_tac) >>
  suspend "packing_frame"
QED

Resume log_declared_suffix_path[packing_frame]:
  `packed.vs_allocas = a1.vs_allocas /\ packed.vs_alloca_next = a1.vs_alloca_next /\
   packed.vs_fmp = a1.vs_fmp /\ packed.vs_labels = a1.vs_labels /\
   packed.vs_data_section = a1.vs_data_section /\
   packed.vs_accounts = a1.vs_accounts /\ packed.vs_transient = a1.vs_transient /\
   packed.vs_call_ctx = a1.vs_call_ctx /\ packed.vs_tx_ctx = a1.vs_tx_ctx /\
   packed.vs_block_ctx = a1.vs_block_ctx /\ packed.vs_logs = a1.vs_logs /\
   packed.vs_outcomes = a1.vs_outcomes /\ packed.vs_requests = a1.vs_requests /\
   packed.vs_pending_deletions = a1.vs_pending_deletions /\
   packed.vs_immutables = a1.vs_immutables /\ packed.vs_code = a1.vs_code` by
    (qpat_assum `packed with <|vs_vars := _; vs_memory := _;
       vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = a1`
      (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next,z.vs_fmp,z.vs_labels,
        z.vs_data_section,z.vs_accounts,z.vs_transient,z.vs_call_ctx,z.vs_tx_ctx,
        z.vs_block_ctx,z.vs_logs,z.vs_outcomes,z.vs_requests,z.vs_pending_deletions,
        z.vs_immutables,z.vs_code)`) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >>
     fs[cs_extends_def, inst_extends_def]) >>
  `!name entry local_ptr_name sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_ptr_name) sz) ==>
    lookup_var local_ptr_name packed = lookup_var local_ptr_name a1` by
    (rpt strip_tac >>
     `not_fresh_at s1 local_ptr_name` by
       (qpat_assum `local_ptrs_reserved cenv s1`
          (qspecl_then [`name`,`name`,`local_ptr_name`,`sz`,`sz`] mp_tac o
           CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >> simp[]) >>
     qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = _`
       (fn th => if free_in ``packed:venom_state`` (concl th) then
          (qspec_then `local_ptr_name` mp_tac) th else NO_TAC) >> simp[]) >>
  `!name lo sz. local_region cenv es.scopes a1 name lo sz ==>
    mem_bytes_at lo sz a1.vs_memory = mem_bytes_at lo sz packed.vs_memory` by
    (rpt strip_tac >>
     `local_region cenv es.scopes a name lo sz` by
       (qpat_x_assum `local_region cenv es.scopes a1 name lo sz` mp_tac >>
        simp[Abbr `a1`,local_region_def,lookup_var_def]) >>
     `lo+sz <= p \/ p+cap <= lo` by
       (qpat_assum `!name lo sz. local_region _ _ a _ _ _ ==> _`
          (qspecl_then [`name`,`lo`,`sz`] drule_all) >> simp[]) >>
     sym_tac >> first_x_assum irule >> fs[Abbr `cap`,arithmeticTheory.MAX_DEF]) >>
  `stmt_state_rel ctx func cenv cx es a1` by
    simp[Abbr `a1`,stmt_state_rel_inst_idx] >>
  `local_ptrs_rel func cenv es.scopes packed` by
    (irule (Q.SPECL [`func`,`cenv`,`es.scopes`,`a1`,`packed`] local_ptrs_rel_mem_agree) >>
     qexists_tac `a1` >> simp[] >>
     qpat_assum `stmt_state_rel ctx func cenv cx es a1`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def,state_rel_def]) >>
     rpt conj_tac
     >~ [`FLOOKUP _ _ = NONE (* sg *)`]
     >- (rpt (pop_assum kall_tac) >> rpt strip_tac >> fs[]) >>
     first_assum ACCEPT_TAC) >>
  suspend "packing_immutables"
QED

Resume log_declared_suffix_path[packing_immutables]:
  `!name tv v off.
    cenv.ce_is_ctor /\
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) packed.vs_memory =
      mem_bytes_at off (type_memory_size tv) a1.vs_memory` by
    (rpt strip_tac >>
     `off+type_memory_size tv <= p \/ p+cap <= off` by
       (drule_all log_buffer_clear_of_immutable >> decide_tac) >>
     first_x_assum irule >> fs[Abbr `cap`,arithmeticTheory.MAX_DEF]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es packed` by
    (`immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es a1` by
       fs[stmt_state_rel_def,state_rel_def,Abbr `a1`] >>
     qpat_x_assum `immutables_rel _ _ _ _ _ a1` mp_tac >>
     simp[immutables_rel_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     Cases_on `cenv.ce_is_ctor` >> fs[] >>
     `mem_bytes_at byte_offset (type_memory_size tv) packed.vs_memory =
      mem_bytes_at byte_offset (type_memory_size tv) a1.vs_memory` by
       (qpat_assum `!name tv v off. _ ==> mem_bytes_at off _ packed.vs_memory = _`
          (qspecl_then [`name`,`tv`,`v`,`byte_offset`] drule_all) >> simp[]) >>
     simp[] >> irule val_in_memory_mem_agree >>
     conj_tac >- (irule (cj 1 immutable_admissible_val_wf) >> simp[]) >>
     qexistsl_tac [`type_memory_size tv`, `a1.vs_memory`] >> simp[]) >>
  `state_rel func cenv cx es packed` by
    (irule (Q.SPECL [`func`,`cenv`,`cx`,`es`,`es`,`a1`,`packed`] state_rel_frame) >>
     simp[] >> qexists_tac `a1` >> fs[stmt_state_rel_def,Abbr `a1`]) >>
  `immutable_alloca_sep func cenv cx es packed` by
    (irule (Q.INST [`initial` |-> `a1`] abi_encode_caller_immutable_separation) >>
     simp[] >> qexists_tac `a1` >> fs[stmt_state_rel_def,Abbr `a1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> fs[]) >>
  `immutable_base_zero cenv packed` by
    (irule (Q.SPECL [`cenv`,`a1`,`packed`] immutable_base_zero_frame) >>
     simp[] >> qexists_tac `a1` >> fs[stmt_state_rel_def,Abbr `a1`] >> rpt strip_tac >>
     `not_fresh_at s1 x` by fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es packed` by
    (irule (Q.SPECL [`func`,`cenv`,`cx`,`es`,`a1`,`es`,`packed`,`ctx`]
      stmt_state_rel_allocas_frame) >>
     simp[] >> qexists_tac `a1` >> simp[Abbr `a1`,stmt_state_rel_inst_idx]) >>
  suspend "tuple_prepare"
QED

Resume log_declared_suffix_path[tuple_prepare]:
  qabbrev_tac `dvs = log_non_indexed_values flags vs` >>
  `tys <> []` by
    (Cases_on `tys` >> fs[] >>
     Cases_on `SND (split_log_ops ops flags)` >> fs[]) >>
  `EVERY (supported_place_type tops) tys` by
    (simp[Abbr `tys`,Abbr `flags`,Abbr `dtys`,log_non_indexed_types_select] >>
     qpat_x_assum `EVERY (\f. if SND f then _ else _) fields` mp_tac >>
     rpt (pop_assum kall_tac) >> Induct_on `fields`
     >- simp[select_log_args_def] >> gen_tac >>
     rename1 `EVERY _ (decl_arg::fields)` >>
     Cases_on `decl_arg` >> rename1 `EVERY _ ((decl,flag_h)::fields)` >>
     Cases_on `decl` >> rename1 `EVERY _ (((name,dty),flag_h)::fields)` >>
     Cases_on `flag_h` >> simp[select_log_args_def]) >>
  `LIST_REL (\dty v. ?tv. evaluate_type (get_tenv cx) dty = SOME tv /\
      value_has_type tv v /\ type_memory_bytes cenv dty = type_memory_size tv)
    tys dvs` by
    (qpat_x_assum `LIST_REL _ (ZIP (SND (split_log_ops ops flags),_)) _` mp_tac >>
     simp[LIST_REL_EL_EQN,EL_ZIP,LENGTH_ZIP,arithmeticTheory.MIN_DEF,
          pairTheory.UNCURRY,Abbr `dvs`] >> strip_tac >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!n. _ ==> event_arg_compatible _ _ /\ _`
       (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     rename1 `evaluate_type (get_tenv cx) (EL n tys) = SOME field_tv` >>
     qexists_tac `field_tv` >> simp[] >>
     irule (Q.SPECL [`cenv`,`EL n tys`,`cx`,`env`,`es0`,`field_tv`]
       expr_sim_inv_memory_size) >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es0`] >> simp[]) >>
  `SUM (MAP (type_memory_bytes cenv) tys) < dimword (:256)` by
    fs[Abbr `tys`,dimword_def] >>
  drule_all log_data_layout_aggregate_typed_tuple >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (TupleT tys) = SOME tuple_tv` >>
  `abi_enc_plan (get_tenv cx) (TupleT tys)
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys))` by
    (irule (Q.INST [`env` |-> `env`, `es` |-> `es0`, `tops` |-> `tops`, `ctx` |-> `ctx`]
      body_log_actual_tuple_abi_plan) >> simp[] >> conj_tac
     >- (qexistsl_tac [`ctx`,`tops`] >> simp[]) >>
     qexistsl_tac [`env`,`es0`] >> simp[]) >>
  `vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV dvs)) = SOME (ListV avs)` by
    simp[Once vyper_to_abi_def,Abbr `dvs`,Abbr `tys`] >>
  `type_memory_size tuple_tv <= cap` by fs[Abbr `cap`] >>
  drule_all log_plan_window_input >> strip_tac >>
  `w2n (n2w p : bytes32) = p` by simp[] >>
  qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
  simp[] >> strip_tac >>
  rename1 `abi_encoder_window_input _ enc_ty enc_val p cap packed.vs_memory` >>
  `LENGTH (enc enc_ty enc_val) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)` by
    (drule_all (cj 1 vyper_to_abi_enc_length_bound) >> strip_tac >>
     drule_all abi_props_vyper_typed >> strip_tac >>
     qpat_x_assum `LENGTH (enc _ _) <= vyper_abi_size_bound _ _` mp_tac >> simp[]) >>
  suspend "output_allocation"
QED

Resume log_declared_suffix_path[output_allocation]:
  qabbrev_tac `outcap = MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT tys))` >>
  `outcap < dimword (:256)` by
    (fs[Abbr `outcap`,Abbr `tys`,arithmeticTheory.MAX_DEF,dimword_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> fs[ci_mono_def]) >>
  qspecl_then [`packed`, `s3`] (qx_choose_then `outlim` strip_assume_tac)
    log_fresh_limit_exists >>
  mp_tac (Q.INST [`cap` |-> `outcap`, `sa` |-> `s2`, `sb` |-> `s3`,
    `buf` |-> `dst`, `s` |-> `packed`, `ce` |-> `cenv`, `limit_st` |-> `outlim`]
      log_buffer_allocate) >>
  impl_tac >- simp[Abbr `outcap`,Abbr `tys`] >>
  disch_then (qx_choose_then `out_raw` (qx_choose_then `db` strip_assume_tac)) >>
  `same_blocks s2 s3` by
    (qpat_assum `compile_alloc_buffer outcap s2 = (dst,s3)`
       (strip_assume_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA [Lit(n2w outcap)] s2 = (dst.buf_operand,s3)`
       (mp_tac o MATCH_MP emit_op_extends) >> simp[]) >>
  `FLOOKUP out_raw.vs_allocas st.cs_next_id = SOME (p,cap)` by
    (drule_at (Pat `abi_builtin_allocation_frame _ _ _ packed out_raw`)
       abi_builtin_allocation_frame_outside >> simp[Abbr `a1`]) >>
  `abi_decoder_operand_live s2.cs_next_var src.buf_operand` by
    (simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
       ASCIInumbersTheory.toString_11] >> fs[ci_mono_def] >> decide_tac) >>
  `eval_operand src.buf_operand packed = SOME (n2w p)` by
    (qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = _`
       (qspec_then `STRING #"%" (toString st.cs_next_var)` mp_tac) >>
     fs[Abbr `a1`,eval_operand_def,lookup_var_def,not_fresh_at_def,
        ASCIInumbersTheory.toString_11] >>
     qpat_x_assum `eval_operand src.buf_operand a = SOME (n2w p)` mp_tac >>
     simp[eval_operand_def,lookup_var_def]) >>
  `eval_operand src.buf_operand out_raw = SOME (n2w p)` by
    (qpat_assum `!op. abi_decoder_operand_live s2.cs_next_var op ==> _`
       (qspec_then `src.buf_operand` mp_tac) >> simp[]) >>
  `abi_encoder_window_input
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys))
    enc_ty enc_val p cap out_raw.vs_memory` by simp[] >>
  suspend "output_ready"
QED

Resume log_declared_suffix_path[output_ready]:
  `emitted_insts s2 s3 =
    [mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
      [STRING #"%" (toString s2.cs_next_var)]]` by
    (qpat_assum `compile_alloc_buffer outcap s2 = (dst,s3)`
       (strip_assume_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA [Lit(n2w outcap)] s2 = (dst.buf_operand,s3)`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `s3.cs_current_bb = s2.cs_current_bb` by fs[inst_extends_def,same_blocks_def] >>
  `?out_bb. lookup_block packed.vs_current_bb func.fn_blocks = SOME out_bb /\
    isPREFIX (emitted_insts s2 s3) (DROP packed.vs_inst_idx out_bb.bb_instructions) /\
    packed.vs_inst_idx + LENGTH (emitted_insts s2 s3) = LENGTH s3.cs_current_insts` by
    (qpat_assum `fn_has_code s2 s3 func`
       (qx_choose_then `prefix_bb` strip_assume_tac o CONJUNCT2 o
        REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `prefix_bb` >>
     qpat_assum `packed.vs_current_bb = s2.cs_current_bb` mp_tac >>
     qpat_assum `packed.vs_inst_idx = LENGTH s2.cs_current_insts` mp_tac >>
     qpat_assum `lookup_block s3.cs_current_bb func.fn_blocks = SOME prefix_bb` mp_tac >>
     qpat_assum `isPREFIX s3.cs_current_insts prefix_bb.bb_instructions` mp_tac >>
     qpat_assum `inst_extends s2 s3` mp_tac >>
     qpat_assum `same_blocks s2 s3` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[inst_extends_def,same_blocks_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1,DROP_LENGTH_NIL,APPEND_ASSOC] >>
     REWRITE_TAC [GSYM LENGTH_APPEND] >> simp[DROP_LENGTH_NIL]) >>
  pop_assum strip_assume_tac >>
  `out_raw.vs_current_bb = s3.cs_current_bb /\ ~out_raw.vs_halted` by
    (qspecl_then [`emitted_insts s2 s3`, `packed`, `0`, `ctx`, `out_bb`]
       mp_tac exec_block_run_inst_seq >>
     impl_tac >- simp[mk_inst_def,is_terminator_def] >>
     fs[abi_builtin_allocation_frame_def]) >>
  `gas_path ctx func packed 0
    (OK (out_raw with vs_inst_idx := LENGTH s3.cs_current_insts))` by
    (qspecl_then [`emitted_insts s2 s3`, `packed`, `out_raw`, `ctx`, `func`, `out_bb`]
       mp_tac tuple_run_inst_seq_gas_path >> simp[mk_inst_def,is_terminator_def]) >>
  qabbrev_tac `prepared = out_raw with vs_inst_idx := LENGTH s3.cs_current_insts` >>
  qabbrev_tac `ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys)` >>
  `stmt_state_rel ctx func cenv cx es prepared` by
    simp[Abbr `prepared`,stmt_state_rel_inst_idx] >>
  `s3.cs_next_var = s2.cs_next_var + 1` by
    (qpat_assum `compile_alloc_buffer outcap s2 = (dst,s3)`
       (strip_assume_tac o MATCH_MP abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA [Lit(n2w outcap)] s2 = (dst.buf_operand,s3)`
       (mp_tac o MATCH_MP emit_op_next_var) >> simp[]) >>
  `!x. src.buf_operand = Var x \/ dst.buf_operand = Var x ==> not_fresh_at s3 x` by
    (qpat_assum `src.buf_operand = Var _` mp_tac >>
     qpat_assum `dst.buf_operand = Var _` mp_tac >>
     qpat_assum `s3.cs_next_var = s2.cs_next_var + 1` mp_tac >>
     qpat_assum `s1.cs_next_var = st.cs_next_var + 1` mp_tac >>
     qpat_assum `ci_mono s1 s2` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[ci_mono_def,not_fresh_at_def,ASCIInumbersTheory.toString_11] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids s3 s4 /\
    FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32` by
    (rpt strip_tac >>
     `inst.inst_operands = [Lit 32w]` by metis_tac[] >>
     fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[dimword_def]) >>
  `abi_encoder_window_pre ctx func s3 s4 dst.buf_operand src.buf_operand ei
      enc_ty enc_val p cap db prepared` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `st` |-> `s3`,
       `en` |-> `s4`, `dstop` |-> `dst.buf_operand`, `srcop` |-> `src.buf_operand`,
       `ei` |-> `ei`, `at` |-> `enc_ty`, `av` |-> `enc_val`,
       `b` |-> `p`, `cap` |-> `cap`, `d` |-> `db`, `s` |-> `prepared`,
       `output_cap` |-> `outcap`, `output_id` |-> `s2.cs_next_id`,
       `source_cap` |-> `cap`, `source_id` |-> `st.cs_next_id`]
       (Q.INST [`src` |-> `srcop`, `dst` |-> `dstop`]
         log_encoder_window_pre_registered)) >>
     impl_tac
     >- (qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
           (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
         asm_rewrite_tac[] >>
         qpat_assum `abi_encoder_window_input ei enc_ty enc_val p cap out_raw.vs_memory` mp_tac >>
         qpat_assum `eval_operand src.buf_operand out_raw = SOME (n2w p)` mp_tac >>
         qpat_assum `eval_operand dst.buf_operand out_raw = SOME (n2w db)` mp_tac >>
         qpat_assum `src.buf_operand = Var _` mp_tac >>
         qpat_assum `dst.buf_operand = Var _` mp_tac >>
         qpat_assum `FLOOKUP out_raw.vs_allocas st.cs_next_id = SOME (p,cap)` mp_tac >>
         qpat_assum `FLOOKUP out_raw.vs_allocas s2.cs_next_id = SOME (db,outcap)` mp_tac >>
         qpat_assum `LENGTH (enc enc_ty enc_val) <= _` mp_tac >>
         qpat_assum `enc enc_ty enc_val = _` mp_tac >>
         qpat_assum `Abbrev (outcap = _)` mp_tac >>
         qpat_assum `Abbrev (prepared = _)` mp_tac >>
         qpat_assum `st.cs_next_id < s2.cs_next_id` mp_tac >>
         qpat_assum `out_raw.vs_current_bb = s3.cs_current_bb` mp_tac >>
         qpat_assum `s3.cs_current_bb = s2.cs_current_bb` mp_tac >>
         qpat_assum `~out_raw.vs_halted` mp_tac >> rpt (pop_assum kall_tac) >>
         simp[markerTheory.Abbrev_def,eval_operand_def,lookup_var_def] >>
         rpt strip_tac >> fs[arithmeticTheory.MAX_DEF] >> decide_tac) >> simp[]) >>
  `code_step enc_safe_opcode s3 s4` by
    (mp_tac (Q.SPECL [`dst.buf_operand`,`src.buf_operand`,`ei`]
       (cj 2 code_action_encoder_mutual)) >>
     REWRITE_TAC[code_action_def] >>
     disch_then (qspecl_then [`s3`,`len`,`s4`] mp_tac) >> asm_rewrite_tac[]) >>
  `label_step s3 s4` by
    (mp_tac (Q.SPECL [`dst.buf_operand`,`src.buf_operand`,`ei`]
       (cj 2 label_action_encoder_mutual)) >>
     REWRITE_TAC[label_action_def] >>
     disch_then (qspecl_then [`s3`,`len`,`s4`] mp_tac) >> asm_rewrite_tac[]) >>
  `frag_ops_free s3 s4 /\ ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code s3 s4)) /\
   ~MEM s4.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks s3 s4)))` by
    (drule (SRULE [GSYM enc_safe_opcode_def,ETA_THM] code_step_frag_facts) >>
     strip_tac >> simp[] >> metis_tac[label_step_current_excluded]) >>
  qabbrev_tac `encoded_post = \t.
    mem_bytes_at db (LENGTH (enc enc_ty enc_val)) t.vs_memory = enc enc_ty enc_val /\
    eval_operand len t = SOME (n2w (LENGTH (enc enc_ty enc_val))) /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
      [(db,LENGTH (enc enc_ty enc_val))] prepared t /\
    alloca_inv t /\ window_alloca_growth prepared t /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids s3 s4 /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
    (!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==>
      lookup_var x t = SOME w) /\
    t.vs_labels = prepared.vs_labels /\ abi_encode_exec_frame func prepared t` >>
  `?encoded. gas_path ctx func prepared 0 (OK encoded) /\
    encoded_post encoded /\ ~encoded.vs_halted /\
    encoded.vs_current_bb = s4.cs_current_bb /\
    encoded.vs_inst_idx = LENGTH s4.cs_current_insts` by
    (Cases_on `s3.cs_blocks = s4.cs_blocks`
     >- suspend "encode_straight" >> suspend "encode_cfg") >>
  rename1 `gas_path ctx func prepared 0 (OK encoded)` >>
  `mem_bytes_at db (LENGTH (enc enc_ty enc_val)) encoded.vs_memory = enc enc_ty enc_val /\
   eval_operand len encoded = SOME (n2w (LENGTH (enc enc_ty enc_val))) /\
   abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
      [(db,LENGTH (enc enc_ty enc_val))] prepared encoded /\
   alloca_inv encoded /\ window_alloca_growth prepared encoded /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids s3 s4 /\
     FLOOKUP encoded.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
   (!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==>
     lookup_var x encoded = SOME w) /\
   encoded.vs_labels = prepared.vs_labels /\ abi_encode_exec_frame func prepared encoded` by
    (qpat_assum `encoded_post encoded` mp_tac >>
     qpat_assum `Abbrev (encoded_post = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def] >>
     rpt strip_tac >> metis_tac[]) >>
  suspend "encode_frame"
QED

Resume log_declared_suffix_path[encode_straight]:
  `same_blocks s3 s4` by
    (`entry_shape s3 s4` by
       (qpat_assum `code_step enc_safe_opcode s3 s4`
          (strip_assume_tac o REWRITE_RULE[code_step_def]) >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `entry_shape s3 s4`
       (DISJ_CASES_THEN strip_assume_tac o REWRITE_RULE[entry_shape_def])
     >- (REWRITE_TAC[same_blocks_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `s4.cs_blocks = _ ++ [_] ++ s3.cs_blocks`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `s3.cs_blocks = s4.cs_blocks` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `?raw. abi_encode_concrete_result ctx func s3 s4 len enc_ty enc_val db prepared raw` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `s3.cs_blocks = s4.cs_blocks` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[abi_encode_concrete_contract_all,abi_encode_concrete_contract_def]) >>
  rename1 `abi_encode_concrete_result ctx func s3 s4 len enc_ty enc_val db prepared encoded_raw` >>
  `inst_extends s3 s4 /\
   run_inst_seq (emitted_insts s3 s4) prepared = OK encoded_raw /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s3 s4) /\
   window_strong_result ctx func s3 s4 len enc_ty enc_val db prepared
     (encoded_raw with vs_inst_idx := LENGTH s4.cs_current_insts)` by
    (qpat_assum `abi_encode_concrete_result _ _ _ _ _ _ _ _ _ encoded_raw`
       (strip_assume_tac o REWRITE_RULE[abi_encode_concrete_result_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encode_exec_frame func prepared
    (encoded_raw with vs_inst_idx := LENGTH s4.cs_current_insts)` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     qpat_assum `s3.cs_blocks = s4.cs_blocks` mp_tac >>
     qpat_assum `fn_has_code s3 s4 func` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts s3 s4) prepared = OK encoded_raw` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[abi_encode_no_block_body_frame_normalized]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS)
    (emitted_insts s3 s4)` by
    (qpat_assum `frag_ops_free s3 s4` mp_tac >>
     qpat_assum `s3.cs_blocks = s4.cs_blocks` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[frag_ops_free_def,frag_code_def,emitted_blocks_def,EVERY_MEM]) >>
  `?encode_bb. lookup_block prepared.vs_current_bb func.fn_blocks = SOME encode_bb /\
    isPREFIX (emitted_insts s3 s4) (DROP prepared.vs_inst_idx encode_bb.bb_instructions) /\
    prepared.vs_inst_idx + LENGTH (emitted_insts s3 s4) = LENGTH s4.cs_current_insts` by
    (qpat_assum `fn_has_code s3 s4 func`
       (qx_choose_then `prefix_bb` strip_assume_tac o CONJUNCT2 o
        REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `prefix_bb` >>
     qpat_assum `Abbrev (prepared = _)` mp_tac >>
     qpat_assum `out_raw.vs_current_bb = s3.cs_current_bb` mp_tac >>
     qpat_assum `lookup_block s4.cs_current_bb func.fn_blocks = SOME prefix_bb` mp_tac >>
     qpat_assum `isPREFIX s4.cs_current_insts prefix_bb.bb_instructions` mp_tac >>
     qpat_assum `inst_extends s3 s4` mp_tac >>
     qpat_assum `same_blocks s3 s4` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     gvs[markerTheory.Abbrev_def,inst_extends_def,same_blocks_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1,DROP_LENGTH_NIL,APPEND_ASSOC] >>
     REWRITE_TAC [GSYM LENGTH_APPEND] >> simp[DROP_LENGTH_NIL]) >>
  pop_assum strip_assume_tac >>
  `gas_path ctx func prepared 0
    (OK (encoded_raw with vs_inst_idx := LENGTH s4.cs_current_insts))` by
    (qspecl_then [`emitted_insts s3 s4`, `prepared`, `encoded_raw`, `ctx`, `func`, `encode_bb`]
       mp_tac tuple_run_inst_seq_gas_path >> impl_tac
     >- (rpt conj_tac
         >~ [`~prepared.vs_halted (* g *)`]
         >- (qpat_assum `~out_raw.vs_halted` mp_tac >>
             qpat_assum `Abbrev (prepared = _)` mp_tac >>
             rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def])
         >~ [`EVERY _ _ (* g *)`]
         >- (qpat_assum `EVERY (\i. ~is_terminator _) _` mp_tac >>
             qpat_assum `EVERY (\i. _ <> INVOKE /\ _ <> GAS) _` mp_tac >>
             rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
         first_assum ACCEPT_TAC) >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts s3 s4) = []` by
       (qpat_assum `EVERY (\i. _ <> INVOKE /\ _ <> GAS) _` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[FILTER_EQ_NIL,EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `prepared.vs_inst_idx + LENGTH (emitted_insts s3 s4) = _` mp_tac >>
     qpat_assum `FILTER _ (emitted_insts s3 s4) = []` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qexists_tac `encoded_raw with vs_inst_idx := LENGTH s4.cs_current_insts` >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `abi_encode_exec_frame func prepared _` mp_tac >>
  qpat_assum `gas_path ctx func prepared 0 _` mp_tac >>
  qpat_assum `Abbrev (encoded_post = _)` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def] >> rpt strip_tac >>
  fs[window_strong_result_def,abi_encoder_window_result_def,eval_operand_def,lookup_var_def] >>
  rpt strip_tac >>
  Cases_on `inst.inst_id IN window_alloca_sites func (frag_ids s3 s4)`
  >- metis_tac[] >>
  fs[window_alloca_sites_def] >> metis_tac[]
QED


Resume log_declared_suffix_path[encode_cfg]:
  `!L ids obs.
    LENGTH ids = LENGTH s3.cs_current_insts /\
    fn_has_code (start_relabel L ids s3) (start_swap s3 L ids s4) obs /\
    fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
    (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
      i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
    (!bb. lookup_block s4.cs_current_bb obs.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
    ?t. encoded_post t /\ ~t.vs_halted /\
      t.vs_current_bb = s4.cs_current_bb /\
      t.vs_inst_idx = LENGTH s4.cs_current_insts /\
      abi_decode_sim ctx obs (prepared with vs_current_bb := L) t` by
    suspend "encoder_observer" >>
  `cs_extends s3 s4` by metis_tac[cs_extends_abi_encode] >>
  `s4.cs_current_insts <> []` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     qpat_assum `s3.cs_blocks <> s4.cs_blocks` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[abi_encoder_core_exit_nonempty]) >>
  `(!t rd. encoded_post t ==> encoded_post (t with vs_returndata := rd)) /\
   (!t prev. encoded_post t ==> encoded_post (t with vs_prev_bb := prev))` by
    (qpat_assum `Abbrev (encoded_post = _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     REWRITE_TAC[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >> BETA_TAC >>
     conj_tac >> (rpt gen_tac >> strip_tac >> rpt conj_tac
     >~ [`abi_encoder_registered_effect _ _ _ _ (* g *)`]
     >- (qpat_assum `abi_encoder_registered_effect _ _ prepared t` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[abi_encoder_registered_effect_def] >>
         strip_tac >> first_assum ACCEPT_TAC)
     >~ [`alloca_inv _ (* g *)`]
     >- (qpat_assum `alloca_inv t` mp_tac >> rpt (pop_assum kall_tac) >>
         simp[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def] >>
         strip_tac >> first_assum ACCEPT_TAC)
     >~ [`window_alloca_growth _ _ (* g *)`]
     >- (qpat_assum `window_alloca_growth prepared t` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[window_alloca_growth_def] >>
         strip_tac >> first_assum ACCEPT_TAC)
     >~ [`abi_encode_exec_frame _ _ _ (* g *)`]
     >- metis_tac[abi_encode_exec_frame_bridge_updates]
     >~ [`eval_operand len _ = _ (* g *)`]
     >- (qpat_assum `eval_operand len t = _` mp_tac >> rpt (pop_assum kall_tac) >>
         Cases_on `len` >> simp[eval_operand_def,lookup_var_def])
     >~ [`lookup_var _ _ (* sg *)`]
     >- (qpat_assum `!x w. _ ==> lookup_var x t = SOME w` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[lookup_var_def]) >>
     simp[] >> first_assum ACCEPT_TAC)) >>
  mp_tac (Q.SPECL [`ctx`,`s3`,`s4`,`encoded_post`,`func`,`prepared`]
    abi_decode_sim_gas_path_relabel) >>
  impl_tac >- (simp[Abbr `prepared`] >> first_assum ACCEPT_TAC) >>
  simp[gas_marked_path_def]
QED

Resume log_declared_suffix_path[encoder_observer]:
  rpt gen_tac >> strip_tac >>
  `compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei
    (start_relabel L ids s3) = (len,start_swap s3 L ids s4)` by
    (mp_tac (Q.SPECL [`dst.buf_operand`,`src.buf_operand`,`ei`]
      (cj 2 entry_action_encoder_mutual)) >>
     rewrite_tac[entry_action_def] >>
     disch_then (qspecl_then [`s3`,`s3`,`len`,`s4`,`L`,`ids`] mp_tac) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ s3 = (len,s4)` mp_tac >>
     qpat_assum `LENGTH ids = LENGTH s3.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[entry_shape_refl,start_swap_initial]) >>
  `abi_encoder_window_pre (ctx with ctx_functions := [obs]) obs
    (start_relabel L ids s3) (start_swap s3 L ids s4)
    dst.buf_operand src.buf_operand ei enc_ty enc_val p cap db
    (prepared with vs_current_bb := L)` by
    (qpat_assum `abi_encoder_window_pre ctx func _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
     `alloca_room (ctx with ctx_functions := [obs]) obs prepared` by
       (irule abi_encode_bridge_local_room >> metis_tac[]) >>
     qpat_assum `abi_encoder_window_pre ctx func s3 s4 _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `alloca_room (ctx with ctx_functions := [obs]) obs prepared` mp_tac >>
     qpat_assum `fn_has_code (start_relabel L ids s3) (start_swap s3 L ids s4) obs` mp_tac >>
     qpat_assum `fn_inst_ids_distinct obs` mp_tac >>
     qpat_assum `!i. MEM i (fn_insts obs) /\ _ ==> MEM i (fn_insts func)` mp_tac >>
     qpat_assum `LENGTH ids = LENGTH s3.cs_current_insts` mp_tac >>
     qpat_assum `s3.cs_blocks <> s4.cs_blocks` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `abi_encoder_window_pre ctx func s3 s4 _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[abi_encoder_window_pre_def]) >>
     `!op. eval_operand op (prepared with vs_current_bb := L) =
       eval_operand op prepared` by
       (Cases >> simp[eval_operand_def,lookup_var_def]) >>
     `frag_ids (start_relabel L ids s3) (start_swap s3 L ids s4) =
       frag_ids s3 s4` by
       (ONCE_REWRITE_TAC[GSYM start_swap_initial] >>
        REWRITE_TAC[abi_encode_start_swap_resource_fields]) >>
     REWRITE_TAC[abi_encoder_window_pre_def] >> rpt conj_tac >>
     simp[abi_encode_start_relabel_resources,
       abi_encode_alloca_resources_current_bb,start_relabel_def]
     >~ [`not_fresh_at s3 _ (* sg *)`]
     >- (rpt strip_tac >>
         qpat_x_assum `!x. src.buf_operand = Var x \/ _ ==> _` irule >> simp[]) >>
     rpt strip_tac >>
     `MEM inst (fn_insts func)` by
       (qpat_x_assum `!i. MEM i (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
     simp[]) >>
  `cs_extends s3 s4` by metis_tac[cs_extends_abi_encode] >>
  qpat_assum `Abbrev (encoded_post = _)` mp_tac >>
  qpat_assum `abi_encoder_window_pre ctx func s3 s4 _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `s3.cs_blocks <> s4.cs_blocks` mp_tac >>
  qpat_assum `cs_extends s3 s4` mp_tac >>
  qpat_assum `fn_inst_ids_distinct func` mp_tac >>
  qpat_assum `fn_inst_ids_distinct obs` mp_tac >>
  qpat_assum `!i. MEM i (fn_insts obs) /\ _ ==> MEM i (fn_insts func)` mp_tac >>
  qpat_assum `!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE` mp_tac >>
  qpat_assum `abi_encoder_window_pre (ctx with ctx_functions := [obs]) obs _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `compile_abi_encode_to_buf _ _ _ (start_relabel L ids s3) = _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  drule_all compile_abi_encode_to_buf_framed_run >>
  disch_then (qx_choose_then `observed` strip_assume_tac) >>
  `frag_ids (start_relabel L ids s3) (start_swap s3 L ids s4) =
    frag_ids s3 s4` by
    (ONCE_REWRITE_TAC[GSYM start_swap_initial] >>
     REWRITE_TAC[abi_encode_start_swap_resource_fields]) >>
  `!f. pending_alloca_size f (prepared with vs_current_bb := L) =
    pending_alloca_size f prepared` by simp[pending_alloca_size_def] >>
  qpat_assum `window_strong_result _ obs _ _ _ _ _ _ _ observed`
    (strip_assume_tac o REWRITE_RULE[window_strong_result_def]) >>
  qpat_assum `abi_encoder_window_result _ obs _ _ _ _ _ _ _ observed`
    (strip_assume_tac o REWRITE_RULE[abi_encoder_window_result_def]) >>
  `abi_encoder_registered_effect (window_alloca_sites obs (frag_ids s3 s4))
    [(db,LENGTH (enc enc_ty enc_val))] prepared observed` by
    (qpat_assum `abi_encoder_registered_effect (window_alloca_sites obs _) _ _ observed` mp_tac >>
     qpat_assum `frag_ids (start_relabel L ids s3) _ = frag_ids s3 s4` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[abi_encoder_registered_effect_def] >>
     rpt (disch_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `abi_decode_sim ctx obs (prepared with vs_current_bb := L) observed` by
    (irule abi_encode_completed_sim_context >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      ~MEM inst (fn_insts obs) ==>
    inst.inst_id NOTIN window_alloca_sites obs (frag_ids s3 s4)` by
    (rpt strip_tac >>
     qpat_x_assum `inst.inst_id IN window_alloca_sites obs _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [window_alloca_sites_def]) >>
     rename1 `MEM other (fn_insts obs)` >>
     `MEM other (fn_insts func)` by
       (qpat_x_assum `!i. MEM i (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
     `other = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
  `abi_encode_exec_frame func prepared observed` by
    (qpat_assum `!f. pending_alloca_size f (prepared with vs_current_bb := L) = _`
       (fn pending => qpat_assum `abi_encode_exec_frame obs _ _`
         (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_exec_frame_def,pending])) >>
     simp[abi_encode_exec_frame_def] >>
     mp_tac (Q.INST [`func` |-> `func`, `obs` |-> `obs`,
       `s` |-> `prepared`, `t` |-> `observed`] abi_encode_charge_difference_lift) >>
     impl_tac
     >- (simp[] >> rpt conj_tac >> rpt strip_tac >>
         rename1 `MEM inst (fn_insts func)` >>
         `inst.inst_id NOTIN window_alloca_sites obs (frag_ids s3 s4)` by metis_tac[] >>
         qpat_assum `abi_encoder_registered_effect (window_alloca_sites obs (frag_ids s3 s4))
           _ prepared observed`
           (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[abi_encoder_registered_effect_def]) >>
         disch_then (qspec_then `inst.inst_id` mp_tac) >> simp[]) >> simp[]) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
    [(db,LENGTH (enc enc_ty enc_val))] prepared observed` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites obs (frag_ids s3 s4)`,
       `[(db,LENGTH (enc enc_ty enc_val))]`] >>
     simp[] >>
     simp[SUBSET_DEF,window_alloca_sites_def] >> rpt strip_tac >>
     qexists_tac `inst` >> simp[] >>
     qpat_x_assum `!i. MEM i (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `s3`, `sb` |-> `s4`, `L` |-> `L`, `ids` |-> `ids`]
    abi_encode_start_swap_control) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `observed` >>
  simp[Abbr `encoded_post`] >> rpt conj_tac
  >~ [`window_alloca_growth _ _ (* g *)`]
  >- (qpat_assum `window_alloca_growth _ observed` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[window_alloca_growth_def] >>
      rpt (disch_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >~ [`FLOOKUP observed.vs_allocas _.inst_id = SOME (_,_) (* sg *)`]
  >- (rpt strip_tac >>
      Cases_on `inst.inst_id IN window_alloca_sites obs (frag_ids s3 s4)`
      >- (qpat_assum `!i b sz. i IN window_alloca_sites obs _ /\ _ ==> _`
            (qspecl_then [`inst.inst_id`,`b`,`sz`] mp_tac) >> simp[] >>
          rpt (disch_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
      `FLOOKUP observed.vs_allocas inst.inst_id =
        FLOOKUP prepared.vs_allocas inst.inst_id` by
        (qpat_assum `abi_encoder_registered_effect (window_alloca_sites obs (frag_ids s3 s4))
           _ prepared observed`
           (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[abi_encoder_registered_effect_def]) >>
         disch_then (qspec_then `inst.inst_id` mp_tac) >> simp[]) >>
      `FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
      qpat_assum `abi_encoder_window_pre ctx func s3 s4 _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[abi_encoder_window_pre_def]) >>
      qpat_x_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
        (qspecl_then [`inst`,`b`,`sz`] mp_tac) >> simp[] >>
      rpt (disch_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >~ [`lookup_var _ observed = SOME _ (* sg *)`]
  >- (qpat_assum `!x w. not_fresh_at (start_relabel L ids s3) x /\ _ ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[abi_encode_start_relabel_resources,lookup_var_def]) >>
  first_assum ACCEPT_TAC
QED

Resume log_declared_suffix_path[encode_frame]:
  `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==>
    FLOOKUP encoded.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  qpat_assum `window_alloca_growth prepared encoded`
    (strip_assume_tac o REWRITE_RULE[window_alloca_growth_def]) >>
  `!i q k. FLOOKUP encoded.vs_allocas i = SOME(q,k) /\
    FLOOKUP prepared.vs_allocas i = NONE ==> prepared.vs_alloca_next <= q` by
    (qpat_assum `window_alloca_growth prepared encoded` mp_tac >>
     rpt (pop_assum kall_tac) >> REWRITE_TAC[window_alloca_growth_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv s3` by
    (qpat_assum `local_ptrs_reserved cenv s2` mp_tac >>
     qpat_assum `s3.cs_next_var = s2.cs_next_var + 1` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule (Q.SPECL [`cenv`,`s2`,`s3`] local_ptrs_reserved_next_var) >>
     simp[] >> qexists_tac `s2` >> simp[]) >>
  `!name entry local_ptr_name sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var local_ptr_name) sz) ==>
    lookup_var local_ptr_name encoded = lookup_var local_ptr_name prepared` by
    (rpt strip_tac >>
     `not_fresh_at s3 local_ptr_name` by
       (qpat_assum `local_ptrs_reserved cenv s3` mp_tac >>
        qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_ptr_name) sz)` mp_tac >>
        rpt (pop_assum kall_tac) >> REWRITE_TAC[local_ptrs_reserved_def] >> metis_tac[]) >>
     `?w. lookup_var local_ptr_name prepared = SOME w` by
       (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
        qpat_assum `lookup_scopes name es.scopes = SOME entry` mp_tac >>
        qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_ptr_name) sz)` mp_tac >>
        rpt (pop_assum kall_tac) >>
        REWRITE_TAC[stmt_state_rel_def,state_rel_def,local_ptrs_rel_def] >> metis_tac[]) >>
     rename1 `lookup_var local_ptr_name prepared = SOME local_word` >>
     qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
       (qspecl_then [`local_ptr_name`,`local_word`] mp_tac) >>
     qpat_assum `lookup_var local_ptr_name prepared = SOME local_word` mp_tac >>
     qpat_assum `not_fresh_at s3 local_ptr_name` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `!name entry local_ptr_name sz inst.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var local_ptr_name) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [local_ptr_name] ==>
    inst.inst_id NOTIN window_alloca_sites func (frag_ids s3 s4)` by
    (rpt strip_tac >>
     qpat_x_assum `inst.inst_id IN window_alloca_sites func _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [window_alloca_sites_def]) >>
     rename1 `MEM other (fn_insts func)` >>
     `other = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
     qpat_x_assum `other = inst` SUBST_ALL_TAC >>
     `?q. inst.inst_outputs = [q] /\ ~not_fresh_at s3 q` by
       metis_tac[encoder_function_alloca_shape] >>
     rename1 `~not_fresh_at s3 fresh_name` >>
     qpat_assum `local_ptrs_reserved cenv s3` mp_tac >>
     qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_ptr_name) sz)` mp_tac >>
     qpat_assum `inst.inst_outputs = [local_ptr_name]` mp_tac >>
     qpat_assum `inst.inst_outputs = [fresh_name]` mp_tac >>
     qpat_assum `~not_fresh_at s3 fresh_name` mp_tac >>
     rpt (pop_assum kall_tac) >>
     REWRITE_TAC[local_ptrs_reserved_def] >> metis_tac[listTheory.CONS_11]) >>
  `FLOOKUP encoded.vs_allocas s2.cs_next_id = SOME(db,outcap)` by
    (qpat_assum `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==> _`
       (qspecl_then [`s2.cs_next_id`,`(db,outcap)`] mp_tac) >>
     qpat_assum `Abbrev (prepared = _)` mp_tac >>
     qpat_assum `FLOOKUP out_raw.vs_allocas s2.cs_next_id = SOME (db,outcap)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def]) >>
  `FLOOKUP prepared.vs_allocas s2.cs_next_id = SOME(db,outcap)` by
    (qpat_assum `Abbrev (prepared = _)` mp_tac >>
     qpat_assum `FLOOKUP out_raw.vs_allocas s2.cs_next_id = SOME (db,outcap)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def]) >>
  suspend "encoder_local_frame"
QED

Resume log_declared_suffix_path[encoder_local_frame]:
  `!name b n. local_region cenv es.scopes prepared name b n ==>
    mem_bytes_at b n encoded.vs_memory = mem_bytes_at b n prepared.vs_memory` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `fn_inst_ids_distinct func` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s2` mp_tac >>
     qpat_assum `compile_alloc_buffer outcap s2 = (dst,s3)` mp_tac >>
     qpat_assum `fn_has_code s2 s3 func` mp_tac >>
     qpat_assum `FLOOKUP prepared.vs_allocas s2.cs_next_id = SOME (db,outcap)` mp_tac >>
     qpat_assum `abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
       _ prepared encoded` mp_tac >>
     qpat_assum `LENGTH (enc enc_ty enc_val) <= abi_size_bound _ _` mp_tac >>
     qpat_assum `Abbrev (outcap = _)` mp_tac >>
     qpat_assum `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==> _` mp_tac >>
     qpat_assum `!i q k. FLOOKUP encoded.vs_allocas i = SOME (q,k) /\ _ ==> _` mp_tac >>
     qpat_assum `!name entry local_ptr_name sz inst. lookup_scopes name es.scopes = SOME entry /\ _ ==> _` mp_tac >>
     qpat_assum `alloca_inv encoded` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `venomMemDefs$regions_disjoint (db,outcap) (b,n)` by
       metis_tac[log_buffer_clear_of_locals,venomMemDefsTheory.regions_disjoint_def] >>
     irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`window_alloca_sites func (frag_ids s3 s4)`,
       `[(db,LENGTH (enc enc_ty enc_val))]`] >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> rpt conj_tac
     >~ [`db + LENGTH (enc enc_ty enc_val) <= b (* sg *)`]
     >- (Cases_on `32 < abi_size_bound cenv.ce_struct_fields (TupleT tys)` >>
         fs[Abbr `outcap`,arithmeticTheory.MAX_DEF,
           venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     qpat_assum `local_region cenv es.scopes prepared name b n`
       (strip_assume_tac o REWRITE_RULE [local_region_def]) >> gvs[] >>
     rename1 `FLOOKUP cenv.ce_vars name = SOME(PtrVar(Var local_ptr_name) n)` >>
     rename1 `lookup_scopes name es.scopes = SOME entry` >>
     rename1 `lookup_var local_ptr_name prepared = SOME w` >>
     mp_tac (Q.SPECL [`func`,`cenv`,`es.scopes`,`prepared`,`encoded`,
       `window_alloca_sites func (frag_ids s3 s4)`,`name`,`entry`,`local_ptr_name`,`n`,`w`]
       abi_encode_local_ptr_separation) >>
     impl_tac
     >- (fs[stmt_state_rel_def,state_rel_def] >> rpt conj_tac >>
         FIRST [first_assum ACCEPT_TAC,
           qx_gen_tac `alloc_inst` >> strip_tac >>
           qpat_x_assum `!name entry local_ptr_name sz inst. _`
             (qspecl_then [`name`,`entry`,`local_ptr_name`,`n`,`alloc_inst`] mp_tac) >> simp[]]) >>
     qpat_assum `_ IN window_alloca_sites func (frag_ids s3 s4)` mp_tac >>
     qpat_assum `FLOOKUP encoded.vs_allocas _ = SOME (_,_)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  suspend "encoder_immutable_frame"
QED

Resume log_declared_suffix_path[encoder_immutable_frame]:
  `cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME(ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME(tv,v) ==>
    mem_bytes_at off (type_memory_size tv) encoded.vs_memory =
    mem_bytes_at off (type_memory_size tv) prepared.vs_memory` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `compile_alloc_buffer outcap s2 = (dst,s3)` mp_tac >>
     qpat_assum `fn_has_code s2 s3 func` mp_tac >>
     qpat_assum `FLOOKUP prepared.vs_allocas s2.cs_next_id = SOME (db,outcap)` mp_tac >>
     qpat_assum `abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
       _ prepared encoded` mp_tac >>
     qpat_assum `LENGTH (enc enc_ty enc_val) <= abi_size_bound _ _` mp_tac >>
     qpat_assum `Abbrev (outcap = _)` mp_tac >>
     qpat_assum `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==> _` mp_tac >>
     qpat_assum `!i q k. FLOOKUP encoded.vs_allocas i = SOME (q,k) /\ _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `venomMemDefs$regions_disjoint (off,type_memory_size tv) (db,outcap)` by
       metis_tac[log_buffer_clear_of_immutable,venomMemDefsTheory.regions_disjoint_def] >>
     irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`window_alloca_sites func (frag_ids s3 s4)`,
       `[(db,LENGTH (enc enc_ty enc_val))]`] >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> rpt conj_tac
     >~ [`db + LENGTH (enc enc_ty enc_val) <= off (* sg *)`]
     >- (Cases_on `32 < abi_size_bound cenv.ce_struct_fields (TupleT tys)` >>
         fs[Abbr `outcap`,arithmeticTheory.MAX_DEF,
           venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     mp_tac (Q.INST [`func` |-> `func`, `cenv` |-> `cenv`, `cx` |-> `cx`,
       `vs` |-> `es`, `initial` |-> `prepared`, `actual` |-> `encoded`,
       `ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
       `name` |-> `name`, `off` |-> `off`, `tv` |-> `tv`, `v` |-> `v`]
       abi_encode_immutable_region_separation) >>
     impl_tac
     >- (qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
           (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           simp[window_alloca_sites_def] >> metis_tac[]]) >>
     qpat_assum `_ IN window_alloca_sites func (frag_ids s3 s4)` mp_tac >>
     qpat_assum `FLOOKUP encoded.vs_allocas _ = SOME (_,_)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `state_rel func cenv cx es encoded` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `abi_encode_exec_frame func prepared encoded` mp_tac >>
     qpat_assum `abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
       _ prepared encoded` mp_tac >>
     qpat_assum `!name entry local_ptr_name sz. lookup_scopes name es.scopes = SOME entry /\ _ ==>
       lookup_var local_ptr_name encoded = lookup_var local_ptr_name prepared` mp_tac >>
     qpat_assum `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==> _` mp_tac >>
     qpat_assum `!i q k. FLOOKUP encoded.vs_allocas i = SOME (q,k) /\ _ ==> _` mp_tac >>
     qpat_assum `prepared.vs_alloca_next <= encoded.vs_alloca_next` mp_tac >>
     qpat_assum `!name b n. local_region cenv es.scopes prepared name b n ==>
       mem_bytes_at b n encoded.vs_memory = _` mp_tac >>
     qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _ ==>
       mem_bytes_at off (type_memory_size tv) encoded.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     mp_tac (Q.INST [`func` |-> `func`, `observer` |-> `func`, `cenv` |-> `cenv`,
       `cx` |-> `cx`, `vs` |-> `es`, `initial` |-> `prepared`, `prepared` |-> `prepared`,
       `actual` |-> `encoded`, `ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
       `outs` |-> `[(db,LENGTH (enc enc_ty enc_val))]`] abi_encode_caller_state_rel) >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `alloca_room ctx func encoded /\ fmp_room ctx func encoded` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `abi_encode_exec_frame func prepared encoded` mp_tac >>
     qpat_assum `fn_inst_ids_distinct func` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `observer` |-> `func`,
       `initial` |-> `prepared`, `actual` |-> `encoded`] abi_encode_caller_resource_room) >>
     impl_tac >- (simp[] >> rpt conj_tac >> metis_tac[]) >> simp[]) >>
  `immutable_alloca_sep func cenv cx es encoded` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `prepared.vs_alloca_next <= encoded.vs_alloca_next` mp_tac >>
     qpat_assum `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==> _` mp_tac >>
     qpat_assum `!i q k. FLOOKUP encoded.vs_allocas i = SOME (q,k) /\ _ ==> _` mp_tac >>
     qpat_assum `!name entry local_ptr_name sz. lookup_scopes name es.scopes = SOME entry /\ _ ==>
       lookup_var local_ptr_name encoded = lookup_var local_ptr_name prepared` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     mp_tac (Q.INST [`func` |-> `func`, `cenv` |-> `cenv`, `cx` |-> `cx`,
       `vs` |-> `es`, `initial` |-> `prepared`, `actual` |-> `encoded`]
       abi_encode_caller_immutable_separation) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `immutable_base_zero cenv encoded` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `encoded.vs_labels = prepared.vs_labels` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s3` mp_tac >>
     qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     qpat_assum `local_ptrs_reserved cenv s3`
       (strip_assume_tac o REWRITE_RULE[local_ptrs_reserved_def]) >>
     mp_tac (Q.INST [`cenv` |-> `cenv`, `initial` |-> `prepared`, `actual` |-> `encoded`]
       abi_encode_caller_immutable_base) >>
     impl_tac
     >- (simp[] >> rpt gen_tac >> strip_tac >>
         `not_fresh_at s3 x` by metis_tac[] >>
         qpat_x_assum `!x w. not_fresh_at s3 x /\ _ ==> _`
           (qspecl_then [`x`,`v`] mp_tac) >> simp[]) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es encoded` by
    (qpat_assum `state_rel func cenv cx es encoded` mp_tac >>
     qpat_assum `alloca_inv encoded` mp_tac >>
     qpat_assum `alloca_room ctx func encoded` mp_tac >>
     qpat_assum `fmp_room ctx func encoded` mp_tac >>
     qpat_assum `immutable_alloca_sep func cenv cx es encoded` mp_tac >>
     qpat_assum `immutable_base_zero cenv encoded` mp_tac >>
     qpat_assum `stmt_state_rel ctx func cenv cx es prepared` mp_tac >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ s3 = (len,s4)` mp_tac >>
     qpat_assum `fn_has_code s3 s4 func` mp_tac >>
     qpat_assum `fn_inst_ids_distinct func` mp_tac >>
     qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> sz = 32` mp_tac >>
     qpat_assum `abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4))
       _ prepared encoded` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     qpat_assum `stmt_state_rel ctx func cenv cx es prepared`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     REWRITE_TAC[stmt_state_rel_def] >> rpt conj_tac
     >~ [`_.inst_operands = [Lit _] (* sg *)`]
     >- (rpt strip_tac >>
         Cases_on `inst.inst_id IN frag_ids s3 s4`
         >- (`inst.inst_operands = [Lit 32w]` by
               metis_tac[encoder_function_alloca_shape] >> gvs[] >>
             simp_tac (srw_ss()) [dimword_def] >> metis_tac[]) >>
         `inst.inst_id NOTIN window_alloca_sites func (frag_ids s3 s4)` by
           simp[window_alloca_sites_def] >>
         `FLOOKUP encoded.vs_allocas inst.inst_id =
           FLOOKUP prepared.vs_allocas inst.inst_id` by
           (qpat_assum `abi_encoder_registered_effect (window_alloca_sites func _) _ prepared encoded`
              (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[abi_encoder_registered_effect_def]) >>
            disch_then (qspec_then `inst.inst_id` mp_tac) >> simp[]) >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  suspend "emit_encoded"
QED

Resume log_declared_suffix_path[emit_encoded]:
  `!x w. not_fresh_at st x /\ lookup_var x u = SOME w ==>
    lookup_var x encoded = SOME w` by
    (qpat_assum `!x. not_fresh_at st x ==> lookup_var x a = _` mp_tac >>
     qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live s2.cs_next_var op ==> eval_operand op out_raw = _` mp_tac >>
     qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _` mp_tac >>
     qpat_assum `Abbrev (ut = _)` mp_tac >>
     qpat_assum `Abbrev (a1 = _)` mp_tac >>
     qpat_assum `Abbrev (prepared = _)` mp_tac >>
     qpat_assum `s1.cs_next_var = st.cs_next_var + 1` mp_tac >>
     qpat_assum `ci_mono s1 s2` mp_tac >>
     qpat_assum `s3.cs_next_var = s2.cs_next_var + 1` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x /\ not_fresh_at s3 x` by
       (qpat_assum `not_fresh_at st x` mp_tac >>
        qpat_assum `s1.cs_next_var = st.cs_next_var + 1` mp_tac >>
        qpat_assum `ci_mono s1 s2` mp_tac >>
        qpat_assum `s3.cs_next_var = s2.cs_next_var + 1` mp_tac >>
        rpt (pop_assum kall_tac) >> REWRITE_TAC[ci_mono_def] >>
        rpt (disch_then strip_assume_tac) >>
        `st.cs_next_var <= s1.cs_next_var /\ st.cs_next_var <= s2.cs_next_var /\
         st.cs_next_var <= s3.cs_next_var` by decide_tac >> metis_tac[not_fresh_at_mono]) >>
     `lookup_var x ut = SOME w` by fs[Abbr `ut`,lookup_var_def] >>
     `lookup_var x a1 = SOME w` by
       (fs[Abbr `a1`,lookup_var_def] >> metis_tac[]) >>
     `lookup_var x packed = SOME w` by metis_tac[] >>
     `lookup_var x prepared = SOME w` by
       (qpat_assum `!op. abi_decoder_operand_live s2.cs_next_var op ==> _`
          (qspec_then `Var x` mp_tac) >>
        qpat_assum `lookup_var x packed = SOME w` mp_tac >>
        qpat_assum `not_fresh_at s2 x` mp_tac >>
        qpat_assum `Abbrev (prepared = _)` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[markerTheory.Abbrev_def,eval_operand_def,lookup_var_def,
          abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
     metis_tac[]) >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
    lookup_var x encoded = SOME w` by
    (qpat_assum `!x w. not_fresh_at st x /\ lookup_var x u = SOME w ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x u = _` mp_tac >>
     qpat_assum `sm.cs_next_var <= st.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  `LIST_REL (\op w. eval_operand op encoded = SOME w) topic_ops topics` by
    (qpat_assum `LIST_REL (\op w. eval_operand op u = SOME w) topic_ops topics` mp_tac >>
     qpat_assum `EVERY (\op. (!z. op = Var z ==> not_fresh_at st z) /\ _) topic_ops` mp_tac >>
     qpat_assum `!x w. not_fresh_at st x /\ lookup_var x u = SOME w ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     fs[LIST_REL_EL_EQN,EVERY_EL] >> rpt strip_tac >>
     `eval_operand (EL n topic_ops) u = SOME (EL n topics)` by metis_tac[] >>
     `(!x. EL n topic_ops = Var x ==> not_fresh_at st x) /\
      (!lab. EL n topic_ops <> Label lab)` by metis_tac[] >>
     Cases_on `EL n topic_ops` >> fs[eval_operand_def] >> metis_tac[]) >>
  `eval_operands (Lit(n2w h)::topic_ops) encoded = SOME(n2w h::topics)` by
    (qpat_assum `LIST_REL (\op w. eval_operand op encoded = SOME w) topic_ops topics`
       (mp_tac o MATCH_MP log_operands_values) >>
     rpt (pop_assum kall_tac) >> simp[eval_operands_def,eval_operand_def]) >>
  `eval_operand dst.buf_operand encoded = SOME(n2w db)` by
    (qpat_assum `eval_operand dst.buf_operand out_raw = SOME(n2w db)` mp_tac >>
     qpat_assum `dst.buf_operand = Var _` mp_tac >>
     qpat_assum `Abbrev (prepared = _)` mp_tac >>
     qpat_assum `!x. src.buf_operand = Var x \/ dst.buf_operand = Var x ==> _` mp_tac >>
     qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     Cases_on `dst.buf_operand` >>
     fs[eval_operand_def,lookup_var_def,Abbr `prepared`] >> metis_tac[]) >>
  `LENGTH (Lit(n2w h)::topic_ops) < dimword(:256)` by
    (qpat_assum `LENGTH flags = LENGTH ops` mp_tac >>
     qpat_assum `LENGTH (FILTER I flags) <= 3` mp_tac >>
     qpat_assum `compile_log_topic_ops (FST (split_log_ops ops flags)) sm = (topic_ops,st)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     drule_all log_emitted_topic_count_exact >> simp[dimword_def]) >>
  mp_tac (Q.INST [`sa` |-> `s4`, `sb` |-> `sb`,
    `ptr_op` |-> `dst.buf_operand`, `len_op` |-> `len`,
    `topic_ops` |-> `Lit(n2w h)::topic_ops`, `s` |-> `encoded`,
    `topics` |-> `n2w h::topics`,
    `off` |-> `n2w db`, `sz` |-> `n2w(LENGTH(enc enc_ty enc_val))`]
    compile_log_emit_run) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `logged` strip_assume_tac) >>
  suspend "encoded_suffix_frame"
QED

Resume log_declared_suffix_path[encoded_suffix_frame]:
  `abi_encoder_registered_effect
    (s2.cs_next_id INSERT window_alloca_sites func (frag_ids s3 s4)) []
    prepared encoded` by
    (qpat_assum `abi_encoder_registered_effect (window_alloca_sites func (frag_ids s3 s4)) _ prepared encoded` mp_tac >>
     qpat_assum `FLOOKUP encoded.vs_allocas s2.cs_next_id = SOME (db,outcap)` mp_tac >>
     qpat_assum `LENGTH (enc enc_ty enc_val) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)` mp_tac >>
     qpat_assum `Abbrev (outcap = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     MATCH_MP_TAC (Q.INST
       [`ids` |-> `s2.cs_next_id INSERT window_alloca_sites func (frag_ids s3 s4)`,
        `outs` |-> `[(db,LENGTH(enc enc_ty enc_val))]`,
        `s` |-> `prepared`, `t` |-> `encoded`]
       abi_encode_registered_effect_absorb_outputs) >> conj_tac
     >- (MATCH_MP_TAC (Q.INST
           [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
            `outs` |-> `[(db,LENGTH(enc enc_ty enc_val))]`,
            `larger` |-> `s2.cs_next_id INSERT window_alloca_sites func (frag_ids s3 s4)`,
            `more` |-> `[(db,LENGTH(enc enc_ty enc_val))]`,
            `s` |-> `prepared`, `t` |-> `encoded`]
           abi_encoder_registered_effect_enlarge) >> simp[SUBSET_DEF]) >>
     simp[] >> qexistsl_tac [`s2.cs_next_id`,`db`,`outcap`] >>
     simp[] >> fs[Abbr `outcap`]) >>
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
    FLOOKUP a1.vs_allocas aid = SOME row /\
    FLOOKUP prepared.vs_allocas aid = SOME row /\
    FLOOKUP encoded.vs_allocas aid = SOME row` by
    (qpat_assum `Abbrev (a1 = _)` mp_tac >>
     qpat_assum `Abbrev (ut = _)` mp_tac >>
     qpat_assum `Abbrev (prepared = _)` mp_tac >>
     qpat_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `packed.vs_allocas = a1.vs_allocas` mp_tac >>
     qpat_assum `!aid row. FLOOKUP ut.vs_allocas aid = SOME row ==> FLOOKUP a.vs_allocas aid = SOME row` mp_tac >>
     qpat_assum `abi_builtin_allocation_frame s2.cs_next_var s2.cs_next_id outcap packed out_raw` mp_tac >>
     qpat_assum `!i r. FLOOKUP prepared.vs_allocas i = SOME r ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     rpt strip_tac >>
     `FLOOKUP a1.vs_allocas aid = SOME row` by
       (fs[Abbr `a1`,Abbr `ut`] >> metis_tac[]) >>
     `FLOOKUP packed.vs_allocas aid = SOME row` by simp[] >>
     `FLOOKUP prepared.vs_allocas aid = SOME row` by
       (qpat_assum `abi_builtin_allocation_frame _ _ _ packed out_raw` mp_tac >>
        qpat_assum `FLOOKUP packed.vs_allocas aid = SOME row` mp_tac >>
        qpat_assum `Abbrev (prepared = _)` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[markerTheory.Abbrev_def,abi_builtin_allocation_frame_def,
          abi_builtin_allocate_state_def] >>
        Cases_on `FLOOKUP packed.vs_allocas s2.cs_next_id = NONE` >>
        fs[FLOOKUP_UPDATE] >> rpt strip_tac >>
        Cases_on `aid = s2.cs_next_id` >> fs[]) >>
     metis_tac[abi_encoder_registered_effect_allocated]) >>
  `!aid lo n. aid < sm.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME(lo,n) ==>
    mem_bytes_at lo n encoded.vs_memory = mem_bytes_at lo n s.vs_memory` by
    suspend "encoded_old_bytes" >>
  `alloca_frame cenv es sm s cenv es logged` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es s` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sm` mp_tac >>
     qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> _` mp_tac >>
     qpat_assum `!aid lo n. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (lo,n) ==> _` mp_tac >>
     qpat_assum `logged with vs_logs := _ = encoded`
       (mp_tac o Q.AP_TERM `\z. (z.vs_vars,z.vs_memory)`) >>
     rpt (pop_assum kall_tac) >> simp[] >>
     rpt (disch_then strip_assume_tac) >>
     MATCH_MP_TAC (Q.INST
       [`ctx` |-> `ctx`, `func` |-> `func`, `cenv` |-> `cenv`,
        `cx` |-> `cx`, `es` |-> `es`, `ee` |-> `es`,
        `sm` |-> `sm`, `s` |-> `s`, `t` |-> `logged`]
       log_suffix_alloca_frame) >> simp[] >>
     rpt strip_tac
     >~ [`eval_operand op logged = SOME w (* g *)`]
     >- (Cases_on `op` >> fs[eval_operand_def,lookup_var_def] >> metis_tac[]) >>
     metis_tac[]) >>
  suspend "logged_path"
QED

Resume log_declared_suffix_path[encoded_old_bytes]:
  rpt strip_tac >>
  `aid <> st.cs_next_id /\ aid <> s2.cs_next_id /\
    aid NOTIN frag_ids s3 s4` by
    (qpat_assum `aid < sm.cs_next_id` mp_tac >>
     qpat_assum `sm.cs_next_id <= st.cs_next_id` mp_tac >>
     qpat_assum `st.cs_next_id < s2.cs_next_id` mp_tac >>
     qpat_assum `s2.cs_next_id < s3.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[frag_ids_def] >> decide_tac) >>
  `FLOOKUP a1.vs_allocas aid = SOME(lo,n) /\
   FLOOKUP prepared.vs_allocas aid = SOME(lo,n) /\
   FLOOKUP encoded.vs_allocas aid = SOME(lo,n)` by
    (qpat_assum `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> _` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas aid = SOME(lo,n)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (lo,n) (p,cap)` by
    (qpat_assum `stmt_state_rel ctx func cenv cx es a1`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[stmt_state_rel_def]) >>
     qpat_assum `FLOOKUP a1.vs_allocas aid = SOME(lo,n)` mp_tac >>
     qpat_assum `FLOOKUP a.vs_allocas st.cs_next_id = SOME(p,cap)` mp_tac >>
     qpat_assum `aid <> st.cs_next_id` mp_tac >>
     qpat_assum `Abbrev (a1 = _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[markerTheory.Abbrev_def,alloca_inv_def,allocas_non_overlapping_def,
       venomMemDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at lo n packed.vs_memory = mem_bytes_at lo n a1.vs_memory` by
    (qpat_assum `!off k. _ ==> mem_bytes_at off k packed.vs_memory = _` mp_tac >>
     qpat_assum `venomMemDefs$regions_disjoint (lo,n) (p,cap)` mp_tac >>
     qpat_assum `p+cap < dimword(:256)` mp_tac >>
     qpat_assum `Abbrev (cap = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     `p < dimword(:256)` by decide_tac >>
     Cases_on `n = 0` >- simp[mem_bytes_at_def] >>
     first_x_assum irule >>
     fs[venomMemDefsTheory.regions_disjoint_def,Abbr `cap`,w2n_n2w,arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `mem_bytes_at lo n encoded.vs_memory = mem_bytes_at lo n prepared.vs_memory` by
    (qpat_assum `abi_encoder_registered_effect (s2.cs_next_id INSERT _) [] prepared encoded` mp_tac >>
     qpat_assum `alloca_inv encoded` mp_tac >>
     qpat_assum `aid NOTIN frag_ids s3 s4` mp_tac >>
     qpat_assum `aid <> s2.cs_next_id` mp_tac >>
     qpat_assum `FLOOKUP encoded.vs_allocas aid = SOME(lo,n)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     MATCH_MP_TAC (Q.INST
       [`ids` |-> `s2.cs_next_id INSERT window_alloca_sites func (frag_ids s3 s4)`,
        `prepared` |-> `prepared`, `actual` |-> `encoded`,
        `aid` |-> `aid`, `b` |-> `lo`, `sz` |-> `n`, `off` |-> `lo`, `n` |-> `n`]
       abi_encode_registered_owned_interval) >> simp[window_alloca_sites_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ ut a`
    (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[abi_builtin_allocation_frame_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ packed out_raw`
    (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[abi_builtin_allocation_frame_def]) >>
  qpat_assum `u.vs_memory = s.vs_memory` mp_tac >>
  qpat_assum `mem_bytes_at lo n packed.vs_memory = mem_bytes_at lo n a1.vs_memory` mp_tac >>
  qpat_assum `mem_bytes_at lo n encoded.vs_memory = mem_bytes_at lo n prepared.vs_memory` mp_tac >>
  qpat_assum `Abbrev (prepared = _)` mp_tac >>
  qpat_assum `Abbrev (a1 = _)` mp_tac >>
  qpat_assum `Abbrev (ut = _)` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[markerTheory.Abbrev_def] >> metis_tac[]
QED

Resume log_declared_suffix_path[logged_path]:
  `~block_is_terminated sb` by metis_tac[logComposeFactsTheory.log_emit_not_terminated] >>
  `inst_extends s4 sb /\ s4.cs_current_bb = sb.cs_current_bb /\
    emitted_insts s4 sb = [mk_inst s4.cs_next_id LOG
      (Lit(n2w(LENGTH(Lit(n2w h)::topic_ops))) ::
        REVERSE (Lit(n2w h)::topic_ops) ++ [len;dst.buf_operand]) []]` by
    (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     strip_tac >> drule emitted_insts_emit_inst >>
     drule inst_extends_emit_inst >> simp[]) >>
  `?log_bb. lookup_block encoded.vs_current_bb func.fn_blocks = SOME log_bb /\
    isPREFIX (emitted_insts s4 sb)
      (DROP encoded.vs_inst_idx log_bb.bb_instructions) /\
    encoded.vs_inst_idx + LENGTH(emitted_insts s4 sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `fn_has_code s4 sb func` mp_tac >>
     qpat_assum `encoded.vs_current_bb = s4.cs_current_bb` mp_tac >>
     qpat_assum `encoded.vs_inst_idx = LENGTH s4.cs_current_insts` mp_tac >>
     qpat_assum `inst_extends s4 sb` mp_tac >>
     qpat_assum `s4.cs_current_bb = sb.cs_current_bb` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     qpat_assum `fn_has_code s4 sb func`
       (qx_choose_then `prefix_bb` strip_assume_tac o CONJUNCT2 o
        REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `prefix_bb` >>
     gvs[inst_extends_def,same_blocks_def,IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1,DROP_LENGTH_NIL,APPEND_ASSOC] >>
     REWRITE_TAC [GSYM LENGTH_APPEND] >> simp[DROP_LENGTH_NIL]) >>
  pop_assum strip_assume_tac >>
  `gas_path ctx func encoded 0
    (OK (logged with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_assum `~encoded.vs_halted` mp_tac >>
     qpat_assum `lookup_block encoded.vs_current_bb func.fn_blocks = SOME log_bb` mp_tac >>
     qpat_assum `isPREFIX (emitted_insts s4 sb) _` mp_tac >>
     qpat_assum `encoded.vs_inst_idx + LENGTH(emitted_insts s4 sb) = LENGTH sb.cs_current_insts` mp_tac >>
     qpat_assum `emitted_insts s4 sb = [_]` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts s4 sb) encoded = OK logged` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     qspecl_then [`emitted_insts s4 sb`,`encoded`,`logged`,`ctx`,`func`,`log_bb`]
       mp_tac tuple_run_inst_seq_gas_path >>
     simp[mk_inst_def,is_terminator_def]) >>
  `gas_path ctx func s 0 (OK a1)` by
    (qpat_assum `gas_path ctx func s 0 (OK ut)` mp_tac >>
     qpat_assum `gas_path ctx func ut 0 (OK _)` mp_tac >>
     qpat_assum `Abbrev (a1 = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     irule (SRULE[] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `ut` >> simp[Abbr `a1`]) >>
  `gas_path ctx func s 0 (OK packed)` by
    (qpat_assum `gas_path ctx func s 0 (OK a1)` mp_tac >>
     qpat_assum `gas_path ctx func a1 0 (OK packed)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     irule (SRULE[] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `a1` >> simp[]) >>
  `gas_path ctx func s 0 (OK prepared)` by
    (qpat_assum `gas_path ctx func s 0 (OK packed)` mp_tac >>
     qpat_assum `gas_path ctx func packed 0 (OK _)` mp_tac >>
     qpat_assum `Abbrev (prepared = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     irule (SRULE[] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `packed` >> simp[Abbr `prepared`]) >>
  `gas_path ctx func s 0 (OK encoded)` by
    (qpat_assum `gas_path ctx func s 0 (OK prepared)` mp_tac >>
     qpat_assum `gas_path ctx func prepared 0 (OK encoded)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     irule (SRULE[] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `prepared` >> simp[]) >>
  `gas_path ctx func s 0
    (OK (logged with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_assum `gas_path ctx func s 0 (OK encoded)` mp_tac >>
     qpat_assum `gas_path ctx func encoded 0 (OK (logged with vs_inst_idx := _))` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     irule (SRULE[] (Q.INST [`n` |-> `0`,`m` |-> `0`] gas_path_then)) >>
     qexists_tac `encoded` >> simp[]) >>
  `logged.vs_halted = encoded.vs_halted /\
   logged.vs_current_bb = encoded.vs_current_bb /\
   logged.vs_allocas = encoded.vs_allocas /\
   logged.vs_vars = encoded.vs_vars` by
    (qpat_x_assum `logged with vs_logs := _ = encoded`
      (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb,z.vs_allocas,z.vs_vars)`) >>
     simp[]) >>
  `LENGTH(enc enc_ty enc_val) < dimword(:256)` by
    (qpat_assum `LENGTH(enc enc_ty enc_val) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)` mp_tac >>
     qpat_assum `abi_size_bound cenv.ce_struct_fields (TupleT tys) < 2 ** 64` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[dimword_def] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx
    (es with logs := es.logs ++
      [<|logger := cx.txn.target;topics := n2w h::topics;
         data := enc (Tuple (vyper_to_abi_types (get_tenv cx) tys)) (ListV avs)|>]) logged` by
    (qpat_assum `stmt_state_rel ctx func cenv cx (es with logs := _) logged` mp_tac >>
     qpat_assum `mem_bytes_at db (LENGTH(enc enc_ty enc_val)) encoded.vs_memory = enc enc_ty enc_val` mp_tac >>
     qpat_assum `db+outcap < dimword(:256)` mp_tac >>
     qpat_assum `LENGTH(enc enc_ty enc_val) < dimword(:256)` mp_tac >>
     qpat_assum `enc enc_ty enc_val = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
     `db < dimword(:256)` by decide_tac >>
     fs[wordsTheory.w2w_id,w2n_n2w,arithmeticTheory.LESS_MOD,
       Once vyper_to_abi_type_def] >>
     qpat_assum `LENGTH(enc enc_ty enc_val) < dimword(:256)`
       (mp_tac o MATCH_MP arithmeticTheory.LESS_MOD) >>
     disch_then (fn mod_eq => RULE_ASSUM_TAC (REWRITE_RULE[mod_eq])) >>
     metis_tac[]) >>
  qpat_assum `Abbrev (tys = _)` mp_tac >>
  qpat_assum `Abbrev (flags = _)` mp_tac >>
  qpat_assum `Abbrev (dtys = _)` mp_tac >>
  qpat_assum `gas_path ctx func s 0 (OK (logged with vs_inst_idx := _))` mp_tac >>
  qpat_assum `stmt_state_rel ctx func cenv cx (es with logs := _) logged` mp_tac >>
  qpat_assum `~block_is_terminated sb` mp_tac >>
  qpat_assum `~encoded.vs_halted` mp_tac >>
  qpat_assum `logged.vs_halted = encoded.vs_halted` mp_tac >>
  qpat_assum `logged.vs_current_bb = encoded.vs_current_bb` mp_tac >>
  qpat_assum `encoded.vs_current_bb = s4.cs_current_bb` mp_tac >>
  qpat_assum `s4.cs_current_bb = sb.cs_current_bb` mp_tac >>
  qpat_assum `logged.vs_vars = encoded.vs_vars` mp_tac >>
  qpat_assum `logged.vs_allocas = encoded.vs_allocas` mp_tac >>
  qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> _` mp_tac >>
  qpat_assum `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> _` mp_tac >>
  qpat_assum `alloca_frame cenv es sm s cenv es logged` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt (disch_then strip_assume_tac) >>
  qexists_tac `logged with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_post_def,stmt_lands_def,stmt_state_rel_inst_idx,cenv_top_ext_refl,
    Abbr `tys`,Abbr `flags`,Abbr `dtys`,Excl "enc_def"] >>
  conj_tac
  >- (qpat_assum `stmt_state_rel ctx func cenv cx (es with logs := _) logged` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[contractABITheory.enc_def]) >>
  simp[alloca_frame_def,local_region_def,lookup_var_def] >>
  fs[alloca_frame_def,local_region_def,lookup_var_def] >> first_assum ACCEPT_TAC
QED

Finalise log_declared_suffix_path
