(* TOP-LEVEL: actual Log lowering with no non-indexed fields executes from
   saved arguments before hashing and agrees with the source event encoder.
   API: compile_saved_log_empty_path. *)
Theory abiLogTopicsEmpty
Ancestors
  vyperEventArgCompat
  eventLogTopicsPath abiLogTopicsReady abiLogSourceEncoding abiEmptyLogPath abiLogAllocationFrame
  typedLogArgs typedCopyStateFrame typedLogSplitComplete abiFieldOperands abiFlatRun abiStateFrame
  context stmtLowering compileEnv fragExec fragBlockPath vyperTypeContract vyperTypeSystem
  vyperEvent venomState list pair words

Theorem compile_saved_log_empty_path:
  !ctx func tenv cenv lctx ty event_id exprs cs cs' sig_hash arg_types flags eval_ops eval_cut
    raw_topics topic_ops topic_cut atvs vs ss dst byte_count.
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,arg_types,flags) /\
    compile_log_eval_all cenv exprs cs = (eval_ops,eval_cut) /\
    split_log_ops eval_ops flags = (raw_topics,[]) /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) /\
    compile_stmt cenv lctx ty (Log event_id exprs) cs = ((),cs') /\
    fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut cs' func /\
    LENGTH flags = LENGTH eval_ops /\ LIST_REL event_arg_compatible arg_types (MAP SND eval_ops) /\
    LIST_REL (\flag fty. flag ==> event_indexable_type fty) flags arg_types /\
    LIST_REL (\arg tv. evaluate_type tenv (SND arg) = SOME tv) eval_ops atvs /\
    log_args_rel eval_ops atvs vs ss /\ log_args_safe eval_ops atvs ss dst byte_count /\
    EVERY (\arg. abi_operand_before eval_cut.cs_next_var (FST arg)) eval_ops /\
    LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\
    ss.vs_current_bb = eval_cut.cs_current_bb /\ ss.vs_inst_idx = LENGTH eval_cut.cs_current_insts /\ ~ss.vs_halted /\
    ~ss.vs_call_ctx.cc_static ==>
    ?out topics.
      encode_vyper_event_metadata tenv (w2w ss.vs_call_ctx.cc_address) (sig_hash,arg_types,flags) vs =
        SOME <|logger := w2w ss.vs_call_ctx.cc_address; topics := n2w sig_hash::topics; data := []|> /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := n2w sig_hash::topics; data := []|>] /\ out.vs_memory = ss.vs_memory /\
      (!arg_op. abi_operand_before eval_cut.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs) /\
      copy_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  `compile_log_topic_ops (FST (split_log_ops eval_ops flags)) eval_cut = (topic_ops,topic_cut)` by asm_simp_tac bool_ss [FST] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `tenv`, `flags`, `eval_ops`, `vs`, `arg_types`, `atvs`,
    `eval_cut`, `topic_ops`, `topic_cut`, `ss`, `dst`, `byte_count`] compile_saved_log_topics_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `middle` (qx_choose_then `topics` strip_assume_tac)) >>
  mp_tac (Q.SPECL [`topic_cut.cs_next_var`, `topic_ops`, `middle`, `topics`, `sig_hash`] log_topic_header) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `~middle.vs_call_ctx.cc_static` by
    (qpat_assum `fragment_path ctx func ss middle`
       (mp_tac o MATCH_MP fragBlockPathTheory.fragment_path_call_ctx) >> fs[]) >>
  drule_all_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) compile_log_empty_data_path >>
  `log_non_indexed_types flags arg_types = []` by (drule_all split_log_data_compatible >> simp[]) >>
  mp_tac (Q.SPECL [`tenv`, `w2w ss.vs_call_ctx.cc_address`, `sig_hash`, `flags`, `arg_types`, `vs`, `topics`]
    empty_event_metadata_encoding) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ss`, `middle`] copy_state_frame_external) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ss`, `middle`] abi_state_frame_observables) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  `fragment_path ctx func ss out` by (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  `!arg_op. abi_operand_before topic_cut.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op middle` by
    asm_simp_tac bool_ss [] >>
  `!arg_op. abi_operand_before eval_cut.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (mp_tac (Q.SPECL [`eval_cut.cs_next_var`, `topic_cut.cs_next_var`, `ss`, `middle`, `out`] abi_operand_before_frame_trans) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `abi_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (mp_tac (Q.SPECL [`ss`, `middle`, `out`] abi_log_allocation_state_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `copy_state_frame middle (out with vs_logs := ss.vs_logs)` by
    (qpat_x_assum `copy_state_frame middle (out with vs_logs := middle.vs_logs)` mp_tac >>
     asm_simp_tac bool_ss []) >>
  `copy_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (irule copy_state_frame_trans >> qexists_tac `middle` >> simp[]) >>
  qexistsl_tac [`out`, `topics`] >> asm_simp_tac bool_ss []
QED
