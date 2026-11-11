(* TOP-LEVEL: execution of a topic from its typed operand representation.
   The bytestring footprint comes from the allocated region. Empty payloads
   also work when adding the header size wraps the unused data pointer. *)
Theory eventTopicValueProps
Ancestors
  valueEncodingDefs eventTopicExecProps eventTopicProps valueLoadProps valueEncoding valueEncodingProps compileEnv
  context exprLowering exprLoweringProps nameLoweringProps vyperTypeContract
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperValue vyperTyping vyperEvent
  vyperEventSoundness
  venomState venomExecSemantics byte words arithmetic vfmConstants
Libs wordsLib monadsyntax

Definition topic_value_rel_def:
  topic_value_rel tenv (arg_op,ty) v ss <=>
    event_indexable_type ty /\
    ?tv addr. evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
      eval_operand arg_op ss = SOME addr /\
      if is_bytestring_type ty then
        val_in_memory tv v (w2n addr) ss.vs_memory /\
        w2n addr + val_memory_size v <= dimword(:256)
      else is_word_type ty /\ addr = typed_val_to_w256 tv v
End

Theorem bytestring_type_not_word:
  !ty. is_bytestring_type ty ==> ~is_word_type ty
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >>
  gvs[is_bytestring_type_def, is_word_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, is_word_type_def] >>
  rename1 `is_bytestring_type (BaseT (BytesT bound))` >> Cases_on `bound` >>
  gvs[is_bytestring_type_def, is_word_type_def]
QED

Theorem indexable_non_bytestring_word:
  !tenv ty tv.
    event_indexable_type ty /\ evaluate_type tenv ty = SOME tv /\
    ~is_bytestring_type ty ==> is_word_type ty
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >>
  gvs[event_indexable_type_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `evaluate_type tenv (BaseT bt) = SOME tv` >> Cases_on `bt` >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `evaluate_type tenv (BaseT (BytesT bound)) = SOME tv` >>
  Cases_on `bound` >>
  gvs[is_word_type_def, is_bytestring_type_def, Once evaluate_type_def, AllCaseEqs()]
QED

Theorem lowered_value_rel_topic_value_rel:
  !tenv arg_op ty tv v ss.
    event_indexable_type ty /\ evaluate_type tenv ty = SOME tv /\
    lowered_value_rel ty tv v arg_op ss /\
    (!addr. is_bytestring_type ty /\ eval_operand arg_op ss = SOME addr ==>
       w2n addr + val_memory_size v <= dimword(:256)) ==>
    topic_value_rel tenv (arg_op,ty) v ss
Proof
  rpt gen_tac >> strip_tac >> fs[lowered_value_rel_def] >>
  rename1 `eval_operand arg_op ss = SOME addr` >>
  rewrite_tac[topic_value_rel_def] >> conj_tac >- simp[] >>
  qexistsl_tac [`tv`, `addr`] >> Cases_on `is_bytestring_type ty`
  >- (`~is_word_type ty` by (irule bytestring_type_not_word >> simp[]) >> gvs[] >>
      drule_all memory_value_rel_bytestring >> simp[]) >>
  `is_word_type ty` by (drule_all indexable_non_bytestring_word >> simp[]) >> gvs[]
QED

Theorem empty_bytestring_topic_correct:
  !arg_op cs op cs' ss addr.
    compile_encode_log_topic arg_op T cs = (op,cs') /\
    eval_operand arg_op ss = SOME addr /\ fresh_vars_wrt cs ss /\
    mload (w2n addr) ss = 0w ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out = SOME (word_of_bytes_be (Keccak_256_w64 [])) /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_bytestring_topic_correct >> strip_tac >>
  goal_assum drule >> simp[read_memory_def, word_of_bytes_be_def]
QED

Theorem word_size_zero:
  !n. word_size n = 0 <=> n = 0
Proof
  simp[word_size_def, DIV_EQ_0]
QED

Theorem bytestring_header_in_range:
  !addr payload_length.
    0 < payload_length /\
    w2n (addr:bytes32) + (32 + 32 * word_size payload_length) <= dimword(:256) ==>
    w2n addr + 32 < 2 ** 256
Proof
  rpt strip_tac >>
  `word_size payload_length <> 0` by simp[word_size_zero] >>
  `dimword(:256) = 2 ** 256` by EVAL_TAC >> decide_tac
QED

Theorem evaluate_bytestring_bound:
  (!tenv cap tv.
    evaluate_type tenv (BaseT (BytesT (Dynamic cap))) = SOME tv ==>
    cap < dimword(:256)) /\
  (!tenv cap tv.
    evaluate_type tenv (BaseT (StringT cap)) = SOME tv ==>
    cap < dimword(:256))
Proof
  rpt conj_tac >> rpt gen_tac >> simp[Once evaluate_type_def, AllCaseEqs()]
QED

Theorem compile_bytes_topic_value_correct:
  !tenv arg_op cap v cs op cs' ss.
    topic_value_rel tenv (arg_op,BaseT (BytesT (Dynamic cap))) v ss /\
    compile_encode_log_topic arg_op T cs = (op,cs') /\ fresh_vars_wrt cs ss ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out = encode_event_topic (BaseT (BytesT (Dynamic cap))) v /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  fs[topic_value_rel_def, is_bytestring_type_def] >>
  drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (BytesV bs) _ _` >>
  Cases_on `bs = []`
  >- (gvs[val_in_memory_def, mem_word_at_eq_mload] >>
      drule_all empty_bytestring_topic_correct >> strip_tac >>
      goal_assum drule >> simp[encode_event_topic_def, is_event_bytestring_type_def]) >>
  `0 < LENGTH bs` by (Cases_on `bs` >> gvs[]) >>
  `w2n addr + 32 < 2 ** 256` by
    (irule bytestring_header_in_range >> qexists_tac `LENGTH bs` >>
     fs[val_memory_size_def]) >>
  `LENGTH bs < 2 ** 256` by
    (drule (cj 1 evaluate_bytestring_bound) >> simp[] >>
     `dimword(:256) = 2 ** 256` by EVAL_TAC >> fs[]) >>
  drule_all compile_bytes_topic_correct >> simp[]
QED

Theorem compile_string_topic_value_correct:
  !tenv arg_op cap v cs op cs' ss.
    topic_value_rel tenv (arg_op,BaseT (StringT cap)) v ss /\
    compile_encode_log_topic arg_op T cs = (op,cs') /\ fresh_vars_wrt cs ss ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out = encode_event_topic (BaseT (StringT cap)) v /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  fs[topic_value_rel_def, is_bytestring_type_def] >>
  drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (StringV s) _ _` >>
  Cases_on `s = ""`
  >- (gvs[val_in_memory_def, mem_word_at_eq_mload] >>
      drule_all empty_bytestring_topic_correct >> strip_tac >>
      goal_assum drule >> simp[encode_event_topic_def, is_event_bytestring_type_def]) >>
  `0 < LENGTH s` by (Cases_on `s` >> gvs[]) >>
  `w2n addr + 32 < 2 ** 256` by
    (irule bytestring_header_in_range >> qexists_tac `LENGTH s` >>
     fs[val_memory_size_def]) >>
  `LENGTH s < 2 ** 256` by
    (drule (cj 2 evaluate_bytestring_bound) >> simp[] >>
     `dimword(:256) = 2 ** 256` by EVAL_TAC >> fs[]) >>
  drule_all compile_string_topic_correct >> simp[]
QED

Theorem compile_topic_value_correct:
  !tenv arg_op ty v cs op cs' ss.
    topic_value_rel tenv (arg_op,ty) v ss /\
    compile_encode_log_topic arg_op (is_bytestring_type ty) cs = (op,cs') /\
    fresh_vars_wrt cs ss ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out = encode_event_topic ty v /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type ty`
  >- (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
      rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def] >>
      TRY (rename1 `is_bytestring_type (BaseT (BytesT bound))` >>
        Cases_on `bound` >> gvs[is_bytestring_type_def]) >>
      FIRST [drule_all compile_bytes_topic_value_correct >> simp[],
             drule_all compile_string_topic_value_correct >> simp[]]) >>
  fs[topic_value_rel_def] >> gvs[] >>
  drule_all compile_word_topic_correct >> strip_tac >> gvs[] >>
  qexists_tac `ss` >> simp[run_inst_seq_def, emitted_insts_def, same_blocks_def]
QED

Theorem topic_value_rel_assignment_frame:
  !tenv arg_op ty v ss out.
    topic_value_rel tenv (arg_op,ty) v ss /\ out with vs_vars := ss.vs_vars = ss /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) ==>
    topic_value_rel tenv (arg_op,ty) v out
Proof
  rpt gen_tac >> strip_tac >>
  `out.vs_memory = ss.vs_memory` by
    (irule assignment_frame_memory >> simp[]) >>
  fs[topic_value_rel_def] >>
  rename1 `evaluate_type tenv ty = SOME value_ty` >>
  rename1 `eval_operand arg_op ss = SOME addr` >>
  qexists_tac `addr` >> simp[]
QED

Theorem topic_value_rel_encodes:
  !tenv arg_op ty v ss.
    topic_value_rel tenv (arg_op,ty) v ss ==>
    ?topic. encode_event_topic ty v = SOME topic
Proof
  rpt gen_tac >> strip_tac >> fs[topic_value_rel_def] >>
  drule_all typed_event_topic_total >> simp[]
QED

Theorem word_size_monotone:
  !n m. n <= m ==> word_size n <= word_size m
Proof
  simp[word_size_def] >> rpt strip_tac >>
  irule DIV_LE_MONOTONE >> simp[]
QED

Theorem bytestring_value_size_bound:
  !tenv ty tv v.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    val_memory_size v <= type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `evaluate_type tenv (BaseT bt) = SOME tv` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def] >>
  TRY (rename1 `evaluate_type tenv (BaseT (BytesT bound)) = SOME tv` >>
    Cases_on `bound` >> gvs[is_bytestring_type_def]) >>
  drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def, val_memory_size_def, type_memory_size_def] >>
  irule word_size_monotone >> simp[]
QED

Theorem local_ptrs_rel_bytestring_topic:
  !tenv func cenv scopes ss id entry p region_size ty.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes id scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
    evaluate_type tenv ty = SOME entry.type /\ is_bytestring_type ty /\
    value_has_type entry.type entry.value /\ ss.vs_alloca_next <= dimword(:256) ==>
    topic_value_rel tenv (Var p,ty) entry.value ss
Proof
  rpt gen_tac >> strip_tac >> drule_all local_ptrs_rel_value >> strip_tac >>
  rename1 `eval_operand (Var p) ss = SOME addr` >>
  `event_indexable_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, event_indexable_type_def]) >>
  `val_memory_size entry.value <= type_memory_size entry.type` by
    (drule_all bytestring_value_size_bound >> simp[]) >>
  drule_all memory_value_rel_bytestring >> DISCH_TAC >>
  rewrite_tac[topic_value_rel_def] >> conj_tac >- simp[] >>
  qexistsl_tac [`entry.type`, `addr`] >> fs[] >> decide_tac
QED

Theorem lower_value_name_ptrvar_topic_correct:
  !tenv func cenv scopes ty ann id entry p region_size ss cs op cs'.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes id scopes = SOME entry /\
    evaluate_type tenv ann = SOME entry.type /\
    value_has_type entry.type entry.value /\ event_indexable_type ann /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
    (is_bytestring_type ann ==> ss.vs_alloca_next <= dimword(:256)) /\
    fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      topic_value_rel tenv (op,ann) entry.value out /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type ann`
  >- (`~is_word_type ann` by (irule bytestring_type_not_word >> simp[]) >>
      mp_tac (Q.SPECL [`cenv`, `id`, `Var p`, `region_size`, `ty`, `ann`, `cs`]
        lower_value_name_ptrvar) >> simp[] >> strip_tac >> gvs[] >>
      `topic_value_rel tenv (Var p,ann) entry.value ss` by
        (mp_tac (Q.SPECL [`tenv`, `func`, `cenv`, `scopes`, `ss`, `id`,
           `entry`, `p`, `region_size`, `ann`] local_ptrs_rel_bytestring_topic) >>
         simp[]) >>
      qexists_tac `ss` >> simp[emitted_insts_def, run_inst_seq_def, same_blocks_def]) >>
  drule_all lower_value_name_ptrvar_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
  qexists_tac `final` >> simp[] >>
  irule lowered_value_rel_topic_value_rel >> simp[] >>
  qexists_tac `entry.type` >> simp[]
QED

(* Checked source evaluation followed by forcing supplies the value; the
   allocation invariant supplies the payload and its address range, including
   empty bytestrings. A source name itself returns a place, not a value. *)
Theorem compile_name_topic_value_correct:
  !env cenv cx func ty ann id es ss cs op cs' p region_size.
    well_typed_expr env (Name ann id) /\ env_consistent env cx es /\
    state_well_typed es /\ state_rel_simple cenv cx es ss /\
    local_ptrs_rel func cenv es.scopes ss /\ event_indexable_type ann /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
    (is_bytestring_type ann ==> ss.vs_alloca_next <= dimword(:256)) /\
    fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (op,cs') ==>
    ?v out.
      (do result <- eval_expr cx (Name ann id); read_result cx result od) es =
        (INL v,es) /\
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      topic_value_rel env.type_defs (op,ann) v out /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all well_typed_Name_lookup >> strip_tac >> gvs[] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  `(do result <- eval_expr cx (Name ann id); read_result cx result od) es =
     (INL entry.value,es)` by
    (irule eval_name_lookup_scopes >> simp[]) >>
  mp_tac (Q.SPECL [`env.type_defs`, `func`, `cenv`, `es.scopes`, `ty`, `ann`,
    `id`, `entry`, `p`, `region_size`, `ss`, `cs`, `op`, `cs'`]
      lower_value_name_ptrvar_topic_correct) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >>
  qexistsl_tac [`entry.value`, `final`] >> simp[] >> conj_tac >>
  FIRST [irule state_rel_simple_assignment_frame >> qexists_tac `ss` >> simp[],
         irule local_ptrs_rel_assignment_frame >> qexists_tac `ss` >> simp[]]
QED
