Theory abiDecoderReentryPointer
Ancestors
  abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderTypedContract
  abiDecoderFrame abiDecoderContract emitHelperProps exprLoweringProps compileEnv valueEncoding
  venomState venomExecProps arithmetic finite_map abiDecoderPrimitiveCaller
  abiDecoderClampedWord abiDecoderClamp abiDecoderCoherence abiEncoder emitHelper
  venomExecSemantics venomInst fragExec instIdxIndep words list rich_list abiDecoderBytesFrame
  abiDecoderBytestring abiDecoderBytesTyped abiDecoderString exprLowering vyperABI vyperTyping
  vyperValue contractABI abiDecoderMemberBound abiDecoderReservation abiDecoderArrayBound
  abiDecoderArrayPtr

(* Lift existing fresh-state sequence proofs to repeated execution. The public
   postcondition protects live operands and freshness at the enclosing bound. *)
Theorem abi_decoder_post_vars_extend:
  abi_decoder_post tv v st' d sz b cap (abi_decoder_prune_vars next initial) clean /\
  abi_decoder_vars_extend initial.vs_vars clean actual /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w) /\
  abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual
Proof
  strip_tac >>
  qpat_assum `abi_decoder_post _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_post_def]) >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `fresh_vars_wrt limit_st clean` by
    (mp_tac (Q.SPECL [`st'`, `limit_st`, `clean`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  `!n. limit_st.cs_next_var <= n ==> STRING #"%" (toString n) NOTIN FDOM initial.vs_vars`
    by fs[fresh_vars_wrt_def, GREATER_EQ] >>
  `fresh_vars_wrt limit_st actual` by
    (drule_all abi_decoder_vars_extend_fresh >> simp[]) >>
  `abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual` by
    fs[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars next initial) = SOME w` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `eval_operand op clean = SOME w` by metis_tac[] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem abi_decoder_sequence_halted:
  run_inst_seq insts s = OK t ==> t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_halted` run_inst_seq_preserves_field)) >>
  qexists_tac `insts` >> simp[] >> rpt strip_tac >>
  drule_all step_inst_base_OK_preserves_halted >> simp[]
QED

Theorem abi_decoder_reentry_frame:
  abi_decode_frame d sz (abi_decoder_prune_vars next initial) clean /\
  abi_decoder_vars_extend initial.vs_vars clean actual ==>
  abi_decode_frame d sz initial actual
Proof
  strip_tac >> drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  fs[abi_decode_frame_def, abi_decoder_prune_vars_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_sequence_reentry:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  run_inst_seq insts (abi_decoder_prune_vars next initial) = OK clean /\
  abi_decoder_post tv v st' d sz b cap (abi_decoder_prune_vars next initial) clean /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq insts initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_footprint_frame [(d,sz);(b,cap)] initial actual /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars (abi_decoder_prune_vars next initial) initial`
    by irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_post_vars_extend >> strip_tac >>
  `actual.vs_halted = initial.vs_halted` by
    (drule_all abi_decoder_sequence_halted >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Primitive child decoders may run repeatedly with stale local bindings.
   Their frame excludes scratch slots and their allocator state is unchanged. *)
Theorem abi_decoder_word_reentry_code:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def,
      abi_decode_source_opcode_def]
QED

Theorem abi_decoder_typed_word_sequence_frame:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d 32 b cap s t /\ abi_decode_frame d 32 s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_typed_primitive_word_sequence >> strip_tac >>
  drule abi_decoder_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_clamp >> strip_tac >>
  `abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
   eval_operand dst s = SOME (n2w d) /\ fresh_vars_wrt st s /\ d < dimword (:256)` by
    (qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [abi_decoder_recursive_pre_def, abi_decoder_pre_def,
       abi_decoder_ranges_def] >> rpt strip_tac >> asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all abi_decoder_clamped_word_copied_window >> strip_tac >> gvs[]
QED

Theorem abi_decoder_primitive_reentry_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule_all abi_decoder_typed_word_sequence_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_primitive_reentry_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
      abi_decode_frame d 32 initial actual /\
      actual.vs_allocas = initial.vs_allocas /\
      actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_primitive_reentry_sequence >> strip_tac >>
  qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

(* Bytestring children execute with stale local SSA bindings under enclosing freshness. *)
Theorem abi_decoder_typed_bytestring_sequence_frame:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap s t /\
    abi_decode_frame d (type_memory_bytes ce ty) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[Excl "enc_def"] >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  Cases_on `av` >>
  gvs[abi_decoder_metadata_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    has_type_def, abi_to_vyper_def, AllCaseEqs(), Excl "enc_def"] >>
  fs[type_to_abi_dec_info_def] >>
  FIRST [drule_all abi_decoder_typed_bytes_sequence_frame >>
      simp[GSYM (cj 1 abi_decoder_bytes_copy_size)],
    drule_all abi_decoder_typed_string_sequence_frame >> simp[]]
QED

Theorem abi_decoder_bytestring_reentry_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_frame d (type_memory_bytes ce ty) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule_all abi_decoder_typed_bytestring_sequence_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_bytestring_reentry_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
        eval_operand op actual = SOME w) /\
      abi_decode_frame d (type_memory_bytes ce ty) initial actual /\
      actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_bytestring_reentry_sequence >> strip_tac >>
  qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx, Excl "enc_def"] >>
  first_assum ACCEPT_TAC
QED

(* Successful address/guard prefixes can be re-entered without requiring all
   their old output variables to be absent from the enclosing loop state. *)
Theorem abi_decoder_prefix_vars_extend:
  abi_decoder_vars_extend initial.vs_vars clean actual /\
  fresh_vars_wrt st' clean /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\
  (!op w. eval_operand op (abi_decoder_prune_vars next initial) = SOME w ==>
    eval_operand op clean = SOME w) ==>
  fresh_vars_wrt limit_st actual /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w)
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st clean` by
    (mp_tac (Q.SPECL [`st'`, `limit_st`, `clean`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  `!n. limit_st.cs_next_var <= n ==> STRING #"%" (toString n) NOTIN FDOM initial.vs_vars`
    by fs[fresh_vars_wrt_def, GREATER_EQ] >>
  `fresh_vars_wrt limit_st actual` by
    (drule_all abi_decoder_vars_extend_fresh >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars next initial) = SOME w` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `eval_operand op clean = SOME w` by metis_tac[] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem abi_decoder_sequence_reentry_prefix:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) insts /\
  run_inst_seq insts (abi_decoder_prune_vars next initial) = OK clean /\
  fresh_vars_wrt st' clean /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\
  (!op w. eval_operand op (abi_decoder_prune_vars next initial) = SOME w ==>
    eval_operand op clean = SOME w) ==>
  ?actual. run_inst_seq insts initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars (abi_decoder_prune_vars next initial) initial`
    by irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_prefix_vars_extend >> strip_tac >>
  `actual.vs_halted = initial.vs_halted` by
    (drule_all abi_decoder_sequence_halted >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Member navigation preserves observations when decoder temporaries are reused.
   TOP-LEVEL: abi_decoder_member_pointer_reentry.
   Helpers: opcode certificate and fresh-state sequence execution. *)
Theorem abi_decoder_member_pointer_code:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> Cases_on `dyn` >> gvs[abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >>
  gvs[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem abi_decoder_member_pointer_counters:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') ==>
  st'.cs_next_var = st.cs_next_var + (if dyn then if hi = Lit 0w then 3 else 5 else 1) /\
  abi_decoder_operand_live st'.cs_next_var member_op
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  imp_res_tac abi_decoder_operand_live_emit >> gvs[] >>
  FIRST [first_assum ACCEPT_TAC,
    irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var + 3` >>
    conj_tac >- decide_tac >> first_assum ACCEPT_TAC]
QED

Theorem abi_decoder_member_pointer_sequence:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  (dyn ==> abi_decode_load opc (n2w (sb + off) : bytes32) s = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + if dyn then payload_off else off)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `dyn` >> simp_tac bool_ss [] >> strip_tac >>
  FIRST [drule_all abi_decode_static_member_pointer >> simp[],
    drule_all abi_decode_dynamic_member_pointer >> simp[]]
QED

Theorem abi_decoder_member_pointer_reentry:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  (dyn ==> abi_decode_load opc (n2w (sb + off) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand member_op actual = SOME (n2w (sb + if dyn then payload_off else off)) /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_memory = initial.vs_memory /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb)`
    by asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `dyn ==> abi_decode_load opc (n2w (sb + off) : bytes32)
      (abi_decoder_prune_vars st.cs_next_var initial) = n2w payload_off /\
    sb + payload_off < dimword (:256)` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)`
    by irule abi_decoder_prune_fresh >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_decoder_member_pointer_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `dyn ==> abi_decode_source_opcode opc` by simp[] >>
  drule_all abi_decode_member_pointer_allocation_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_prune_vars_def]
QED

(* Dynamic-element navigation is safe on every iteration, including guarded
   memory sources. Only temporaries allocated by this prefix are overwritten. *)
Theorem abi_decoder_array_pointer_code:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def,
      abi_decode_source_opcode_def, is_terminator_def, is_alloca_op_def]
QED

Theorem abi_decoder_array_pointer_sequence:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand elem_src s = SOME p /\
  eval_operand src_data s = SOME (n2w data_base) /\
  abi_decode_load opc (p:bytes32) s = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    data_base + child_off + abi_sz <= hb /\ hb < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (data_base + child_off)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w` >> asm_simp_tac bool_ss [] >> strip_tac >>
  FIRST [drule_all abi_decode_array_pointer_sentinel >> simp[],
         drule_all abi_decode_bounded_array_pointer >> simp[]]
QED

Theorem abi_decoder_array_pointer_reentry:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand elem_src initial = SOME p /\
  eval_operand src_data initial = SOME (n2w data_base) /\
  abi_decode_load opc (p:bytes32) initial = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    data_base + child_off + abi_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  abi_decoder_operand_live st.cs_next_var src_data /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand child_op actual = SOME (n2w (data_base + child_off)) /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_memory = initial.vs_memory /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand elem_src (abi_decoder_prune_vars st.cs_next_var initial) = SOME p /\
   eval_operand src_data (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w data_base)`
    by asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `abi_decode_load opc (p:bytes32) (abi_decoder_prune_vars st.cs_next_var initial) = n2w child_off`
    by fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)`
    by irule abi_decoder_prune_fresh >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_decoder_array_pointer_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [abi_decoder_prune_eval] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_array_pointer_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_prune_vars_def]
QED
