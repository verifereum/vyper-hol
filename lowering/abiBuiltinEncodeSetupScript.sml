Theory abiBuiltinEncodeSetup
Ancestors
  abiBuiltinEncodeCode abiBuiltinEncodeContext abiBuiltinAllocation abiBuiltinSetupFrames
  abiBuiltinPrefix abiEncoderSequence abiEncoderBytesPrefix abiDecoderReentry
  abiDecoderDynamicLoopSetup abiDecoderGuards abiDecoderContract abiDecoderLoop fragExec
  instIdxIndep compileEnv emitHelperProps exprLoweringProps venomState venomExecSemantics
  finite_map words list arithmetic abiEncoderInputFrame abiEncoderInput abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderFrameCompose

(* ===== Builtin Encode Setup ===== *)

(* Allocation and pointer setup for the ABI encoder without a method ID.
   Both fresh allocation and re-entry at an existing output site are covered. *)

Theorem abi_builtin_encode_setup_none_execute:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,maxlen+32)) /\
  maxlen+32 < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st ready) initial = OK actual /\
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32)) /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (maxlen+32) initial actual /\
    inst_extends st ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_setup_trace >> strip_tac >>
  qpat_x_assum `abi_builtin_encode_method_id NONE _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [abi_builtin_encode_method_id_def, comp_return_def]) >>
  disch_then SUBST_ALL_TAC >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= allocated.cs_next_var`
    by decide_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `outsz` |-> `maxlen+32:num`,
    `st'` |-> `allocated`] abi_builtin_alloc_buffer_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (maxlen+32) initial allocated_s` >>
  mp_tac (Q.INST [`lhs` |-> `buf.buf_operand`, `rhs` |-> `Lit 32w`, `out` |-> `data_ptr`,
    `a` |-> `n2w p:bytes32`, `b` |-> `32w:bytes32`, `st` |-> `allocated`,
    `st'` |-> `ready`, `s` |-> `allocated_s:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix allocated ready limit_st allocated_s actual` >>
  `eval_operand buf.buf_operand actual = SOME (n2w p)` by
    (drule_all abi_encoder_prefix_eval >> simp[]) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (maxlen+32) initial actual` by
    (irule abi_builtin_allocation_frame_suffix >>
     qexistsl_tac [`allocated_s`, `allocated.cs_next_var`] >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `actual` >> gvs[word_add_n2w]
QED

Theorem abi_builtin_encode_setup_none_reach:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,maxlen+32)) /\
  maxlen+32 < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32)) /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (maxlen+32) initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule_all abi_builtin_encode_setup_none_execute >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

(* ===== Frame ===== *)

(* Exact allocator metadata and memory frame for a method-ID setup store.
   write_size records the full store width independently of returned prefix size. *)

Definition abi_builtin_encode_setup_frame_def:
  abi_builtin_encode_setup_frame next site outsz p write_size s t <=>
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_frame (p+32) write_size s t /\ t.vs_halted = s.vs_halted /\
    t.vs_allocas = (abi_builtin_allocate_state site outsz s).vs_allocas /\
    t.vs_alloca_next = (abi_builtin_allocate_state site outsz s).vs_alloca_next
End

Theorem abi_builtin_encode_setup_frame_compose:
  abi_builtin_allocation_frame next site outsz initial addressed /\
  abi_decode_frame (p+32) write_size addressed prepared /\
  prepared.vs_allocas = addressed.vs_allocas /\ prepared.vs_alloca_next = addressed.vs_alloca_next /\
  prepared.vs_halted = addressed.vs_halted /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op addressed = SOME w ==>
    eval_operand op prepared = SOME w) /\ next <= child_next ==>
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `abi_decode_frame (p+32) write_size initial prepared` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >>
     asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  asm_simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> rpt strip_tac >>
  `eval_operand op addressed = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live child_next op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `next` >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_setup_frame_budget:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  (abi_decoder_budget first last b cap t <=>
    abi_decoder_budget first last b cap (abi_builtin_allocate_state site outsz s))
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> strip_tac >>
  irule abi_decoder_budget_transport >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_setup_frame_input:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  abi_encoder_input ei at av sb source_cap s.vs_memory /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) ==>
  abi_encoder_input ei at av sb source_cap t.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
  qpat_assum `abi_decode_frame _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  `mem_bytes_at sb source_cap s.vs_memory = mem_bytes_at sb source_cap t.vs_memory` by
    (irule EQ_SYM >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED
