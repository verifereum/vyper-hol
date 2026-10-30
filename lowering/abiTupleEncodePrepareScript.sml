Theory abiTupleEncodePrepare
Ancestors
  abiTupleProps abiTupleEncodeSlot exprLowering context compileEnv emitHelperProps
  exprLoweringProps venomInst words list rich_list arithmetic abiTupleEncodeResult
  abiTupleEncodeInput abiTupleEncodeMemory abiDecoderReentry abiDecoderContract
  abiDecoderFrameCompose venomState venomExecSemantics abiBuiltinAllocation emitHelper
  abiDecoderGuards finite_map abiEncoderSequence abiDecoderLoop fragExec instIdxIndep
  abiTupleEncodeAssembly abiTupleEncodeLayout abiBuiltinEncodeResources abiBuiltinEncodeInput

(* Compiler provenance for the complete tuple producer. *)
Theorem abi_tuple_encode_store_cons:
  compile_store_abi_tuple ce buf off ((op,ty)::xs) =
  do compile_abi_tuple_slot ce buf off op ty;
     compile_store_abi_tuple ce buf (off+type_memory_bytes ce ty) xs od
Proof
  simp[FUN_EQ_THM, compile_store_abi_tuple_def, compile_abi_tuple_slot_def,
    comp_bind_def, comp_ignore_bind_def] >>
  qx_gen_tac `st` >> Cases_on `emit_op ADD [buf;Lit (n2w off)] st` >> simp[]
QED

Theorem abi_tuple_encode_store_shape:
  !xs ce buf off st final. compile_store_abi_tuple ce buf off xs st = ((),final) ==>
  final.cs_next_var = st.cs_next_var+LENGTH xs /\ st.cs_next_id <= final.cs_next_id /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def, emitted_insts_def, inst_extends_refl] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >> first_x_assum drule >> strip_tac >>
  `inst_extends st final` by
    (irule inst_extends_trans >> qexists_tac `middle` >> asm_simp_tac bool_ss []) >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    (irule isPREFIX_TRANS >> qexists_tac `middle.cs_current_insts` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> decide_tac
QED

(* Execute every actual tuple slot, preserving complete nonword sources for
   later slots and complete child input already written by earlier slots. *)
Theorem abi_tuple_encode_tail_inputs:
  abi_tuple_encode_result sf ce [(op,ty)] [at] [av] st middle limit_st d s t /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  st.cs_next_var <= middle.cs_next_var /\ lo <= d /\ d+type_memory_bytes ce ty <= hi ==>
  abi_tuple_encode_inputs sf ce xs ats avs middle.cs_next_var lo hi t
Proof
  strip_tac >> qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [abi_tuple_encode_result_def, abi_tuple_bytes_def]) >>
  `lo <= hi` by decide_tac >>
  `abi_decode_frame lo (hi-lo) s t` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `type_memory_bytes ce ty`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all abi_tuple_encode_inputs_transport >> simp[]
QED

Theorem abi_tuple_encode_sequence:
  !xs ce buf off st final s baddr ats avs lo hi.
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ abi_decoder_operand_live st.cs_next_var buf /\
  lo <= baddr+off /\ baddr+off+abi_tuple_bytes ce xs <= hi /\ hi < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_encode_result sf ce xs ats avs st final limit_st (baddr+off) s actual
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_encode_inputs_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[abi_tuple_encode_result_def, emitted_insts_def, run_inst_seq_def, inst_extends_refl,
        abi_tuple_encode_memory_def, abi_tuple_bytes_def, abi_decode_frame_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[abi_tuple_encode_inputs_def] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  rename1 `abi_tuple_encode_input sf ce h1 head_at head_av h0 st.cs_next_var lo hi s` >>
  rename1 `abi_tuple_encode_inputs sf ce xs tail_ats tail_avs st.cs_next_var lo hi s` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
   baddr+off < dimword (:256) /\ lo <= hi /\ baddr+off+type_memory_bytes ce h1 <= hi /\
   lo <= baddr+(off+type_memory_bytes ce h1) /\
   baddr+(off+type_memory_bytes ce h1)+abi_tuple_bytes ce xs <= hi` by
    (fs[abi_tuple_bytes_def] >> decide_tac) >>
  drule_all abi_tuple_encode_result_slot >> strip_tac >>
  rename1 `abi_tuple_encode_result sf ce [(h0,h1)] [head_at] [head_av] st middle limit_st (baddr+off) s written` >>
  drule_all abi_tuple_encode_tail_inputs >> strip_tac >>
  qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_result_def]) >>
  `eval_operand buf written = SOME (n2w baddr)` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live middle.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  qpat_x_assum `!ce buf off st final s baddr ats avs lo hi. _`
    (qspecl_then [`ce`, `buf`, `off+type_memory_bytes ce h1`, `middle`, `final`, `written`,
      `baddr`, `tail_ats`, `tail_avs`, `lo`, `hi`] (mp_tac o PURE_REWRITE_RULE [ADD_ASSOC])) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `abi_tuple_encode_result sf ce xs tail_ats tail_avs middle final limit_st _ written actual` >>
  qexists_tac `actual` >> RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  mp_tac (Q.INST [`op` |-> `h0`, `ty` |-> `h1`, `at` |-> `head_at`, `av` |-> `head_av`,
    `ats` |-> `tail_ats`, `avs` |-> `tail_avs`, `d` |-> `baddr+off`,
    `t` |-> `written:venom_state`, `u` |-> `actual:venom_state`]
    (Q.ISPEC `h0:operand` (Q.GEN `op` abi_tuple_encode_result_cons))) >>
  asm_simp_tac bool_ss [ADD_ASSOC]
QED

(* ===== Code ===== *)

(* Allocation plus all tuple writes stays in its actual containing block. *)

Theorem abi_tuple_encode_alloc_shape:
  compile_alloc_buffer n st = (buf,allocated) ==>
  allocated.cs_next_var = st.cs_next_var+1 /\ allocated.cs_next_id = st.cs_next_id+1 /\
  allocated.cs_blocks = st.cs_blocks /\ allocated.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts allocated.cs_current_insts /\ inst_extends st allocated /\
  abi_decoder_operand_live allocated.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st allocated)
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_tuple_encode_stage_shape:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) ==>
  staged.cs_next_var = st.cs_next_var+1+LENGTH xs /\ st.cs_next_id < staged.cs_next_id /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts staged.cs_current_insts /\ inst_extends st staged /\
  allocated.cs_next_var <= staged.cs_next_var /\ abi_decoder_operand_live staged.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st staged)
Proof
  strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `inst_extends st staged` by
    (irule inst_extends_trans >> qexists_tac `allocated` >> asm_simp_tac bool_ss []) >>
  `isPREFIX st.cs_current_insts staged.cs_current_insts` by
    (irule isPREFIX_TRANS >> qexists_tac `allocated.cs_current_insts` >> asm_simp_tac bool_ss []) >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `allocated.cs_next_var <= staged.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live staged.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> decide_tac
QED

(* ===== Sequence ===== *)

(* Execute allocation and complete tuple construction, including site reuse. *)

Theorem abi_tuple_encode_stage_sequence:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_memory sf ce xs ats avs sb actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  `abi_tuple_bytes ce xs < dimword (:256) /\ allocated.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= allocated.cs_next_var` by decide_tac >>
  drule_all abi_builtin_alloc_buffer_frame >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id _ initial addressed` >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `abi_tuple_encode_inputs sf ce xs ats avs allocated.cs_next_var sb (sb+abi_tuple_bytes ce xs) addressed` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `later` |-> `allocated.cs_next_var`,
      `lo` |-> `sb:num`, `hi` |-> `sb+abi_tuple_bytes ce xs`, `s` |-> `initial:venom_state`,
      `t` |-> `addressed:venom_state`] (SPEC_ALL abi_tuple_encode_inputs_transport)) >>
     impl_tac >- (asm_simp_tac bool_ss [abi_decode_frame_def] >> decide_tac) >> simp[]) >>
  mp_tac (SIMP_RULE (srw_ss()) [] (Q.INST [`buf` |-> `source_buf.buf_operand`, `off` |-> `0:num`,
    `st` |-> `allocated`, `final` |-> `staged`, `s` |-> `addressed:venom_state`,
    `baddr` |-> `sb:num`, `lo` |-> `sb:num`, `hi` |-> `sb+abi_tuple_bytes ce xs`]
    (SPEC_ALL abi_tuple_encode_sequence))) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss [] >> decide_tac]) >>
  strip_tac >> rename1 `abi_tuple_encode_result sf ce xs ats avs allocated staged limit_st sb addressed encoded` >>
  qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_result_def]) >>
  `eval_operand source_buf.buf_operand encoded = SOME (n2w sb)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame sb (abi_tuple_bytes ce xs) initial encoded` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  `run_inst_seq (emitted_insts st staged) initial = OK encoded /\ inst_extends st staged` by
    (mp_tac (Q.INST [`st1` |-> `allocated`, `st2` |-> `staged`, `s` |-> `initial:venom_state`,
      `s1` |-> `addressed:venom_state`, `s2` |-> `encoded:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `encoded` >> asm_simp_tac bool_ss [] >> qx_genl_tac [`older`, `older_word`] >> strip_tac >>
  `eval_operand older addressed = SOME older_word` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live allocated.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Reach ===== *)

(* Reach the real encoder entry after allocation and all tuple writes. *)

Theorem abi_tuple_encode_stage_reach:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_memory sf ce xs ats avs sb actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_tuple_encode_stage_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

(* The actual tuple producer establishes complete encoder input. Its future
   resources depend only on numeric bounds and pure allocation metadata. *)
Theorem abi_tuple_encode_prepare:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  abi_tuple_encode_layout ce xs ats /\ has_type (Tuple ats) (ListV avs) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
  abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap
    (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_builtin_encode_pre (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
      (Tuple ats) (ListV avs) staged method_id_opt source_buf.buf_operand sb (abi_tuple_bytes ce xs)
      p maxlen first last b cap actual /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  qpat_assum `abi_builtin_encode_resources _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]) >>
  drule_all abi_tuple_encode_stage_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_tuple_encode_input >> strip_tac >>
  `abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual` by
    (mp_tac (Q.INST [`st` |-> `staged`, `ready` |-> `staged`,
      `source_cap` |-> `abi_tuple_bytes ce (xs:(operand # type) list)`,
      `s` |-> `abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce (xs:(operand # type) list)) initial`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_resources_transport) >>
     impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_builtin_encode_pre_resources] >> first_assum ACCEPT_TAC
QED
