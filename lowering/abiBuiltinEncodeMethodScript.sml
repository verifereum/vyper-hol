Theory abiBuiltinEncodeMethod
Ancestors
  abiBuiltinEncodeCode abiBuiltinEncodeFinish abiBuiltinPrefix abiEncoderWrites
  abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderGuards abiDecoderFrameCompose
  abiDecoderContract compileEnv emitHelper emitHelperProps exprLoweringProps venomInst
  venomState venomExecSemantics words list rich_list arithmetic abiEncoderMemory
  abiEncoderSequence abiDecoderTypedContract abiDecoderLoop fragExec instIdxIndep
  valueEncodingProps byte abiBuiltinEncodeAllocate abiBuiltinEncodeSetup abiBuiltinAllocation
  finite_map valueEncoding abiBuiltinEncodeInput abiBuiltinEncodeEffect
  abiBuiltinEncodeOwnership abiBuiltinEncodeBody abiBuiltinEncodeContext abiEncoderCorrect
  abiEncoderInput abiDecoderEffect abiDecoderAllocation builtinAbi exprLowering

(* ===== Builtin Encode Method ===== *)

(* Actual method-ID address computation and full-word store. Only the first
   four bytes are retained before the recursive payload overwrites the tail. *)

Theorem abi_builtin_encode_method_trace:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  ?method_ptr write_st.
    emit_op ADD [buf;Lit 32w] st = (method_ptr,write_st) /\
    emit_void MSTORE [method_ptr;Lit (mid << 224)] write_st = ((),final)
Proof
  simp_tac (srw_ss()) [abi_builtin_encode_method_id_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [buf;Lit 32w] st = (method_ptr,write_st)` >>
  qexistsl_tac [`method_ptr`, `write_st`] >> simp[]
QED

Theorem abi_builtin_encode_method_shape:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  final.cs_next_id = st.cs_next_id+2 /\ final.cs_next_var = st.cs_next_var+1 /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_builtin_encode_method_sequence:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    fresh_vars_wrt limit_st actual /\ mload (p+32) actual = mid << 224 /\
    abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `write_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`lhs` |-> `buf`, `rhs` |-> `Lit 32w`, `out` |-> `method_ptr`,
    `a` |-> `n2w p:bytes32`, `b` |-> `32w:bytes32`, `st'` |-> `write_st`,
    `s` |-> `initial:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix st write_st limit_st initial prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  mp_tac (Q.INST [`buf` |-> `method_ptr`, `value_op` |-> `Lit (mid << 224)`,
    `p` |-> `p+32:num`, `s` |-> `prepared:venom_state`, `st` |-> `write_st`,
    `w` |-> `(mid:bytes32) << 224`] abi_builtin_store_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [word_add_n2w, eval_operand_def] >> strip_tac >>
  `run_inst_seq (emitted_insts st final) initial = OK (mstore (p+32) (mid << 224) prepared) /\
   inst_extends st final` by
    (mp_tac (Q.INST [`st1` |-> `write_st`, `st2` |-> `final`, `s` |-> `initial:venom_state`,
      `s1` |-> `prepared:venom_state`, `s2` |-> `mstore (p+32) (mid << 224) prepared`]
      abi_decode_sequence_chain) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decode_frame (p+32) 32 initial (mstore (p+32) (mid << 224) prepared)` by
    (irule abi_decode_frame_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `mstore (p+32) (mid << 224) prepared` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

(* ===== Reach ===== *)

(* The actual full-word method-ID store yields its four-byte prefix at the
   containing-function endpoint, with the exact full-word write frame. *)

Definition abi_builtin_encode_method_bytes_def:
  abi_builtin_encode_method_bytes (mid:bytes32) = TAKE 4 (word_to_bytes (mid << 224) T)
End

Theorem abi_builtin_encode_method_bytes_length[simp]:
  LENGTH (abi_builtin_encode_method_bytes mid) = 4
Proof
  simp[abi_builtin_encode_method_bytes_def, LENGTH_word_to_bytes]
QED

Theorem abi_builtin_encode_method_window:
  mload p s = mid << 224 ==>
  mem_bytes_at p 4 s.vs_memory = abi_builtin_encode_method_bytes mid
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`p`, `[]:byte list`, `TAKE 4 (word_to_bytes ((mid:bytes32) << 224) T)`,
    `DROP 4 (word_to_bytes ((mid:bytes32) << 224) T)`, `s.vs_memory`]
    abi_decoder_source_subwindow) >>
  asm_simp_tac (srw_ss()) [TAKE_DROP, LENGTH_word_to_bytes, LENGTH_TAKE,
    abi_encoder_word_window, mem_word_at_eq_mload, abi_builtin_encode_method_bytes_def]
QED

Theorem abi_builtin_encode_method_reach:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  drule_all abi_builtin_encode_method_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule abi_builtin_encode_method_window >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

(* ===== Setup ===== *)

(* Actual allocation, data-pointer ADD and method-ID ADD/MSTORE setup. *)

Theorem abi_builtin_encode_method_setup_context:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func ==>
  ?address_st.
    abi_builtin_encode_allocate (maxlen+36) 36 st = (ops,address_st) /\
    abi_builtin_encode_method_id (SOME mid) (FST ops) address_st = ((),ready) /\
    fn_has_code st address_st func /\ fn_has_code address_st ready func /\
    address_st.cs_next_var = st.cs_next_var+2 /\ ready.cs_next_var = address_st.cs_next_var+1
Proof
  strip_tac >> drule abi_builtin_encode_setup_allocate_trace >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [GSYM ADD_ASSOC]) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  `cs_extends st address_st /\ cs_extends address_st ready` by
    (conj_tac >> irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `address_st`, `ready`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `address_st` >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_method_setup_reach:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,maxlen+36)) /\
  maxlen+36 < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+36)) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (maxlen+36) p 32 initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_method_setup_context >> strip_tac >>
  drule abi_builtin_encode_allocate_live >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`outsz` |-> `maxlen+36:num`, `data_offset` |-> `36:num`, `ctx` |-> `ctx`]
    abi_builtin_encode_allocate_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial addressed` >>
  mp_tac (Q.INST [`st` |-> `address_st`, `final` |-> `ready`, `buf` |-> `FST (ops:operand # operand)`,
    `initial` |-> `addressed:venom_state`, `ctx` |-> `ctx`] abi_builtin_encode_method_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func addressed actual` >>
  `actual.vs_halted = addressed.vs_halted` by simp[] >>
  `eval_operand (FST ops) actual = SOME (n2w p) /\
   eval_operand (SND ops) actual = SOME (n2w (p+36))` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (maxlen+36) p 32 initial actual` by
    (drule_all abi_builtin_encode_setup_frame_compose >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss []
QED

(* ===== Value ===== *)

(* Interpret the completed method prefix and recursive payload as source Bytes. *)

Theorem abi_builtin_encode_method_value:
  mload p s = n2w (LENGTH bytes+4) /\
  mem_bytes_at (p+32) 4 s.vs_memory = abi_builtin_encode_method_bytes mid /\
  mem_bytes_at (p+36) (LENGTH bytes) s.vs_memory = bytes ==>
  mem_bytes_at (p+32) (4+LENGTH bytes) s.vs_memory = abi_builtin_encode_method_bytes mid ++ bytes /\
  val_in_memory (BaseTV (BytesT (Dynamic (maxlen+4))))
    (vyperValue$BytesV (abi_builtin_encode_method_bytes mid ++ bytes)) p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at (p+32) (4+LENGTH bytes) s.vs_memory = abi_builtin_encode_method_bytes mid ++ bytes` by
    (ONCE_REWRITE_TAC [abi_encoder_mem_split] >> asm_simp_tac (srw_ss()) [GSYM ADD_ASSOC]) >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload,
    abi_builtin_encode_method_bytes_length, ADD_COMM] >>
  first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ADD_COMM])
QED

(* ===== Correct ===== *)

(* Complete lower_abi_encode with a method ID, from pure input/resources. *)

Theorem lower_abi_encode_method:
  lower_abi_encode ensure (SOME mid) src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av start (SOME mid) src sb source_cap
    p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+4) /\
    mem_bytes_at (p+32) (4+LENGTH (enc at av)) actual.vs_memory =
      abi_builtin_encode_method_bytes mid ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+4))))
      (vyperValue$BytesV (abi_builtin_encode_method_bytes mid ++ enc at av)) p actual.vs_memory /\
    abi_builtin_encode_effect first last start final limit_st p (maxlen+36) 32 b cap initial actual /\
    FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+36) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  qpat_assum `abi_builtin_encode_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss())
      [abi_builtin_encode_pre_def, LET_THM, GSYM ADD_ASSOC]) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ maxlen+36 < dimword (:256) /\
   p+32 < dimword (:256) /\ first <= ready.cs_next_id` by (asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `ctx` |-> `ctx`] abi_builtin_encode_method_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_builtin_encode_method_ready >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AC ADD_COMM ADD_ASSOC]) >>
  drule_all (SIMP_RULE (srw_ss()) [AC ADD_COMM ADD_ASSOC]
    (Q.INST [`mid_size` |-> `4:num`] abi_builtin_encode_body_finish)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid` by
    asm_simp_tac bool_ss [] >>
  drule_all abi_builtin_encode_method_value >> disch_then (qspec_then `maxlen` strip_assume_tac) >>
  `abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (maxlen+36) b cap prepared actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`, `ready.cs_next_var`,
       `LENGTH (enc at av)+36`] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, asm_simp_tac (srw_ss()) [] >> decide_tac]) >>
  `start.cs_next_id < ready.cs_next_id /\ ready.cs_next_id <= final.cs_next_id` by decide_tac >>
  `FLOOKUP prepared.vs_allocas start.cs_next_id = SOME (p,maxlen+36)` by
    (drule_all abi_builtin_encode_setup_frame_row >> simp[]) >>
  `FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+36)` by
    (mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `lo` |-> `ready.cs_next_id`,
      `next` |-> `ready.cs_next_var`, `d` |-> `p:num`,
      `sz` |-> `maxlen+36:num`, `outsz` |-> `maxlen+36:num`,
      `hi` |-> `final.cs_next_id`, `s` |-> `prepared:venom_state`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_body_allocation_row) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  drule_all abi_builtin_encode_effect_compose >> strip_tac >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
