Theory abiEncoderBytes
Ancestors
  abiEncoderInput abiEncoderInputFrame abiDecoderFrame abiDecoderContract valueEncoding
  valueEncodingProofs venomState contractABI words list arithmetic abiEncoderBytesCode
  abiEncoderWrites abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderGuards emitHelperProps exprLoweringProps emitHelper compileEnv venomExecSemantics
  venomInst abiEncoderBytesPrefix abiEncoderMemory venomMemProps abiEncoderRounding byte
  rich_list valueEncodingProps

(* ===== Active ===== *)

(* Byte-string encoder inputs observe only their count and active bytes.
   Unused semantic capacity need not be protected or copied. *)

Theorem abi_encoder_bytes_active:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb (32+LENGTH bs) mem
Proof
  simp[abi_encoder_input_bytes_iff]
QED

Theorem abi_encoder_bytes_active_relocate:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem /\
  mem_bytes_at sb (32+LENGTH bs) mem = mem_bytes_at db (32+LENGTH bs) mem' /\
  32+LENGTH bs <= outcap ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) db outcap mem'
Proof
  strip_tac >> drule abi_encoder_bytes_active >> strip_tac >>
  drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`db`, `mem'`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  irule abi_encoder_input_capacity >> qexists_tac `32+LENGTH bs` >> simp[]
QED

Theorem abi_encoder_bytes_active_frame:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint sb (32+LENGTH bs) fp ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap t.vs_memory
Proof
  strip_tac >>
  `32+LENGTH bs <= cap` by fs[abi_encoder_input_bytes_iff] >>
  `mem_bytes_at sb (32+LENGTH bs) s.vs_memory =
     mem_bytes_at sb (32+LENGTH bs) t.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[EQ_SYM_EQ]) >>
  drule_all abi_encoder_bytes_active_relocate >> simp[]
QED

Theorem abi_encoder_bytes_mcopy_prefix:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  32+LENGTH bs <= copied /\ 32+LENGTH bs <= outcap ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) db outcap
    (mcopy db sb copied s).vs_memory
Proof
  strip_tac >>
  `mem_bytes_at sb (32+LENGTH bs) s.vs_memory =
     mem_bytes_at db (32+LENGTH bs) (mcopy db sb copied s).vs_memory` by
    (mp_tac (Q.INST [`sb` |-> `sb`, `db` |-> `db`, `cap` |-> `copied`,
      `mem` |-> `s.vs_memory`, `mem'` |-> `(mcopy db sb copied s).vs_memory`,
      `off` |-> `0`, `len` |-> `32+LENGTH (bs:word8 list)`] abi_encoder_window_slice) >>
     simp[mcopy_mem_bytes_at_same]) >>
  drule_all abi_encoder_bytes_active_relocate >> simp[]
QED

(* ===== Copy ===== *)

(* Execute the actual zero-store, copy-length ADD and MCOPY bytes phase. *)

Theorem abi_encoder_copy_eval:
  eval_operand op (mcopy db sb cnt s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_copy_memory:
  s.vs_memory = t.vs_memory ==>
  (mcopy db sb cnt s).vs_memory = (mcopy db sb cnt t).vs_memory
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_bytes_copy_sequence:
  abi_encode_bytes_copy dst src len lastptr st = ((),st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w cnt) /\ eval_operand lastptr s = SOME (n2w (db+rounded)) /\
  db+rounded < dimword (:256) /\ sb < dimword (:256) /\ 32+cnt < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\
    actual.vs_memory = (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)).vs_memory /\
    fresh_vars_wrt limit_st actual /\ inst_extends st st' /\
    actual.vs_call_ctx = s.vs_call_ctx /\ actual.vs_data_section = s.vs_data_section /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void MSTORE [lastptr;Lit 0w] st = ((),c1)` >>
  rename1 `emit_op ADD [Lit 32w;len] c1 = (copylen,c2)` >>
  rename1 `emit_void MCOPY [dst;src;copylen] c2 = ((),end_st)` >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emitted_insts_emit_op >>
  `db < dimword (:256) /\ c2.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`ptr_op` |-> `lastptr`, `value_op` |-> `Lit 0w`, `p` |-> `db+rounded`,
    `w` |-> `0w:bytes32`, `st'` |-> `c1`] abi_encoder_emit_store) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  qabbrev_tac `stored = mstore (db+rounded) 0w s` >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `len`, `out` |-> `copylen`,
    `a` |-> `32w:bytes32`, `b` |-> `n2w cnt:bytes32`, `st` |-> `c1`, `st'` |-> `c2`,
    `s` |-> `stored:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_def, eval_operand_mstore] >>
  strip_tac >> rename1 `abi_builtin_prefix c1 c2 limit_st stored prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand dst prepared = SOME (n2w db) /\ eval_operand src prepared = SOME (n2w sb)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_mstore]) >>
  `eval_operand copylen prepared = SOME (n2w (32+cnt))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `src`, `len` |-> `copylen`,
    `cnt` |-> `32+cnt`, `st` |-> `c2`, `st'` |-> `end_st`, `s` |-> `prepared:venom_state`]
    abi_encoder_emit_copy) >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `run_inst_seq (emitted_insts st c2) s = OK prepared /\ inst_extends st c2` by
    (mp_tac (Q.INST [`st1` |-> `c1`, `st2` |-> `c2`, `s1` |-> `stored:venom_state`,
      `s2` |-> `prepared:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`stored`]) >>
  qexists_tac `mcopy db sb (32+cnt) prepared` >>
  asm_simp_tac bool_ss [abi_encoder_copy_eval] >> rpt conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`prepared`, `c2`] >> asm_simp_tac bool_ss [])
  >- (simp_tac bool_ss [ADD_COMM] >> irule abi_encoder_copy_memory >> asm_simp_tac bool_ss [])
  >- (irule inst_extends_trans >> qexists_tac `c2` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_encoder_write_observations, Abbr`stored`] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) [eval_operand_mstore]
QED

(* ===== Body ===== *)

(* Execute the bytes encoder through its copy, preserving the loaded length. *)

Theorem abi_encode_bytes_body_sequence:
  abi_encode_bytes_prefix dst src st = (ops,ready) /\
  abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  db+contractABI$ceil32 cnt < dimword (:256) /\ 32+cnt < dimword (:256) /\
  copied.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st copied) s = OK actual /\ inst_extends st copied /\
    fresh_vars_wrt limit_st actual /\ eval_operand (FST ops) actual = SOME (n2w cnt) /\
    abi_decoder_operand_live copied.cs_next_var (FST ops) /\
    actual.vs_memory = (mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory /\
    actual.vs_call_ctx = s.vs_call_ctx /\ actual.vs_data_section = s.vs_data_section /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_bytes_prefix_shape >> strip_tac >> drule abi_encode_bytes_copy_shape >> strip_tac >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= ready.cs_next_var /\
   ready.cs_next_var <= copied.cs_next_var` by decide_tac >>
  drule_all abi_encode_bytes_prefix_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st ready limit_st s prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w db)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var src /\ abi_decoder_operand_live ready.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`len` |-> `FST (ops:operand # operand)`, `lastptr` |-> `SND (ops:operand # operand)`,
    `st` |-> `ready`, `st'` |-> `copied`, `s` |-> `prepared:venom_state`,
    `rounded` |-> `contractABI$ceil32 cnt`] abi_encode_bytes_copy_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready copied) prepared = OK actual` >>
  `eval_operand (FST ops) actual = SOME (n2w cnt)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live copied.cs_next_var (FST ops)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `actual.vs_memory = (mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w s)).vs_memory` by
    (irule EQ_TRANS >>
     qexists_tac `(mcopy db sb (32+cnt) (mstore (db+contractABI$ceil32 cnt) 0w prepared)).vs_memory` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encoder_bytes_write_memory_cong >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live ready.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED

(* ===== Contract ===== *)

(* The bytes/string source contract supplies live data; the encoder supplies padding. *)

Theorem abi_encoder_bytes_padded_length:
  cnt+32+(contractABI$ceil32 cnt-cnt) = 32+contractABI$ceil32 cnt
Proof
  mp_tac abi_encoder_ceil32_bounds >> strip_tac >> decide_tac
QED

Theorem abi_encoder_bytes_encoding:
  at = Bytes NONE \/ at = String ==>
  enc at (BytesV bs) = word_to_bytes (n2w (LENGTH bs):bytes32) T ++
    bs ++ REPLICATE (contractABI$ceil32 (LENGTH bs)-LENGTH bs) 0w /\
  LENGTH (enc at (BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)
Proof
  strip_tac >> gvs[Once enc_def, enc_number_def, LET_THM, abi_encoder_bytes_padded_length]
QED

Theorem abi_encoder_bytes_input_memory:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  (sb+(32+LENGTH bs) <= db \/ db+(32+contractABI$ceil32 (LENGTH bs)) <= sb) ==>
  mem_bytes_at db (LENGTH (enc at (BytesV bs)))
    (mcopy db sb (32+LENGTH bs) (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s)).vs_memory =
    enc at (BytesV bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `payload` (MAP_EVERY assume_tac o CONJUNCTS) o
      REWRITE_RULE [abi_encoder_input_bytes_iff]) >>
  `payload = bs` by
    (qpat_x_assum `contractABI$BytesV bs = BytesV payload` mp_tac >>
     simp_tac (srw_ss()) [EQ_SYM_EQ]) >>
  qpat_x_assum `payload = bs` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`bs` |-> `bs:byte list`] abi_encoder_bytes_encoding) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:byte list)`] abi_encoder_ceil32_bounds) >> strip_tac >>
  `contractABI$ceil32 (LENGTH bs) <= LENGTH bs+32` by decide_tac >>
  mp_tac (Q.INST [`rounded` |-> `contractABI$ceil32 (LENGTH (bs:byte list))`] abi_encoder_bytes_zero_copy) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss []
QED

(* ===== Correct ===== *)

(* Complete emitted bytes/string encoder execution under enclosing freshness. *)

Theorem abi_encoder_bytes_sequence:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) /\
  abi_encoder_input (AbiBytestring maxlen) at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db+LENGTH (enc at av) < dimword (:256) /\
  (sb+cap <= db \/ db+LENGTH (enc at av) <= sb) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `bs` (MAP_EVERY assume_tac o CONJUNCTS) o REWRITE_RULE [abi_encoder_input_bytes_iff]) >>
  qpat_x_assum `av = contractABI$BytesV bs` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`bs` |-> `bs:byte list`] abi_encoder_bytes_encoding) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:byte list)`] abi_encoder_ceil32_bounds) >> strip_tac >>
  drule abi_encode_bytes_trace >> strip_tac >> drule abi_encode_bytes_suffix_shape >> strip_tac >>
  drule abi_encode_bytes_copy_shape >> strip_tac >> drule abi_encode_bytes_prefix_shape >> strip_tac >>
  `copied.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= copied.cs_next_var /\
   LENGTH bs+31 < dimword (:256) /\ db+contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
   32+LENGTH bs < dimword (:256)` by decide_tac >>
  `mload sb s = n2w (LENGTH bs)` by fs[mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (bs:byte list)`] abi_encode_bytes_body_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st copied) s = OK prepared` >>
  mp_tac (Q.INST [`len` |-> `FST (ops:operand # operand)`, `cnt` |-> `LENGTH (bs:byte list)`,
    `st` |-> `copied`, `st'` |-> `final`, `s` |-> `prepared:venom_state`]
    abi_encode_bytes_suffix_sequence) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix copied final limit_st prepared actual` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `sb+(32+LENGTH bs) <= db \/ db+(32+contractABI$ceil32 (LENGTH bs)) <= sb` by decide_tac >>
  `mem_bytes_at db (LENGTH (enc at (contractABI$BytesV bs)))
    (mcopy db sb (32+LENGTH bs) (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s)).vs_memory =
    enc at (contractABI$BytesV bs)` by
    (mp_tac (Q.INST [`maxlen` |-> `maxlen`, `cap` |-> `cap`] abi_encoder_bytes_input_memory) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_frame db (32+contractABI$ceil32 (LENGTH bs)) s
    (mcopy db sb (32+LENGTH bs) (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s))` by
    (irule abi_encoder_bytes_write_frame >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame db (32+contractABI$ceil32 (LENGTH bs)) s actual` by
    (mp_tac (Q.INST [`t` |-> `mcopy db sb (32+LENGTH (bs:byte list))
        (mstore (db+contractABI$ceil32 (LENGTH (bs:byte list))) 0w s)`,
      `u` |-> `actual:venom_state`, `sz` |-> `32+contractABI$ceil32 (LENGTH (bs:byte list))`]
      abi_encoder_frame_memory) >> asm_simp_tac bool_ss []) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op actual = SOME w` by
    (rpt strip_tac >> `abi_decoder_operand_live copied.cs_next_var op` by
      (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
     `eval_operand op prepared = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
     first_x_assum irule >> asm_simp_tac bool_ss []) >>
  (qexists_tac `actual` >> asm_simp_tac (srw_ss()) [abi_encoder_bytes_padded_length] >>
   qpat_x_assum `mem_bytes_at db (LENGTH (enc at _)) _ = _` mp_tac >>
   asm_simp_tac (srw_ss()) [abi_encoder_bytes_padded_length])
QED
