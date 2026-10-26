(* Execute dynamic-child head/offset stores after the recursive child returns. *)
Theory abiEncoderChildSuffix
Ancestors
  abiEncoderChildCode abiEncoderWrites abiEncoderReentryLeaves abiBuiltinPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderFrame abiDecoderGuards abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding valueEncodingProps
  venomState venomExecSemantics venomInst words list arithmetic

Theorem abi_encoder_store_footprint:
  MEM (p,32) fp ==> abi_decode_footprint_frame fp s (mstore p w s)
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
      gvs[abi_footprint_disjoint_def] >> first_x_assum drule >> simp[]) >>
  simp[]
QED

Theorem abi_encoder_footprint_memory:
  abi_decode_footprint_frame fp s t /\ u.vs_memory = t.vs_memory /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_data_section = s.vs_data_section ==>
  abi_decode_footprint_frame fp s u
Proof
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_child_suffix_frame:
  abi_decode_footprint_frame [(h,32);(p,32)] s
    (mstore p next (mstore h off s))
Proof
  irule abi_decode_footprint_frame_trans >> qexists_tac `mstore h off s` >>
  conj_tac >> irule abi_encoder_store_footprint >> simp[]
QED

Theorem abi_encoder_child_suffix_words:
  h+32 <= p \/ p+32 <= h ==>
  mem_word_at h (mstore p next (mstore h off s)).vs_memory = off /\
  mem_word_at p (mstore p next (mstore h off s)).vs_memory = next
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [mstore_mem_word_at_same, mstore_mem_word_at_disjoint]
QED

Theorem abi_encoder_child_suffix_preserves_tail:
  (q+n <= h \/ h+32 <= q) /\ (q+n <= p \/ p+32 <= q) ==>
  mem_bytes_at q n (mstore p next (mstore h off s)).vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >> mp_tac (Q.INST [`fp` |-> `[(h,32);(p,32)]`, `p` |-> `q`,
    `t` |-> `mstore p next (mstore h off s)`] abi_decode_footprint_frame_slice) >>
  asm_simp_tac (srw_ss()) [abi_encoder_child_suffix_frame, abi_footprint_disjoint_def,
    DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem abi_encode_child_suffix_sequence:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\
  eval_operand head s = SOME (n2w h) /\ eval_operand dyn_ptr s = SOME (n2w p) /\
  eval_operand offset s = SOME (n2w off) /\ eval_operand child_len s = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\ inst_extends st st' /\
    eval_operand out actual = SOME (n2w len) /\ fresh_vars_wrt limit_st actual /\
    actual.vs_memory = (mstore p (n2w (off+len)) (mstore h (n2w off) s)).vs_memory /\
    abi_decode_footprint_frame [(h,32);(p,32)] s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  simp_tac bool_ss [abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void MSTORE [head;offset] st = ((),c1)` >>
  rename1 `emit_op ADD [offset;child_len] c1 = (next_offset,c2)` >>
  rename1 `emit_void MSTORE [dyn_ptr;next_offset] c2 = ((),ready)` >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emitted_insts_emit_op >>
  `c2.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`ptr_op` |-> `head`, `value_op` |-> `offset`, `p` |-> `h`,
    `w` |-> `n2w off:bytes32`, `st'` |-> `c1`] abi_encoder_emit_store) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >> qabbrev_tac `stored = mstore h (n2w off) s` >>
  mp_tac (Q.INST [`lhs` |-> `offset`, `rhs` |-> `child_len`, `out` |-> `next_offset`,
    `a` |-> `n2w off:bytes32`, `b` |-> `n2w len:bytes32`, `st` |-> `c1`, `st'` |-> `c2`,
    `s` |-> `stored:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_mstore] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st stored prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand dyn_ptr prepared = SOME (n2w p) /\ eval_operand child_len prepared = SOME (n2w len)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) [Abbr`stored`, eval_operand_mstore]) >>
  `eval_operand next_offset prepared = SOME (n2w (off+len))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`ptr_op` |-> `dyn_ptr`, `value_op` |-> `next_offset`,
    `w` |-> `n2w (off+len):bytes32`, `st` |-> `c2`, `st'` |-> `ready`,
    `s` |-> `prepared:venom_state`] abi_encoder_emit_store) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `actual = mstore p (n2w (off+len)) prepared` >>
  `run_inst_seq (emitted_insts st c2) s = OK prepared /\ inst_extends st c2` by
    (mp_tac (Q.INST [`st1` |-> `c1`, `st2` |-> `c2`, `s1` |-> `stored:venom_state`,
      `s2` |-> `prepared:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`stored`]) >>
  `run_inst_seq (emitted_insts st ready) s = OK actual /\ inst_extends st ready` by
    (mp_tac (Q.INST [`st1` |-> `c2`, `st2` |-> `ready`, `s1` |-> `prepared:venom_state`,
      `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >> asm_simp_tac bool_ss [Abbr`actual`]) >>
  `actual.vs_memory = (mstore p (n2w (off+len)) stored).vs_memory` by
    (simp_tac bool_ss [Abbr`actual`] >> irule abi_encoder_store_memory >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(h,32);(p,32)] s actual` by
    (mp_tac (Q.INST [`t` |-> `mstore p (n2w (off+len)) stored`, `u` |-> `actual:venom_state`,
      `fp` |-> `[(h,32);(p,32)]`] abi_encoder_footprint_memory) >>
     asm_simp_tac (srw_ss()) [Abbr`stored`, Abbr`actual`, abi_encoder_child_suffix_frame]) >>
  qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [Abbr`actual`, Abbr`stored`, eval_operand_mstore, ADD_COMM] >>
  rpt strip_tac >> irule eval_operand_mstore >> first_x_assum irule >>
  asm_simp_tac (srw_ss()) [eval_operand_mstore]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CHILD_SUFFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder child suffix not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderChildSuffix");
