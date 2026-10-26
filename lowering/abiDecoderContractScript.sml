(* Canonical-success interface probes, not recursive decoder correctness. *)
Theory abiDecoderContract
Ancestors
  fragExec abiBoundaryChecks abiTupleProps emitHelperProps valueEncodingProps
  exprLowering vyperABI venomExecSemantics venomInst venomState compileEnv abiEncoder
  emitHelper valueEncoding words venomExecProofs exprLoweringProps

(* Contract-design handoff (C6.4): abi_decode_read, abi_decode_word_fragment
   and the two empty-fragment probes below validate only specialized interfaces.
   They do NOT establish recursive decoder correctness. A general precondition
   still needs all of the following, to be justified by layout/range consumers:
   - evaluate_type tenv ty = SOME tv and a typed value;
   - descriptor = type_to_abi_dec_info cenv.ce_struct_fields cenv ty, with
     agreement of semantic/compiler struct and flag metadata on reachable types;
   - canonical ABI bytes through abi_decode_source, and nonwrapping head/tail
     source ranges, not merely equality of ABI and memory buffer sizes;
   - nonwrapping destination range of type_memory_bytes cenv ty;
   - a real hi bounds the canonical source end (the sentinel adds no premise);
   - memory-source bytes still needed must survive output and scratch writes;
     calldata and data-section sources are immutable;
   - mutually disjoint, capacity-bounded scratch ranges, also separate from
     source/output. SSA freshness alone supplies none of these memory facts.
   The general frame must allow scratch writes; abi_decode_frame below is
   appropriate for the scratch-free word probe, not for the recursive decoder.

   CFG handoff: conditional composition must expose the chosen successor.
   Header/body/exit composition needs i <= count, variant count-i, stable
   header reload of the source count, operand/freshness preservation, and a
   body increment i'=i+1 without wrap. The invariant separates initialized
   output prefix from untouched source and scratch. frag_exec_seq alone does
   not establish this finite-loop rule. These are outstanding obligations,
   not assumptions of execution success and not results of these probes. *)

Definition abi_decode_source_def:
  abi_decode_source opc s =
    if opc = CALLDATALOAD then s.vs_call_ctx.cc_calldata
    else if opc = DLOAD then s.vs_data_section else s.vs_memory
End

Definition abi_decode_load_def:
  abi_decode_load opc p s =
    if opc = MLOAD then mload (w2n p) s
    else word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n p) (abi_decode_source opc s) ++ REPLICATE 32 0w))
End

Definition abi_decode_source_opcode_def:
  abi_decode_source_opcode opc <=>
    opc = MLOAD \/ opc = CALLDATALOAD \/ opc = DLOAD
End

(* Frames are byte observations, allowing destination expansion. *)
Definition abi_decode_frame_def:
  abi_decode_frame d sz before after <=>
    (!p k. p + k <= d \/ d + sz <= p ==>
      mem_bytes_at p k after.vs_memory = mem_bytes_at p k before.vs_memory) /\
    after.vs_call_ctx = before.vs_call_ctx /\
    after.vs_data_section = before.vs_data_section
End

Theorem abi_decode_read_step:
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p ==>
  step_inst_base (mk_inst id opc [src] [out]) s =
    OK (update_var out (abi_decode_load opc p s) s)
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >>
  simp[abi_decode_load_def, abi_decode_source_def, step_MLOAD,
       step_CALLDATALOAD] >>
  simp[Once step_inst_base_def, exec_read1_def]
QED

Theorem abi_decode_read:
  emit_op opc [src] st = (v,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand v s' = SOME (abi_decode_load opc p s) /\
    same_blocks st st' /\ fresh_vars_wrt st' s' /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s' = SOME w) /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`opc`, `abi_decode_load opc`] emit_op_read1_correct) >>
  disch_then drule >> disch_then (qspecl_then [`p`, `s`] mp_tac) >>
  simp[abi_decode_read_step] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id opc [src]
      [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
       (abi_decode_load opc p s) s)` by
    (irule abi_decode_read_step >> simp[]) >>
  gvs[run_inst_seq_def, update_var_def]
QED

(* Empty tuples emit no instructions when the sentinel bound is used.
   P is unrestricted: no success assumption is needed. *)
Theorem abi_decode_empty_fragment:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (DecComplex F []) st = ((),st') ==>
  frag_exec ctx st st' P P (K F)
Proof
  simp[compile_abi_decode_to_buf_def, comp_return_def] >>
  strip_tac >> gvs[] >> irule frag_exec_refl >> simp[]
QED

Theorem abi_decode_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    val_in_memory (BaseTV (UintT 256))
      (IntV (&w2n (abi_decode_load opc p s))) d s'.vs_memory /\
    abi_decode_frame d 32 s s' /\
    fresh_vars_wrt st' s' /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s' = SOME w) /\
    same_blocks st st' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >>
  drule_all abi_decode_read >> strip_tac >> gvs[] >>
  `eval_operand dst s' = SOME (n2w d)` by metis_tac[] >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts st st' = emitted_insts st cs' ++ emitted_insts cs' st'` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK ss'` by
    (qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
     qpat_x_assum `run_inst_seq (emitted_insts st cs') s = OK s'`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts cs' st'` SUBST1_TAC) >> simp[]) >>
  `same_blocks st st'` by
    (gvs[same_blocks_def]) >>
  qexists_tac `ss'` >>
  simp[same_blocks_def, val_in_memory_def,
       val_to_w256_def, mstore_mem_word_at_same, w2n_n2w,
       integer_wordTheory.i2w_pos, n2w_w2n] >>
  conj_tac
  >- (simp[abi_decode_frame_def] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `s'.vs_memory = _` (SUBST1_TAC o SYM) >>
          irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      simp[mstore_def]) >>
  gvs[abi_decode_source_opcode_def, is_terminator_def]
QED

Definition abi_decode_word_pre_def:
  abi_decode_word_pre st src dst opc p d w s <=>
    abi_decode_source_opcode opc /\ fresh_vars_wrt st s /\
    eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
    d + 32 <= dimword (:256) /\ abi_decode_load opc p s = w
End

Theorem abi_decode_word_fragment:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  frag_exec ctx st st'
    (\s. s = s0 /\ abi_decode_word_pre st src dst opc p d w s)
    (\s'. val_in_memory (BaseTV (UintT 256)) (IntV (&w2n w)) d s'.vs_memory /\
          abi_decode_frame d 32 s0 s')
    (K F)
Proof
  strip_tac >> irule frag_exec_run_inst_seq >>
  conj_tac
  >- (rpt strip_tac >> disj1_tac >>
      fs[abi_decode_word_pre_def] >>
      `d < dimword (:256)` by decide_tac >>
      drule_all abi_decode_word_sequence >> strip_tac >>
      gvs[abi_decode_frame_def] >> metis_tac[]) >>
  gvs[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
      compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def,
      rich_listTheory.DROP_LENGTH_APPEND, abi_decode_source_opcode_def,
      is_terminator_def, rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def]
QED

(* A single successful pure emission changes only the SSA map. *)
Theorem abi_guard_emit_frame[local]:
  emit_op opc ops st = (v,st') /\
  (opc = ADD \/ opc = GT \/ opc = ISZERO) /\
  run_inst_seq (emitted_insts st st') s = OK s' ==>
  s'.vs_memory = s.vs_memory /\ s'.vs_call_ctx = s.vs_call_ctx /\
  s'.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def] >>
  gvs[Once step_inst_base_def, mk_inst_def] >>
  gvs[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def]
QED

Theorem abi_decode_seq_compose[local]:
  st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 /\
  st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2 /\
  run_inst_seq (emitted_insts st st1) s = OK s1 /\
  run_inst_seq (emitted_insts st1 st2) s1 = OK s2 ==>
  run_inst_seq (emitted_insts st st2) s = OK s2 /\
  st2.cs_current_insts = st.cs_current_insts ++ emitted_insts st st2
Proof
  strip_tac >> drule_all emitted_insts_append >> strip_tac >>
  conj_tac >- metis_tac[run_inst_seq_append] >>
  simp[listTheory.APPEND_ASSOC]
QED

Theorem abi_decode_empty_bounded_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecComplex F []) st = ((),st') /\
  hi <> Lit 0w /\ fresh_vars_wrt st s /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  w2n p <= w2n h ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    s'.vs_memory = s.vs_memory /\ s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_data_section = s.vs_data_section
Proof
  simp[compile_abi_decode_to_buf_def] >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_void ASSERT [ok] c3 = ((),c4)` >>
  rename1 `emit_op ISZERO [oob] c2 = (ok,c3)` >>
  rename1 `emit_op GT [item_end; hi] c1 = (oob,c2)` >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand hi s1 = SOME h` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[WORD_ADD_0, bool_to_word_def] >>
  `1w <> (0w:bytes32)` by simp[] >>
  drule_all emit_void_ASSERT_ok >> strip_tac >>
  imp_res_tac abi_guard_emit_frame >> gvs[] >>
  `s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_data_section = s.vs_data_section /\
   s1.vs_memory = s.vs_memory /\ s2.vs_call_ctx = s.vs_call_ctx /\
   s2.vs_data_section = s.vs_data_section /\ s2.vs_memory = s.vs_memory /\
   s3.vs_data_section = s.vs_data_section` by metis_tac[] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  drule_all abi_decode_seq_compose >> strip_tac >>
  drule_all abi_decode_seq_compose >> strip_tac >>
  drule_all abi_decode_seq_compose >> strip_tac >>
  qexists_tac `s3` >> simp[] >> metis_tac[]
QED

Theorem abi_decode_empty_bounded_fragment:
  compile_abi_decode_to_buf dst src opc hi (DecComplex F []) st = ((),st') /\
  hi <> Lit 0w ==>
  frag_exec ctx st st'
    (\s. s = s0 /\ fresh_vars_wrt st s /\
         eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
         w2n p <= w2n h)
    (\s'. s'.vs_memory = s0.vs_memory /\
          s'.vs_call_ctx = s0.vs_call_ctx /\
          s'.vs_data_section = s0.vs_data_section)
    (K F)
Proof
  strip_tac >> irule frag_exec_run_inst_seq >> conj_tac
  >- (rpt strip_tac >> disj1_tac >> gvs[] >>
      drule_all abi_decode_empty_bounded_sequence >> strip_tac >> gvs[]) >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def,
      rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def]
QED

(* Proof-integrity check for this theory only. Unrelated existing admissions in
   ancestors (including compile_abi_decode_static_correct) are not used. *)
