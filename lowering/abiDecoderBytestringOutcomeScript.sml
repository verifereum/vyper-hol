(* Arbitrary bounded-memory bytestring outcomes. *)
Theory abiDecoderBytestringOutcome
Ancestors
  valueEncodingDefs
  abiDecoderBytes abiDecoderBytesRuntime abiDecoderGuard abiDecoderBytesPhases abiDecoderRange
  abiDecoderGuards abiDecoderContract
  abiDecoderSiteEffect abiDecoderWordOutcome
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding pred_set venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_add_range_iff:
  a < dimword (:256) /\ b < dimword (:256) /\ h < dimword (:256) ==>
  ((a <= w2n ((n2w a:bytes32) + n2w b) /\
    w2n ((n2w a:bytes32) + n2w b) <= h) <=> a+b <= h)
Proof
  strip_tac >> simp[word_add_n2w, w2n_n2w] >>
  Cases_on `a+b < dimword (:256)`
  >- simp[] >>
  `(a+b) MOD dimword (:256) = a+b-dimword (:256)` by
    (irule MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

Theorem abi_decode_bytes_payload_guard_revert:
  abi_decode_bytes_payload_guard head len hi st = ((),st') /\ hi <> Lit 0w /\
  eval_operand head s = SOME (n2w hb) /\ eval_operand len s = SOME (n2w cnt) /\
  eval_operand hi s = SOME (n2w h) /\
  hb < dimword (:256) /\ cnt < dimword (:256) /\ h < dimword (:256) /\
  h < hb+cnt /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_def,
       comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [head;len] st = (e,c1)` >>
  drule_all abiDecoderBytesBoundTheory.abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand head s1 = SOME (n2w hb) /\
   eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  `w2n ((n2w hb:bytes32) + n2w cnt) < hb \/
   h < w2n ((n2w hb:bytes32) + n2w cnt)` by
    (mp_tac (Q.INST [`a` |-> `hb`, `b` |-> `cnt`] abi_decode_add_range_iff) >>
     simp[] >> decide_tac) >>
  `w2n ((n2w hb:bytes32) + n2w cnt) < w2n (n2w hb:bytes32) \/
   w2n (n2w h:bytes32) < w2n ((n2w hb:bytes32) + n2w cnt)` by
    simp[w2n_n2w] >>
  `?t. run_inst_seq (emitted_insts c1 st') s1 = Abort Revert_abort t` by
    (drule abi_decode_range_check_revert >>
     disch_then (qspec_then `s1` mp_tac) >> simp[]) >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac compile_abi_decode_range_check_shape >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  metis_tac[]
QED

Theorem abi_decode_bytes_head_revert:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w pos) /\ eval_operand hi s = SOME (n2w h) /\
  pos < dimword (:256) /\ h < dimword (:256) /\
  h < pos+32 /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [src;Lit 32w] st = (e,c1)` >>
  rename1 `compile_abi_decode_range_check src e hi c1 = ((),st')` >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abiDecoderBytesBoundTheory.abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w pos) /\
   eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  `w2n ((n2w pos:bytes32) + 32w) < pos \/
   h < w2n ((n2w pos:bytes32) + 32w)` by
    (mp_tac (Q.INST [`a` |-> `pos`, `b` |-> `32`] abi_decode_add_range_iff) >>
     simp[dimword_def] >> decide_tac) >>
  `?t. run_inst_seq (emitted_insts c1 st') s1 = Abort Revert_abort t` by
    (drule abi_decode_range_check_revert >>
     disch_then (qspec_then `s1` mp_tac) >> simp[w2n_n2w]) >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac compile_abi_decode_range_check_shape >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >> simp[]
QED

Theorem abi_decode_count_guard_revert:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  abi_decode_load opc p s = n2w cnt /\
  limit < cnt /\ cnt < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op;Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),st')` >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `limit < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c2 st' /\ inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 =
   run_inst_seq (emitted_insts c2 st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c2 st') s2 =
   run_inst_seq (emitted_insts c3 st') s3` by
    (irule run_inst_seq_emit_extend >> simp[]) >> simp[]
QED

Definition abi_bytes_opcode_def:
  abi_bytes_opcode opc <=>
    abi_word_opcode opc \/ opc = LT \/ opc = GT \/ opc = AND \/
    opc = NOT \/ opc = MCOPY
End

Theorem abi_bytes_step_static:
  abi_bytes_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  simp_tac bool_ss [abi_bytes_opcode_def] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac)
  >- (drule_all abi_word_step_static >> simp[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [step_inst_base_def] >> asm_rewrite_tac [venomInstTheory.opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def, mcopy_def, write_memory_with_expansion_def] >>
  simp[venom_state_component_equality]
QED

Theorem abi_bytes_sequence_static:
  !insts s t. EVERY (\i. abi_bytes_opcode i.inst_opcode) insts /\
  run_inst_seq insts s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all abi_bytes_step_static >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  fs[venom_state_component_equality]
QED

Theorem abi_decoder_bytes_opcodes:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w ==>
  EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_position_phases, abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >>
  gvs[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def, compile_abi_dec_addr_def,
      abi_decode_count_guard_def, abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_def,
      abi_decode_bytes_runtime_tail_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_bytes_frame_memory:
  0 < cap /\ abi_decode_frame d cap s t /\
  {a | d <= a /\ a < d+cap} SUBSET writes ==>
  decode_memory_frame writes s t
Proof
  rw[decode_memory_frame_def] >> Cases_on `n = 0` >- simp[mem_bytes_at_def] >>
  `p+n <= d \/ d+cap <= p` suffices_by metis_tac[abi_decode_frame_def] >>
  fs[SUBSET_DEF] >>
  Cases_on `p+n <= d` >- simp[] >> Cases_on `d+cap <= p` >- simp[] >>
  Cases_on `p <= d`
  >- (first_x_assum (qspec_then `d` mp_tac) >>
      first_x_assum (qspec_then `d` mp_tac) >> simp[] >> decide_tac) >>
  first_x_assum (qspec_then `p` mp_tac) >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[] >> decide_tac
QED

Theorem abi_decoder_bytes_success_effect:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand hi s = SOME (n2w h) /\
  abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
  p+32 <= h /\ c <= n /\ p+32+c <= h /\ b+h < dimword (:256) /\
  d+abi_decode_bytes_copy_size n < dimword (:256) /\
  (b+h <= d \/ d+abi_decode_bytes_copy_size n <= b) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  {a | d <= a /\ a < d+abi_decode_bytes_copy_size n} SUBSET writes /\
  d+abi_decode_bytes_copy_size n <= s.vs_alloca_next ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
    mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
      REPLICATE (32*((c+31) DIV 32)-c) 0w /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `n <= 32*((n+31) DIV 32)` by metis_tac[abi_decode_bytes_round_bounds] >>
  `n < dimword (:256) /\ c+31 < dimword (:256) /\
   b+p < dimword (:256) /\ h < dimword (:256) /\
   (b+p+32+c <= d \/ d+abi_decode_bytes_copy_size n <= b+p)` by
    (fs[abi_decode_bytes_copy_size_def] >> decide_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_bytes_memory_sequence >>
  disch_then (qspec_then `s` mp_tac) >>
  disch_then (qspecl_then [`p`, `d`, `c`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists `h` >> simp[])) >> strip_tac >>
  drule_all abi_decoder_bytes_opcodes >> strip_tac >>
  drule_all abi_bytes_sequence_static >> strip_tac >>
  `decode_static_frame s t` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp` by fs[venom_state_component_equality] >>
  `decode_site_resources ctx fn t` by metis_tac[decode_site_resources_fields] >>
  `0 < abi_decode_bytes_copy_size n` by simp[abi_decode_bytes_copy_size_def] >>
  `decode_memory_frame writes s t` by
    (drule_all abi_bytes_frame_memory >> simp[]) >>
  `decode_upper_frame s t` by
    (match_mp_tac (Q.SPECL [`d`, `abi_decode_bytes_copy_size n`] decode_upper_frame_outside) >>
     reverse conj_tac >- fs[] >>
     qpat_x_assum `abi_decode_frame _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_decode_frame_def]) >>
     rpt strip_tac >>
     qpat_x_assum `!p k. _ ==> mem_bytes_at p k _ = _` irule >> decide_tac) >>
  qexists `t` >> simp[decode_site_effect_def]
QED

Theorem abi_decoder_bytes_revert:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\
  abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
  p < dimword (:256) /\ h < dimword (:256) /\ c < dimword (:256) /\
  n < dimword (:256) /\
  ~(p+32 <= h /\ c <= n /\ p+32+c <= h) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_position_phases, abi_decode_source_opcode_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >> gnvs[] >>
  rename1 `abiDecoderBytesBound$abi_decode_bytes_head pos hi st = (head,c1)` >>
  rename1 `compile_abi_dec_addr base_op pos c1 = (addr,c2)` >>
  rename1 `abi_decode_count_guard MLOAD addr n c2 = (cnt,c3)` >>
  rename1 `abiDecoderBytesBound$abi_decode_bytes_payload_guard head cnt hi c3 = ((),c4)` >>
  rename1 `abi_decode_bytes_runtime_tail dst addr cnt c4 = ((),st')` >>
  imp_res_tac abiDecoderBytesBoundTheory.abi_decode_bytes_head_shape >>
  `inst_extends c1 c2` by
    (fs[compile_abi_dec_addr_def] >> metis_tac[inst_extends_emit_op]) >>
  imp_res_tac abi_decode_count_guard_shape >>
  imp_res_tac abiDecoderBytesBoundTheory.abi_decode_bytes_payload_guard_shape >>
  imp_res_tac abi_decode_bytes_runtime_tail_shape >>
  `inst_extends c3 st' /\ inst_extends c2 st' /\ inst_extends c1 st'` by
    metis_tac[inst_extends_trans] >>
  Cases_on `p+32 <= h`
  >- suspend "accepted_head" >>
  `h < p+32` by decide_tac >>
  drule_all abi_decode_bytes_head_revert >> strip_tac >>
  drule_all run_inst_seq_abort_extends >> metis_tac[]
QED

Resume abi_decoder_bytes_revert[accepted_head]:
  qpat_x_assum `EVERY _ _` kall_tac >>
  drule_all abiDecoderBytesBoundTheory.abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_load MLOAD (n2w (b+p):bytes32) s2 = n2w c` by
    (qpat_x_assum `abi_decode_load _ _ s = _` mp_tac >>
     simp[abi_decode_load_def, mload_def]) >>
  Cases_on `c <= n`
  >- suspend "accepted_count" >>
  `n < c` by decide_tac >>
  drule_all abi_decode_count_guard_revert >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = Abort Revert_abort t` >>
  `run_inst_seq (emitted_insts c2 st') s2 = Abort Revert_abort t` by
    (irule run_inst_seq_abort_extends >> simp[] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 =
   run_inst_seq (emitted_insts c2 st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED
Resume abi_decoder_bytes_revert[accepted_count]:
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\
   eval_operand hi s3 = SOME (n2w h)` by metis_tac[] >>
  `p+32 < dimword (:256) /\ h < p+32+c` by decide_tac >>
  drule_all abi_decode_bytes_payload_guard_revert >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = Abort Revert_abort t` >>
  `run_inst_seq (emitted_insts c3 st') s3 = Abort Revert_abort t` by
    (irule run_inst_seq_abort_extends >> simp[] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c2 st') s2 =
   run_inst_seq (emitted_insts c3 st') s3` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 =
   run_inst_seq (emitted_insts c2 st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED
Finalise abi_decoder_bytes_revert

(* Guard characterization uses the actual loaded length, not a canonical
   encoding witness. Rejection supplies a finite sequence execution. *)
Theorem abi_decoder_bytes_outcome:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand hi s = SOME (n2w h) /\
  c = w2n (abi_decode_load MLOAD (n2w (b+p):bytes32) s) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\
  d+abi_decode_bytes_copy_size n < dimword (:256) /\
  (b+h <= d \/ d+abi_decode_bytes_copy_size n <= b) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  {a | d <= a /\ a < d+abi_decode_bytes_copy_size n} SUBSET writes /\
  d+abi_decode_bytes_copy_size n <= s.vs_alloca_next ==>
  ((?t. run_inst_seq (emitted_insts st st') s = OK t) <=>
     p+32 <= h /\ c <= n /\ p+32+c <= h) /\
  (if p+32 <= h /\ c <= n /\ p+32+c <= h then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
      mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
      mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
        REPLICATE (32*((c+31) DIV 32)-c) 0w /\
      (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
      decode_site_effect ctx fn next writes s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
   else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_load MLOAD (n2w (b+p):bytes32) s = n2w c /\
   c < dimword (:256)` by metis_tac[n2w_w2n, w2n_lt] >>
  `n <= 32*((n+31) DIV 32)` by metis_tac[abi_decode_bytes_round_bounds] >>
  `n < dimword (:256) /\ h < dimword (:256)` by
    (fs[abi_decode_bytes_copy_size_def] >> decide_tac) >>
  qpat_x_assum `c = w2n _` kall_tac >>
  Cases_on `p+32 <= h /\ c <= n /\ p+32+c <= h`
  >- (pop_assum strip_assume_tac >>
      drule_all abi_decoder_bytes_success_effect >>
      disch_then (qspec_then `next` strip_assume_tac) >>
      conj_tac >- (simp[] >> qexists `t` >> simp[]) >>
      simp[] >>
      qpat_x_assum `mem_bytes_at d _ _ = _` mp_tac >>
      qpat_x_assum `mem_bytes_at (d+32+c) _ _ = _` mp_tac >>
      simp_tac arith_ss []) >>
  drule_all abi_decoder_bytes_revert >> strip_tac >> simp[]
QED
