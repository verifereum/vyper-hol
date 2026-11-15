(* Actual frontier checks for the bounded-memory bytes decoder. *)
Theory abiDecodeBytesMem
Ancestors
  abiDecoderBytesRuntime abiDecoderBytesPhases abiDecodePtrBytesTail
  abiDecoderBytesPrefix abiDecodePtrBytesMember abiDecodePtrRead
  abiDecoderBytesBound abiDecoderGuard abiDecoderGuards abiDecoderContract abiEncoder
  abiBoundedBytesExecution
  bodyPtrBopScalarCompile
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq fragExecMem instMemFrontier
  emitHelperProps exprLoweringProps compileEnv emitHelper memSafeRun
  venomState venomExecSemantics venomInst words arithmetic list pred_set

Theorem abi_decode_bytes_runtime_copy_mem_ok:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) /\
  eval_operand lastptr s = SOME (n2w (d+q)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\
  d+q < dimword(:256) /\ d < dimword(:256) /\ a < dimword(:256) /\
  32+c < dimword(:256) /\ fresh_vars_wrt st s /\
  d+q+32 <= s.vs_alloca_next /\ d+32+c <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st c3) s
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st c1) s = OK (mstore (d+q) 0w s)` by
    (qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
       mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     simp[run_inst_seq_mem_ok_last, SRULE [mk_inst_def] below_frontier_MSTORE,
       inst_dload_in_section_other, mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `fresh_vars_wrt c1 (mstore (d+q) 0w s)` by
    (drule_all fresh_vars_wrt_emit_void_ss >> simp[fresh_vars_wrt_mstore]) >>
  `!op. eval_operand op (mstore (d+q) 0w s) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def, mstore_def,
      write_memory_with_expansion_def]) >>
  `eval_operand cnt (mstore (d+q) 0w s) = SOME (n2w c) /\
   eval_operand (Lit 32w) (mstore (d+q) 0w s) = SOME 32w` by
    simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) _ = OK prepared` >>
  `bop_scalar_seq {} {Lit 32w;cnt} (emitted_insts c1 c2)
      (sz INSERT {Lit 32w;cnt})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[Lit 32w;cnt]`] >> simp[]) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `prepared = _` (fn th => once_rewrite_tac[th]) >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a)` by metis_tac[] >>
  `w2n (32w+(n2w c:bytes32)) = 32+c` by
    simp[word_add_n2w] >>
  `run_inst_seq_mem_ok (emitted_insts c2 c3) prepared` by
    (qpat_assum `emit_void MCOPY _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     simp[run_inst_seq_mem_ok_last, SRULE [mk_inst_def] below_frontier_MCOPY,
       inst_dload_in_section_other, mk_inst_def, w2n_n2w] >> metis_tac[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st c3 = emitted_insts st c1 ++
      (emitted_insts c1 c2 ++ emitted_insts c2 c3)` by
    metis_tac[emitted_insts_append, inst_extends_trans, inst_extends_def] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >> simp[] >>
  match_mp_tac run_inst_seq_mem_ok_append >>
  conj_tac >- metis_tac[bop_scalar_seq_mem_ok] >> simp[]
QED



(* Only the count load reads memory; both surrounding guards are scalar. *)
Theorem abi_decode_bytes_prefix_mem_ok:
  abi_decode_bytes_position_prefix pos MLOAD (Var src) hi n st = ((addr,cnt),en) /\
  hi <> Lit 0w /\ fresh_vars_wrt st s /\
  eval_operand pos s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w h) /\ lookup_var src s = SOME b /\
  p+32 <= h /\ w2n b+h < dimword(:256) /\
  w2n b+h <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_assum `abi_decode_bytes_position_prefix _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [abi_decode_bytes_position_prefix_trace]) >>
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [abi_decode_count_guard_trace]) >> strip_tac >>
  rename1 `emit_op MLOAD [addr] addr_st = (cnt,loaded)` >>
  `?A. bop_scalar_seq {} UNIV (emitted_insts st head_st) A /\
     UNIV SUBSET A /\ head IN A` by
    (qpat_assum `abi_decode_bytes_head _ _ _ = _`
       (mp_then Any mp_tac (abi_decode_bytes_head_scalar |>
         Q.INST [`R` |-> `{}:string set`, `A` |-> `UNIV`])) >> simp[]) >>
  `?A. bop_scalar_seq {} UNIV (emitted_insts loaded count_st) A /\
     UNIV SUBSET A` by
    (qpat_assum `abi_decode_le_guard _ _ _ = _`
       (mp_then Any mp_tac (abi_decode_le_guard_scalar |>
         Q.INST [`R` |-> `{}:string set`, `A` |-> `UNIV`])) >> simp[]) >>
  `?A. bop_scalar_seq {} UNIV (emitted_insts count_st en) A /\
     UNIV SUBSET A` by
    (qpat_assum `abi_decode_bytes_payload_guard _ _ _ _ = _`
       (mp_then Any mp_tac (abi_decode_bytes_payload_scalar |>
         Q.INST [`R` |-> `{}:string set`, `A` |-> `UNIV`])) >> simp[]) >>
  `h < dimword(:256)` by decide_tac >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st head_st) s = OK sh` >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `sh.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `sh = s with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `lookup_var src sh = SOME b /\ eval_operand pos sh = SOME (n2w p)` by
    (conj_tac
     >- (qpat_assum `!op w. eval_operand op s = SOME w ==> _`
           (qspecl_then [`Var src`, `b`]
             (irule o SRULE [eval_operand_def])) >> fs[eval_operand_def]) >>
     qpat_assum `!op w. eval_operand op s = SOME w ==> _`
       (qspecl_then [`pos`, `n2w p`] irule) >> fs[]) >>
  `run_inst_seq_mem_ok (emitted_insts head_st loaded) sh` by
    (qpat_assum `compile_abi_dec_addr _ _ _ = _`
       (mp_then Any mp_tac (abi_decode_relative_load_mem_ok |>
         Q.INST [`b` |-> `b`, `p` |-> `p`, `s` |-> `sh`])) >>
     disch_then (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     disch_then irule >> simp[] >> qexists_tac `p` >>
     simp[] >> decide_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_prefix_shape >> strip_tac >>
  imp_res_tac abi_decode_bytes_head_fragment_shape >>
  imp_res_tac abi_decode_le_guard_shape >>
  imp_res_tac abi_decode_bytes_payload_guard_fragment_shape >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends head_st loaded /\ inst_extends loaded en` by
    (fs[compile_abi_dec_addr_def] >> imp_res_tac inst_extends_emit_op >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts st en = emitted_insts st head_st ++
      (emitted_insts head_st loaded ++
       (emitted_insts loaded count_st ++ emitted_insts count_st en))` by
    metis_tac[emitted_insts_append, inst_extends_trans, inst_extends_def] >>
  `!z. run_inst_seq_mem_ok
      (emitted_insts loaded count_st ++ emitted_insts count_st en) z` by
    (gen_tac >> match_mp_tac run_inst_seq_mem_ok_append >>
     conj_tac >> metis_tac[bop_scalar_seq_mem_ok]) >>
  `run_inst_seq_mem_ok (emitted_insts head_st loaded ++
      (emitted_insts loaded count_st ++ emitted_insts count_st en)) sh` by
    (match_mp_tac run_inst_seq_mem_ok_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st head_st ++
      (emitted_insts head_st loaded ++
       (emitted_insts loaded count_st ++ emitted_insts count_st en))) s` by
    (match_mp_tac run_inst_seq_mem_ok_append >>
     conj_tac >- metis_tac[bop_scalar_seq_mem_ok] >> fs[APPEND_ASSOC]) >>
  metis_tac[]
QED

Theorem abi_decode_bytes_prefix_checked_mem_ok[local]:
  abi_decode_bytes_position_prefix pos MLOAD (Var src) hi n st = ((addr,cnt),en) /\
  hi <> Lit 0w /\ fresh_vars_wrt st s /\
  eval_operand pos s = SOME (n2w p) /\ p < dimword(:256) /\
  eval_operand hi s = SOME (n2w h) /\ lookup_var src s = SOME b /\
  w2n b+h < dimword(:256) /\ w2n b+h <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >> Cases_on `p+32 <= h`
  >- (drule_all abi_decode_bytes_prefix_mem_ok >> simp[]) >>
  qpat_assum `abi_decode_bytes_position_prefix _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [abi_decode_bytes_position_prefix_trace]) >> strip_tac >>
  `h < dimword(:256)` by decide_tac >>
  drule_all abi_decode_bytes_head_total >> strip_tac
  >- (rename1 `run_inst_seq (emitted_insts st head_st) s = Abort _ rejected` >>
      `?A. bop_scalar_seq {} UNIV (emitted_insts st head_st) A /\
          UNIV SUBSET A /\ head IN A` by
        (irule (abi_decode_bytes_head_scalar |>
           Q.INST [`R` |-> `{}:string set`, `A` |-> `UNIV`]) >>
         simp[] >> metis_tac[]) >>
      `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      drule_all abi_decode_count_guard_shape >> strip_tac >>
      drule abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
      drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
      `inst_extends head_st en` by
        (fs[compile_abi_dec_addr_def] >>
         metis_tac[inst_extends_emit_op, inst_extends_trans]) >>
      `emitted_insts st en = emitted_insts st head_st ++ emitted_insts head_st en` by
        (irule emitted_insts_append >> fs[inst_extends_def]) >>
      pop_assum SUBST1_TAC >> match_mp_tac run_inst_seq_mem_ok_append >>
      conj_tac >- metis_tac[bop_scalar_seq_mem_ok] >> simp[]) >>
  gvs[w2n_n2w]
QED

Theorem abi_decode_bytes_runtime_pointer_scalar:
  emit_op ADD [cnt;Lit 31w] st = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,c3) /\
  emit_op ADD [dst;rounded] c3 = (lastptr,c4) ==>
  bop_scalar_seq {} UNIV (emitted_insts st c4) UNIV
Proof
  strip_tac >>
  `bop_scalar_seq {} UNIV (emitted_insts st c3) UNIV` by
    (irule (abi_decode_bytes_round_scalar |>
       Q.INST [`R` |-> `{}:string set`, `A` |-> `UNIV`] |>
       SRULE [INSERT_UNIV]) >>
     simp[] >> metis_tac[]) >>
  `bop_scalar_seq {} UNIV (emitted_insts c3 c4) UNIV` by
    (irule (bop_scalar_seq_emit_op |>
       Q.INST [`R` |-> `{}:string set`, `A` |-> `UNIV`] |>
       SRULE [INSERT_UNIV]) >>
     simp[] >> qexistsl_tac [`ADD`, `[dst;rounded]`] >> simp[]) >>
  imp_res_tac inst_extends_emit_op >>
  `emitted_insts st c4 = emitted_insts st c3 ++ emitted_insts c3 c4` by
    (irule emitted_insts_append >>
     metis_tac[inst_extends_trans, inst_extends_def]) >>
  simp[] >> metis_tac[bop_scalar_seq_append]
QED

Theorem abi_decode_bytes_runtime_tail_mem_ok:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),en) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c <= n /\ c+31 < dimword(:256) /\
  a < dimword(:256) /\ d+(32+32*((n+31) DIV 32)) < dimword(:256) /\
  fresh_vars_wrt st s /\
  d+(32+32*((n+31) DIV 32)) <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_runtime_tail_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  qspec_then `c` strip_assume_tac (GEN_ALL abi_decode_bytes_round_bounds) >>
  `32*((c+31) DIV 32)+32 <= 32+32*((n+31) DIV 32)` by
    (irule abi_decode_bytes_round_capacity >> simp[]) >>
  `d+32*((c+31) DIV 32) < dimword(:256) /\ d < dimword(:256) /\
   32+c < dimword(:256) /\ c < dimword(:256)` by decide_tac >>
  drule_all abi_decode_bytes_runtime_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  drule_all abi_decode_bytes_runtime_pointer_scalar >> strip_tac >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `prepared = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a) /\
   eval_operand cnt prepared = SOME (n2w c)` by metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts ready en) prepared` by
    (qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any mp_tac (abi_decode_bytes_runtime_copy_mem_ok |>
         Q.INST [`a` |-> `a`, `c` |-> `c`, `d` |-> `d`,
           `q` |-> `32*((c+31) DIV 32)`])) >>
     disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     disch_then (drule_at (Pat `emit_void MCOPY _ _ = _`)) >>
     disch_then irule >> simp[] >> qexistsl_tac [`a`, `c`, `d`] >>
     simp[] >> decide_tac) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st en = emitted_insts st ready ++ emitted_insts ready en` by
    (irule emitted_insts_append >>
     metis_tac[inst_extends_trans, inst_extends_def]) >>
  pop_assum SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >>
  conj_tac >- metis_tac[bop_scalar_seq_mem_ok] >> simp[]
QED

Theorem abi_decode_bytes_member_checked_mem_ok:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) st = ((),en) /\ hi <> Lit 0w /\
  fresh_vars_wrt st s /\ lookup_var src s = SOME b /\
  lookup_var dst s = SOME d /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  p < dimword(:256) /\ n+31 < dimword(:256) /\
  w2n b+h < dimword(:256) /\ w2n b+h <= s.vs_alloca_next /\
  w2n d+(32+32*((n+31) DIV 32)) < dimword(:256) /\
  w2n d+(32+32*((n+31) DIV 32)) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s

Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `h < dimword(:256) /\ n < dimword(:256)` by decide_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_prefix_phases,
    abi_decode_source_opcode_def, comp_bind_def, operand_distinct, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> Cases_on `ac` >> gvs[] >>
  rename1 `abi_decode_bytes_position_prefix _ _ _ _ _ st = ((addr,cnt),ready)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_prefix_shape >> strip_tac >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  `emitted_insts st en = emitted_insts st ready ++ emitted_insts ready en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st ready) s` by
    (mp_tac (abi_decode_bytes_prefix_checked_mem_ok |>
       Q.INST [`st` |-> `st`, `en` |-> `ready`, `pos` |-> `pos`,
         `hi` |-> `hi`, `n` |-> `n`, `src` |-> `src`, `addr` |-> `addr`,
         `cnt` |-> `cnt`, `s` |-> `s`, `p` |-> `p`, `h` |-> `h`, `b` |-> `b`]) >>
     (impl_tac >- simp[]) >> simp[]) >>
  mp_tac (abi_decode_bytes_position_prefix_total |>
    Q.INST [`b` |-> `source_offset`] |>
    Q.INST [`source_offset` |-> `w2n (b:bytes32)`, `pos` |-> `pos`,
      `opc` |-> `MLOAD`, `base_op` |-> `Var src`, `hi` |-> `hi`,
      `n` |-> `n`, `st` |-> `st`, `st'` |-> `ready`, `addr` |-> `addr`,
      `cnt` |-> `cnt`, `s` |-> `s`, `p` |-> `p`, `h` |-> `h`]) >>
  (impl_tac >- simp[eval_operand_def]) >> strip_tac
  >- (qpat_assum `emitted_insts st en = _` SUBST1_TAC >>
      match_mp_tac run_inst_seq_mem_ok_append >> simp[]) >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
      (emitted_insts st ready)` by fs[EVERY_MEM] >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (drule_all abi_decode_nonallocating_sequence_frame >> simp[]) >>
  `eval_operand (Var dst) prepared = SOME (n2w (w2n d))` by
    (simp[] >> qpat_assum `!op w. eval_operand op s = SOME w ==> _`
       (qspecl_then [`Var dst`, `d`] irule) >> fs[eval_operand_def]) >>
  `c+31 < dimword(:256) /\ w2n b+p < dimword(:256)` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts ready en) prepared` by
    (mp_tac (abi_decode_bytes_runtime_tail_mem_ok |>
       Q.INST [`d` |-> `destination_offset`, `dst` |-> `destination_operand`] |>
       Q.INST [`destination_operand` |-> `Var dst`, `addr` |-> `addr`,
         `cnt` |-> `cnt`, `st` |-> `ready`, `en` |-> `en`, `s` |-> `prepared`,
         `a` |-> `w2n (b:bytes32)+p`, `c` |-> `c`,
         `destination_offset` |-> `w2n (d:bytes32)`, `n` |-> `n`]) >>
     (impl_tac >- (simp[] >> decide_tac)) >> simp[]) >>
  qpat_assum `emitted_insts st en = _` SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >> simp[]
QED

Theorem abi_decode_bytes_member_mem_ok:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) st = ((),en) /\ hi <> Lit 0w /\
  fresh_vars_wrt st s /\ lookup_var src s = SOME b /\
  lookup_var dst s = SOME d /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  p < dimword(:256) /\ n+31 < dimword(:256) /\
  w2n b+h < dimword(:256) /\ w2n b+h <= s.vs_alloca_next /\
  w2n d+(32+32*((n+31) DIV 32)) < dimword(:256) /\
  w2n d+(32+32*((n+31) DIV 32)) <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts st en) s = OK u ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  metis_tac[abi_decode_bytes_member_checked_mem_ok]
QED
