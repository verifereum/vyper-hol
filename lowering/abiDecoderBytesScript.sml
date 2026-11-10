(* Bytes execution: syntactic zero base retains capacity copying; resolved
   memory sources use runtime length and padded last-word zeroing. *)
Theory abiDecoderBytes
Ancestors
  abiDecoderBytesPrefix abiDecoderBytesRuntime abiDecoderBytesPhases abiDecoderRange abiDecoderGuards
  abiDecoderCopy abiDecoderComposition abiDecoderContract abiDecoderBytesBound
  abiDecoderGuard abiCanonicalBytes abiEncoder emitHelperProps exprLoweringProps compileEnv
  emitHelper valueEncoding valueEncodingDefs venomExecSemantics venomState words

Definition abi_decode_bytes_copy_size_def:
  abi_decode_bytes_copy_size n = 32 + 32 * ((n + 31) DIV 32)
End

Theorem abi_decode_bytes_phases:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) =
    do ac <- abi_decode_bytes_position_prefix pos opc base_op hi n;
       if base_op = Lit 0w then
         emit_void (abi_decode_copy_opcode opc)
           [dst; pos; Lit (n2w (abi_decode_bytes_copy_size n))]
       else abi_decode_bytes_runtime_tail dst (FST ac) (SND ac)
    od
Proof
  simp[abi_decode_bytes_prefix_phases, abi_decode_bytes_copy_size_def]
QED

Theorem abi_decode_bytes_sentinel:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst pos opc base_op (Lit 0w) (DecBytestring n) =
    do addr <- compile_abi_dec_addr base_op pos;
       cnt <- abi_decode_count_guard opc addr n;
       if base_op = Lit 0w then
         emit_void (abi_decode_copy_opcode opc)
           [dst; pos; Lit (n2w (abi_decode_bytes_copy_size n))]
       else abi_decode_bytes_runtime_tail dst addr cnt
    od
Proof
  simp[abi_decode_bytes_position_sentinel, abi_decode_bytes_copy_size_def]
QED

Theorem abi_decode_bytes_zero_base_sequence:
  compile_abi_decode_to_buf dst pos opc (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w p : bytes32) s = n2w c /\
  c <= n /\ n < dimword (:256) /\ p < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     p + 32 + c <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d (abi_decode_bytes_copy_size n) t.vs_memory =
      mem_bytes_at p (abi_decode_bytes_copy_size n) (abi_decode_source opc s) /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!t. run_inst_seq (emitted_insts st st') s = OK t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[abi_decode_bytes_position_allocation_frame] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gnvs[] >> PairCases_on `ac` >>
  drule abi_decode_bytes_position_prefix_sequence >>
  disch_then (qspecl_then [`s`, `p`, `c`, `0`] mp_tac) >>
  (impl_tac >- simp[eval_operand_def]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  `eval_operand pos prepared = SOME (n2w p) /\
   eval_operand dst prepared = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit (n2w (abi_decode_bytes_copy_size n))) prepared =
    SOME (n2w (abi_decode_bytes_copy_size n))` by simp[eval_operand_def] >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready st') prepared = OK t` >>
  `fresh_vars_wrt st' t` by (drule_all abi_decode_copy_fresh >> simp[]) >>
  drule inst_extends_emit_void >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[] >>
  qexists_tac `t` >>
  gvs[w2n_n2w, abi_decode_copy_bytes_def, mem_bytes_at_def,
      abi_decode_source_def, abi_decode_frame_def] >> metis_tac[]
QED

Theorem abi_decode_bytes_memory_sequence:
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ base_op <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w (b+p) : bytes32) s = n2w c /\
  c <= n /\ n < dimword (:256) /\ c+31 < dimword (:256) /\
  b+p < dimword (:256) /\ d+abi_decode_bytes_copy_size n < dimword (:256) /\
  (b+p+32+c <= d \/ d+abi_decode_bytes_copy_size n <= b+p) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     p+32+c <= h /\ h < dimword (:256)) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
    mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
      REPLICATE (32*((c+31) DIV 32)-c) 0w /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!t. run_inst_seq (emitted_insts st st') s = OK t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[abi_decode_bytes_position_allocation_frame] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gnvs[] >> PairCases_on `ac` >> gnvs[] >>
  drule abi_decode_bytes_position_prefix_sequence >>
  disch_then (qspecl_then [`s`, `p`, `c`, `b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  `eval_operand dst prepared = SOME (n2w d)` by metis_tac[] >>
  `d+(32+32*((n+31) DIV 32)) < dimword (:256) /\
   (b+p+32+c <= d \/ d+(32+32*((n+31) DIV 32)) <= b+p)` by
    (simp[GSYM abi_decode_bytes_copy_size_def] >> decide_tac) >>
  drule abi_decode_bytes_runtime_tail_memory >>
  disch_then (qspec_then `prepared` mp_tac) >>
  disch_then (qspecl_then [`n`, `d`, `c`, `b+p`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready st') prepared = OK t` >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [abi_decode_bytes_copy_size_def] >>
  gvs[abi_decode_frame_def] >> metis_tac[]
QED

Theorem abi_decode_bytes_sequence:
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w (b+p) : bytes32) s = n2w c /\ c <= n /\
  n < dimword (:256) /\ p < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (base_op <> Lit 0w ==>
    c+31 < dimword (:256) /\ b+p < dimword (:256) /\
    d+abi_decode_bytes_copy_size n < dimword (:256) /\
    (b+p+32+c <= d \/ d+abi_decode_bytes_copy_size n <= b+p)) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     p+32+c <= h /\ h < dimword (:256)) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (if base_op = Lit 0w then
       mem_bytes_at d (abi_decode_bytes_copy_size n) t.vs_memory =
         mem_bytes_at p (abi_decode_bytes_copy_size n) (abi_decode_source opc s)
     else
       mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
       mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
         REPLICATE (32*((c+31) DIV 32)-c) 0w) /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Cases_on `base_op = Lit 0w`
  >- (disch_then (map_every assume_tac o CONJUNCTS) >>
      `n2w b : bytes32 = 0w` by gvs[eval_operand_def] >>
      `abi_decode_load opc (n2w p : bytes32) s = n2w c` by
        gvs[GSYM word_add_n2w, WORD_ADD_0] >>
      qpat_x_assum `base_op = Lit 0w` SUBST_ALL_TAC >>
      simp[] >> drule_all abi_decode_bytes_zero_base_sequence >> metis_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `base_op <> Lit 0w ==> _` mp_tac >>
  asm_rewrite_tac[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bytes_memory_sequence >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

(* Literal-zero-base sentinel still supports every original source opcode. *)
Theorem abi_decode_bytes_sentinel_sequence:
  compile_abi_decode_to_buf dst pos opc (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w p : bytes32) s = n2w c /\ c <= n /\
  n < dimword (:256) /\ p < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d (abi_decode_bytes_copy_size n) t.vs_memory =
      mem_bytes_at p (abi_decode_bytes_copy_size n) (abi_decode_source opc s) /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule abi_decode_bytes_zero_base_sequence >>
  simp[] >> qexistsl_tac [`c`, `dst`, `Lit 0w`, `pos`] >> simp[]
QED
