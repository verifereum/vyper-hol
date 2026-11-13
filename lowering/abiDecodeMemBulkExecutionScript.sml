(* Composition of bounded bulk-array decoding with rejection-aware guards. *)
Theory abiDecodeMemBulkExecution
Ancestors
  abiDecodeMemBulkPrefix abiDecodeMemBulkBody abiDecoderBulk abiDecoderDynarrayBound
  abiDecoderDynarrayPrefix abiDecoderContract abiEncoder fragGasPathMem fragGasMode fragExec
  allocaFootprint localPtrsProps emitHelperProps exprLoweringProps compileEnv
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_bulk_bounded_path_mem:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi
    (DecDynArray ei asz msz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ asz = msz /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand hi s = SOME (n2w h) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\ b+h <= s.vs_alloca_next /\
  maxn < dimword (:256) /\ maxn*asz < dimword (:256) /\
  d+32+maxn*msz < dimword (:256) /\ d+32+maxn*msz <= s.vs_alloca_next /\
  (b+h <= d \/ d+32+maxn*msz <= b) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) \/
  (?c t. c <= maxn /\ p+32+c*msz <= h /\
    abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    mem_word_at d t.vs_memory = n2w c /\
    mem_bytes_at (d+32) (c*msz) t.vs_memory =
      mem_bytes_at (b+p+32) (c*msz) s.vs_memory /\
    abi_decode_frame d (32+c*msz) s t /\
    mem_bytes_at b h t.vs_memory = mem_bytes_at b h s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    alloca_history func t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  rename1 `abi_decode_dynarray_position_prefix pos MLOAD base_op hi maxn msz st = (addr,c1)` >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_bulk_body_shape >> strip_tac >>
  `fn_has_code st c1 func /\ fn_has_code c1 st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def, same_blocks_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  mp_tac (Q.INST [`stride` |-> `msz`, `st'` |-> `c1`]
    abi_decode_dynarray_position_prefix_path_mem) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  `eval_operand pos s1 = SOME (n2w p) /\ eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `alloca_inv s1` by (irule alloca_inv_fields >> metis_tac[]) >>
  `c*msz <= maxn*msz` by simp[LE_MULT_RCANCEL] >>
  `abi_decode_load MLOAD (n2w (b+p) : bytes32) s1 = n2w c` by
    gvs[abi_decode_load_def, mload_def] >>
  `b+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
   c*msz < dimword (:256) /\ b+p+32+c*msz <= s1.vs_alloca_next /\
   d+32+c*msz <= s1.vs_alloca_next /\
   (b+p+32+c*msz <= d \/ d+32+c*msz <= b+p)` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`] abi_decode_bulk_body_path_mem) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK t)` by metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `mem_bytes_at b h t.vs_memory = mem_bytes_at b h s.vs_memory` by
    (qpat_assum `abi_decode_frame _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
     simp[] >> first_x_assum irule >> decide_tac) >>
  disj2_tac >> qexistsl_tac [`c`, `t`] >>
  simp[] >> gvs[abi_decode_frame_def] >> gvs[]
QED
