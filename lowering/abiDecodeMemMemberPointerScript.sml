Theory abiDecodeMemMemberPointer
Ancestors
  abiDecodeMemBytesGuards abiDecodeMemCountGuard abiDecoderMemberBound
  abiDecoderReentryPointer abiDecoderReservation abiDecoderGuard abiDecoderRange
  entryDecoderHistoryFrame entrySinkExtraction allocaFootprint bodyFieldMemoryProps
  abiDecoderBytesPrefix abiDecoderBytesBound abiDecoderContract
  fragExecMem fragExec fragGasSeqMem fragGasSeqAbort fragGasMode allocaHistoryFragment
  freshWrites bodyUnopFragMemory instMemFrontier memSafeRun
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  loweringStateRelDefs venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_mem_member_shape:
  compile_getelemptr_abi src dyn off MLOAD base_op hi st = (member_op,st') ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  Cases_on `base_op = Lit 0w` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, inst_extends_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
       IS_PREFIX_APPEND]
QED

Theorem abi_decode_mem_ge_rejected:
  abi_decode_ge_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n va < w2n vb /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all emit_op_LT_correct >> strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Theorem abi_decode_mem_member_sentinel_safe[local]:
  compile_getelemptr_abi src T off MLOAD base_op (Lit 0w) st = (member_op,st') /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\ fresh_vars_wrt st s /\
  B + sb + off < dimword (:256) /\
  B + sb + off + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [src;Lit (n2w off)] st = (head,c1)` >>
  rename1 `compile_abi_dec_addr base_op head c1 = (addr,ca)` >>
  rename1 `emit_op MLOAD [addr] ca = (v,c2)` >>
  rename1 `emit_op ADD [src;v] c2 = (member_op,st')` >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand head s1 = SOME (n2w (sb+off)) /\
   eval_operand base_op s1 = SOME (n2w B)` by (gvs[word_add_n2w] >> metis_tac[]) >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 ca) s1 = OK sa` >>
  `straight_fresh (compile_abi_dec_addr base_op head)` by
    (Cases_on `base_op = Lit 0w` >> simp[compile_abi_dec_addr_def] >>
     FIRST [irule straight_fresh_return,
            irule straight_fresh_emit_op >> simp[fresh_write_op_def]]) >>
  fs[straight_fresh_def] >>
  `writes_fresh c1 (emitted_insts c1 ca)` by metis_tac[] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends c1 ca` by simp[inst_extends_def] >>
  `run_inst_seq (emitted_insts st ca) s = OK sa /\ inst_extends st ca` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  suspend "split"
QED

Resume abi_decode_mem_member_sentinel_safe[split]:
  `inst_extends ca st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st ca ++ emitted_insts ca st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- (`emitted_insts st ca = emitted_insts st c1 ++ emitted_insts c1 ca` by
        (irule emitted_insts_append >> fs[inst_extends_def]) >>
      simp[] >> MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
      >- metis_tac[attr_add_prefix_mem_ok] >>
      rpt strip_tac >> metis_tac[writes_fresh_mem_ok]) >>
  gen_tac >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq (emitted_insts st ca) s = OK sa` >>
  `sa.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `sa = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
     `straight_fresh (emit_op ADD [src;Lit (n2w off)])` by
       (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
     `writes_fresh st (emitted_insts st c1)` by fs[straight_fresh_def] >>
     drule_all run_inst_seq_writes_fresh >> strip_tac >>
     qpat_x_assum `s1 = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  imp_res_tac emitted_insts_emit_op >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_def] >>
  conj_tac >- (qpat_x_assum `n2w (off+sb) = _` kall_tac >>
    simp[below_frontier_MLOAD, w2n_n2w]) >>
  Cases_on `step_inst_base (mk_inst ca.cs_next_id MLOAD [addr]
      [STRING #"%" (toString ca.cs_next_var)]) sa` >> simp[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_dload_in_section_def] >>
  gen_tac >> irule below_frontier_no_ranges >> simp[]
QED
Finalise abi_decode_mem_member_sentinel_safe

Theorem abi_decode_mem_ge_straight[local]:
  straight_fresh (abi_decode_ge_guard a b)
Proof
  rewrite_tac[abi_decode_ge_guard_def] >>
  rpt (irule straight_fresh_bind >>
       (reverse conj_tac >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
       gen_tac >> BETA_TAC) >>
  irule straight_fresh_emit_void >> simp[fresh_write_op_def]
QED

Theorem abi_decode_mem_member_safe:
  compile_getelemptr_abi src dyn off MLOAD base_op hi st = (member_op,st') /\
  eval_operand src s = SOME (n2w sb) /\ fresh_vars_wrt st s /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    B + sb + off < dimword (:256) /\
    B + sb + off + 32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `dyn` >> simp_tac bool_ss [] >> strip_tac
  >- (Cases_on `hi = Lit 0w`
      >- (gvs[] >> drule abi_decode_mem_member_sentinel_safe >>
          disch_then irule >> reverse conj_tac >- simp[] >>
          qexistsl_tac [`B`,`sb`] >> simp[]) >>
      qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [abi_decode_bounded_member_phases, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, LET_THM] >>
      pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      rename1 `compile_getelemptr_abi src T off MLOAD base_op (Lit 0w) st = (member_op,mid)` >>
      rename1 `abi_decode_ge_guard member_op src mid = (u,st')` >>
      Cases_on `u` >> gvs[] >>
      drule abi_decode_mem_member_shape >> strip_tac >>
      drule abi_decode_ge_guard_shape >> strip_tac >>
      `emitted_insts st st' = emitted_insts st mid ++ emitted_insts mid st'` by
        (irule emitted_insts_append >> fs[inst_extends_def]) >>
      qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
      MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
      >- (drule abi_decode_mem_member_sentinel_safe >>
          disch_then irule >> reverse conj_tac >- simp[] >>
          qexistsl_tac [`B`,`sb`] >> simp[]) >>
      rpt strip_tac >>
      mp_tac (Q.INST [`a` |-> `member_op`, `b` |-> `src`] abi_decode_mem_ge_straight) >>
      simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
      metis_tac[writes_fresh_mem_ok]) >>
  `straight_fresh (compile_getelemptr_abi src F off MLOAD base_op hi)` by
    (simp[compile_getelemptr_abi_def] >> irule straight_fresh_bind >>
     reverse conj_tac >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
     gen_tac >> BETA_TAC >> irule straight_fresh_return) >>
  fs[straight_fresh_def] >> metis_tac[writes_fresh_mem_ok]
QED

Theorem abi_decode_mem_member_rejected:
  compile_getelemptr_abi src T off MLOAD base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\ fresh_vars_wrt st s /\
  B+sb+off < dimword (:256) /\ sb < dimword (:256) /\
  dimword (:256) <= sb + w2n (mload (B+sb+off) s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_member_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T off MLOAD base_op (Lit 0w) st = (member_op,mid)` >>
  rename1 `abi_decode_ge_guard member_op src mid = (u,st')` >>
  Cases_on `u` >> gvs[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_load MLOAD (n2w (B+(sb+off)) : bytes32) s =
    n2w (w2n (mload (B+sb+off) s))` by
    (`B+(sb+off) < dimword (:256)` by decide_tac >>
     pure_rewrite_tac[abi_decode_load_def] >>
     asm_simp_tac std_ss [w2n_n2w, n2w_w2n, ADD_ASSOC, LESS_MOD]) >>
  drule_all abi_decode_dynamic_member_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK sm` >>
  `eval_operand src sm = SOME (n2w sb)` by metis_tac[] >>
  `w2n (n2w (sb + w2n (mload (B+sb+off) s)) : bytes32) <
   w2n (n2w sb : bytes32)` by
    (simp[w2n_n2w] >>
     `w2n (mload (B+sb+off) s : bytes32) < dimword (:256)` by
       irule w2n_lt >>
     `sb + w2n (mload (B+sb+off) s) < 2 * dimword (:256)` by decide_tac >>
     `sb + w2n (mload (B+sb+off) s) - dimword (:256) < dimword (:256)`
       by decide_tac >>
     mp_tac (Q.INST [`m` |-> `sb + w2n (mload (B+sb+off) s)`,
       `n` |-> `dimword (:256)`, `q` |-> `1`] MOD_SUB) >>
     strip_tac >>
     full_simp_tac std_ss [AC ADD_ASSOC ADD_COMM, LESS_MOD, MULT_CLAUSES,
       ZERO_LT_dimword] >>
     qpat_x_assum `_ ==> _` mp_tac >> (impl_tac >- decide_tac) >>
     asm_simp_tac arith_ss [LESS_MOD] >> decide_tac) >>
  drule_all abi_decode_mem_ge_rejected >> strip_tac >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  `emitted_insts st st' = emitted_insts st mid ++ emitted_insts mid st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[] >> drule run_inst_seq_append >>
  disch_then (pure_rewrite_tac o single) >> simp[] >> metis_tac[]
QED

Theorem abi_decode_mload_member_path_mem:
  compile_getelemptr_abi src dyn off MLOAD base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  sb < dimword (:256) /\ fresh_vars_wrt st s /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+off < dimword (:256) /\ B+sb+off+32 <= s.vs_alloca_next) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((dyn ==> sb + w2n (mload (B+sb+off) s) < dimword (:256)) ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand member_op t = SOME
        (n2w (sb + if dyn then w2n (mload (B+sb+off) s) else off)) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (dyn /\ dimword (:256) <= sb + w2n (mload (B+sb+off) s) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> drule abi_decode_mem_member_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (drule abi_decode_mem_member_safe >> disch_then irule >>
     reverse conj_tac >- simp[] >> qexistsl_tac [`B`,`sb`] >> simp[]) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_mload_member_path_mem[accept]:
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `dyn ==> abi_decode_load MLOAD (n2w (B+(sb+off)) : bytes32) s =
    n2w (w2n (mload (B+sb+off) s))` by
    (strip_tac >> fs[] >>
     `B+(sb+off) < dimword (:256)` by decide_tac >>
     pure_rewrite_tac[abi_decode_load_def] >>
     asm_simp_tac std_ss [w2n_n2w, n2w_w2n, ADD_ASSOC, LESS_MOD]) >>
  drule abi_decoder_member_pointer_sequence >>
  disch_then (qspecl_then [`B`,`sb`,`s`,`w2n (mload (B+sb+off) s)`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_nonallocating_sequence_frame >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[fresh_vars_wrt_def]
QED
Resume abi_decode_mload_member_path_mem[reject]:
  strip_tac >> gvs[] >>
  drule abi_decode_mem_member_rejected >>
  disch_then (qspecl_then [`sb`,`s`,`B`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Finalise abi_decode_mload_member_path_mem
