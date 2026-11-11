(* Bounded memory execution of primitive ABI decoding, on arbitrary words. *)
Theory abiDecodeMemPrimitive
Ancestors
  abiDecodeStaticProps entryDecodeProps memSafeRun abiDecoderRange abiDecoderClamp abiDecodeMemRange
  fragExecMem fragGasSeqMem bodyUnopFragMemory freshWrites
  instMemFrontier moduleLoweringProps allocaHistoryFragment
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_clamp_straight[local]:
  straight_fresh (compile_abi_clamp_basetype op clamp)
Proof
  Cases_on `clamp` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  REPEAT (IF_CASES_TAC) >>
  rpt (irule straight_fresh_bind >>
       (reverse conj_tac >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
       gen_tac >> BETA_TAC) >>
  FIRST [irule straight_fresh_emit_void >> simp[fresh_write_op_def],
         irule straight_fresh_return]
QED

Theorem abi_decode_static_mem_ok[local]:
  compile_abi_decode_static src dst MLOAD
    (\v. compile_abi_clamp_basetype v clamp) st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME d /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] st = (v,c1)` >>
  rename1 `compile_abi_clamp_basetype v clamp c1 = ((),c2)` >>
  `step_inst_base (mk_inst st.cs_next_id MLOAD [src]
     [STRING #"%" (toString st.cs_next_var)]) s =
     OK (update_var (STRING #"%" (toString st.cs_next_var)) (mload (w2n p) s) s)` by
    simp[step_MLOAD] >>
  drule_all decode_emit_update_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  mp_tac (Q.INST [`op` |-> `v`] abi_decode_clamp_straight) >>
  simp[straight_fresh_def] >>
  disch_then drule >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++
     (emitted_insts c1 c2 ++ emitted_insts c2 st')` by
    (`emitted_insts c1 st' = emitted_insts c1 c2 ++ emitted_insts c2 st'` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
       (irule emitted_insts_append >> fs[inst_extends_def] >> rfs[]) >> simp[]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD,
           inst_dload_in_section_def]) >>
  gen_tac >> strip_tac >> gvs[] >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[writes_fresh_mem_ok] >>
  rpt strip_tac >> drule_all decode_clamp_frame >>
  Cases_on `abi_clamp_ok clamp (mload (w2n p) s)` >> simp[] >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE, inst_dload_in_section_def] >>
  `eval_operand dst s'' = SOME d` by metis_tac[] >>
  fs[vars_pc_only_def, venom_state_component_equality]
QED

Theorem abi_decode_primitive_mem_ok:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME d /\
  B + pos < dimword (:256) /\
  B + pos + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, comp_bind_def, LET_THM] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  rename1 `compile_abi_dec_addr base_op src st = (addr,c1)` >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK sa` >>
  `straight_fresh (compile_abi_dec_addr base_op src)` by
    (Cases_on `base_op = Lit 0w` >> simp[compile_abi_dec_addr_def] >>
     FIRST [irule straight_fresh_return,
            irule straight_fresh_emit_op >> simp[fresh_write_op_def]]) >>
  fs[straight_fresh_def] >>
  `writes_fresh st (emitted_insts st c1)` by metis_tac[] >>
  `inst_extends c1 st'` by
    (drule dec_straight_decode_static >> simp[is_terminator_def] >>
     simp[dec_straight_def]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[writes_fresh_mem_ok] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  gen_tac >> strip_tac >> gvs[] >>
  irule abi_decode_static_mem_ok >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`clamp`, `d`, `dst`, `n2w (B + pos)`, `addr`] >>
  simp[w2n_n2w] >>
  qpat_x_assum `s' = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
