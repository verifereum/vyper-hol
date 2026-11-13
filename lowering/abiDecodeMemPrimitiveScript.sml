(* Bounded memory execution of primitive ABI decoding, on arbitrary words. *)
Theory abiDecodeMemPrimitive
Ancestors
  abiDecodeStaticProps entryDecodeProps memSafeRun abiDecoderRange abiDecoderClamp abiDecodeMemRange
  fragExec fragExecMem fragGasSeqMem fragGasSeqAbort fragGasFresh bodyUnopFragMemory freshWrites
  instMemFrontier moduleLoweringProps allocaHistoryFragment loweringStateRelDefs
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

Theorem abi_decode_primitive_mem_ok[local]:
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

Theorem abi_decode_static_shape[local]:
  compile_abi_decode_static src dst MLOAD
    (\v. compile_abi_clamp_basetype v clamp) st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >>
  `dec_straight st st'` by
    (drule dec_straight_decode_static >> simp[is_terminator_def]) >>
  qpat_x_assum `compile_abi_decode_static _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] st = (v,c1)` >>
  rename1 `compile_abi_clamp_basetype v clamp c1 = ((),c2)` >>
  mp_tac (Q.INST [`op` |-> `v`] abi_decode_clamp_straight) >>
  simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++
    (emitted_insts c1 c2 ++ emitted_insts c2 st')` by
    (`emitted_insts c1 st' = emitted_insts c1 c2 ++ emitted_insts c2 st'` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
       (irule emitted_insts_append >> fs[inst_extends_def] >> rfs[]) >> simp[]) >>
  gvs[dec_straight_def, inst_extends_def, is_terminator_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[mk_inst_def] >> metis_tac[]
QED

Theorem abi_decode_primitive_shape[local]:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, comp_bind_def, LET_THM] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  rename1 `compile_abi_dec_addr base_op src st = (addr,c1)` >>
  drule abi_decode_static_shape >> strip_tac >>
  Cases_on `base_op = Lit 0w`
  >- gvs[compile_abi_dec_addr_def, comp_return_def] >>
  gvs[compile_abi_dec_addr_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `inst_extends c1 st'` by simp[inst_extends_def] >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_decode_primitive_sequence[local]:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME d /\
  B + pos < dimword (:256) ==>
  if abi_clamp_ok clamp (mload (B+pos) s) then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only (mstore (w2n d) (mload (B+pos) s) s) t /\
        fresh_vars_wrt st' t /\
        (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
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
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `inst_extends c1 st'` by
    (drule dec_straight_decode_static >> simp[is_terminator_def, dec_straight_def]) >>
  `inst_extends st c1 /\ st.cs_next_var <= c1.cs_next_var` by
    (gvs[inst_extends_def] >> metis_tac[]) >>
  drule_all run_inst_seq_emit_extend >> disch_then SUBST1_TAC >>
  `!id out. step_inst_base (mk_inst id MLOAD [addr] [out]) sa =
      OK (update_var out (mload (B+pos) s) sa)` by
    (drule step_MLOAD >> simp[w2n_n2w, mload_def]) >>
  `eval_operand dst sa = SOME d` by metis_tac[] >>
  drule_all compile_abi_decode_static_run >>
  Cases_on `abi_clamp_ok clamp (mload (B+pos) s)` >> simp[] >> strip_tac >> simp[] >>
  conj_tac
  >- (`vars_pc_only s sa` by
        (qpat_x_assum `sa = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
         simp[vars_pc_only_def, venom_state_component_equality]) >>
      drule decode_mstore_frame >> disch_then (qspecl_then [`w2n d`, `mload (B+pos) s`] assume_tac) >>
      metis_tac[vars_pc_only_trans]) >>
  rpt strip_tac >>
  `eval_operand op sa = SOME w` by metis_tac[] >>
  `!x. op = Var x ==> not_fresh_at c1 x` by
    (simp[not_fresh_at_def] >> gen_tac >> disch_tac >> gen_tac >> disch_tac >>
     irule fresh_vars_wrt_eval_operand >>
     qexistsl_tac [`op`, `sa`, `c1`, `w`] >> simp[]) >>
  drule vars_pc_only_fields >> strip_tac >>
  `sa.vs_labels = s.vs_labels` by
    (qpat_x_assum `sa = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def, mstore_def]
QED

Theorem abi_decode_primitive_path_mem:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME d /\
  B + pos < dimword (:256) /\
  B + pos + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (abi_clamp_ok clamp (mload (B+pos) s) ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
        t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
        vars_pc_only (mstore (w2n d) (mload (B+pos) s) s) t /\
        fresh_vars_wrt st' t /\
        (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
        t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
        alloca_history func t) /\
  (~abi_clamp_ok clamp (mload (B+pos) s) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> drule abi_decode_primitive_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[abi_decode_primitive_mem_ok] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  conj_tac >- suspend "success" >> suspend "reject"
QED

Resume abi_decode_primitive_path_mem[success]:
  strip_tac >> drule_all abi_decode_primitive_sequence >> simp[] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all exec_block_run_inst_seq >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st st' ++ rest`
    by fs[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')` >>
  simp[] >>
  `t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas` by
    (fs[vars_pc_only_def, mstore_def, venom_state_component_equality]) >>
  simp[] >> conj_tac >- gvs[LENGTH_APPEND] >>
  conj_tac >- fs[vars_pc_only_def, venom_state_component_equality] >>
  fs[fresh_vars_wrt_def]
QED

Resume abi_decode_primitive_path_mem[reject]:
  strip_tac >> drule_all abi_decode_primitive_sequence >> simp[] >> strip_tac >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Finalise abi_decode_primitive_path_mem
