(* Conditional composite decoder replay: concrete guarded entry phases. *)
Theory extcallDecoderCompositeMemory
Ancestors
  extcallDecoderPreparationMemory extcallDecoderMemberPreparationMemory extcallDecoderHeadBounds
  extcallDecoderMemberSemantics extcallDecoderArraySemantics extcallDecoderStaticSuffix
  extcallDecoderIndexedMember
  extcallDecoderBudgetBounds valueEncodingProps
  typedCopyTuplePtr
  extcallDecoderPrefixMemory extcallDecoderBulkMemory extcallDecoderLoopEdgesMemory
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMemberBound
  abiDecoderMemberSetup abiDecoderMemberCode freshWrites exprSimCalldataSlice
  abiDecoderReentry abiDecoderReentryPointer abiDecoderReservation abiDecoderVarSequence abiDecoderDynamicLoopSetup
  loweringStateRelDefs varsExt abiScratchAddress abiScratchDecoderSubwindow abiEncoderArrayFrame
  abiScratchEffect abiScratchAfterAddress abiScratchDecoderMemberFrames abiEncoderInput
  abiDecoderFrame abiDecoderMemberFrames abiScratchFootprint
  fragGasSeqMem fragGasSeqAbort fragGasMode fragGasPathMem instMemFrontier
  abiDecoderGuard abiDecoderGuards abiDecoderRange abiDecoderBytesBound
  abiEncoder compileEnv emitHelper fragExecMem abiDecoderContract
  emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem extcall_decoder_complex_guard_mem_ok[local]:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) ==>
  run_inst_seq_mem_ok (emitted_insts st fin) s
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem extcall_decoder_complex_guard_reject_run[local]:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand hi s = SOME (n2w H) /\
  sb < dimword(:256) /\ H < dimword(:256) /\ headsz < dimword(:256) /\
  H < sb+headsz /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t
Proof
  strip_tac >> qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w headsz)] st = (endop,c1)` >>
  `eval_operand (Lit (n2w headsz)) s = SOME (n2w headsz)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[word_add_n2w] >>
  `eval_operand src s1 = SOME (n2w sb) /\ eval_operand hi s1 = SOME (n2w H)` by metis_tac[] >>
  `~(w2n (n2w sb : bytes32) <= w2n (n2w (sb+headsz) : bytes32) /\
      w2n (n2w (sb+headsz) : bytes32) <= w2n (n2w H : bytes32))` by
    (mp_tac (Q.INST [`modulus` |-> `dimword(:256)`, `a` |-> `sb`,
       `n` |-> `headsz`, `limit` |-> `H`] slice_bounds_mod) >>
     simp[w2n_n2w] >> decide_tac) >>
  `eval_operand endop s1 = SOME (n2w (sb+headsz))` by simp[ADD_COMM] >>
  drule_all extcall_decoder_range_check_reject_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac compile_abi_decode_range_check_shape >>
  `emitted_insts st fin = emitted_insts st c1 ++ emitted_insts c1 fin` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts c1 fin` assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem extcall_decoder_complex_guard_reject:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand hi s = SOME (n2w H) /\
  sb < dimword(:256) /\ H < dimword(:256) /\ headsz < dimword(:256) /\
  H < sb+headsz /\ abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?k t. gas_path_mem ctx fn s k (Abort Revert_abort t)
Proof
  strip_tac >>
  `(!z. src = Var z ==> not_fresh_at st z) /\
   (!z. hi = Var z ==> not_fresh_at st z)` by
    (Cases_on `src` >> Cases_on `hi` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand src (drop_fresh st s) = SOME (n2w sb) /\
   eval_operand hi (drop_fresh st s) = SOME (n2w H)` by
    asm_simp_tac bool_ss [eval_operand_drop_fresh] >>
  `fresh_vars_wrt st (drop_fresh st s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all extcall_decoder_complex_guard_reject_run >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by gvs[EVERY_CONJ, EVERY_MEM] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts st fin)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >>
     Cases_on `i.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def, is_ext_call_op_def]) >>
  `vars_ext (drop_fresh st s) s` by simp[vars_ext_drop_fresh] >>
  drule_all run_inst_seq_vars_ext >>
  simp[vars_ext_result_def] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st fin) s` by
    metis_tac[extcall_decoder_complex_guard_mem_ok] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[gas_marked_path_def] >> metis_tac[]
QED

Theorem extcall_decoder_complex_guard_success:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand hi s = SOME (n2w H) /\
  sb+headsz <= H /\ H < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  fin.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?k t. gas_path_mem ctx fn s k
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st fin))) /\
    fresh_vars_wrt limit t /\ abi_decoder_address_frame st.cs_next_var s t /\
    t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  Q.SUBGOAL_THEN `hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    sb+headsz <= hb /\ hb < dimword(:256)` assume_tac >- metis_tac[] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by gvs[EVERY_CONJ, EVERY_MEM] >>
  `run_inst_seq_mem_ok (emitted_insts st fin) s` by
    metis_tac[extcall_decoder_complex_guard_mem_ok] >>
  `actual.vs_current_bb = s.vs_current_bb` by
    (drule_all fragExecTheory.exec_block_run_inst_seq >> simp[]) >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st fin))`,
    `actual`] >> simp[ADD_COMM]
QED

Theorem extcall_decoder_member_pointer_wrap_reentry[local]:
  compile_getelemptr_abi src T ao MLOAD base_op hi st = (member_ptr,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
  sb < dimword(:256) /\ off < dimword(:256) /\ dimword(:256) <= sb+off /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t /\
      inst_extends st fin
Proof
  strip_tac >>
  `(!z. src = Var z ==> not_fresh_at st z) /\
   (!z. base_op = Var z ==> not_fresh_at st z)` by
    (Cases_on `src` >> Cases_on `base_op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand src (drop_fresh st s) = SOME (n2w sb) /\
   eval_operand base_op (drop_fresh st s) = SOME (n2w B)` by
    asm_simp_tac bool_ss [eval_operand_drop_fresh] >>
  `abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) (drop_fresh st s) = n2w off` by
    gvs[abi_decode_load_def, mload_def, drop_fresh_def] >>
  `fresh_vars_wrt st (drop_fresh st s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all extcall_decoder_member_pointer_wrap_run >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`is_dyn` |-> `T`] abi_decode_member_pointer_allocation_shape)) >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts st fin)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!ii. MEM ii _ ==> ~is_terminator _ /\ _`
       (qspec_then `i` mp_tac) >>
     qpat_x_assum `!ii. MEM ii _ ==> abi_decoder_reentry_opcode _`
       (qspec_then `i` mp_tac) >>
     Cases_on `i.inst_opcode` >>
     gvs[abi_decoder_reentry_opcode_def, is_ext_call_op_def, is_terminator_def]) >>
  `vars_ext (drop_fresh st s) s` by simp[vars_ext_drop_fresh] >>
  drule_all run_inst_seq_vars_ext >> simp[vars_ext_result_def] >> metis_tac[]
QED

Theorem extcall_decoder_member_setup_wrap_reentry_run[local]:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
  sb < dimword(:256) /\ off < dimword(:256) /\ dimword(:256) <= sb+off /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t
Proof
  strip_tac >> qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_member_setup_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T ao MLOAD base_op hi st = (mp,mid)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] mid = (dp,last)` >>
  `abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off` by simp[ADD_COMM] >>
  `dimword(:256) <= sb+off` by simp[ADD_COMM] >>
  drule_all extcall_decoder_member_pointer_wrap_reentry >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `!u. run_inst_seq (emitted_insts st mid) s <> OK u` by simp[] >>
  drule_all run_inst_seq_emit_extend_err >> metis_tac[]
QED

Theorem extcall_decoder_member_setup_wrap_reentry:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
  sb < dimword(:256) /\ off < dimword(:256) /\ dimword(:256) <= sb+off /\
  B+sb+ao < dimword(:256) /\ B+sb+ao+32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n t. gas_path_mem ctx func s n (Abort Revert_abort t)
Proof
  strip_tac >> drule_all extcall_decoder_member_setup_wrap_reentry_run >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by fs[EVERY_CONJ] >>
  `run_inst_seq_mem_ok (emitted_insts st fin) s` by
    (irule extcall_decoder_member_setup_mem_ok >> metis_tac[]) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[gas_marked_path_def] >> metis_tac[]
QED

(* No semantic validity is needed to select the member pointer path. *)
Theorem extcall_decoder_member_setup_paths[local]:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword(:256) /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
    off < dimword(:256) /\ B+sb+ao < dimword(:256) /\
    B+sb+ao+32 <= s.vs_alloca_next) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  fin.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?k r. gas_path_mem ctx func s k r /\
    ((?t. r = OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st fin)) /\
      (dyn ==> sb+off < dimword(:256)) /\
      eval_operand (FST ops) t = SOME (n2w (sb + if dyn then off else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
      abi_decoder_operand_live fin.cs_next_var (FST ops) /\
      abi_decoder_operand_live fin.cs_next_var (SND ops) /\
      fresh_vars_wrt limit t /\ abi_decoder_address_frame st.cs_next_var s t /\
      inst_extends st fin /\ t.vs_current_bb = s.vs_current_bb) \/
     (?t. r = Abort Revert_abort t /\ dyn /\ dimword(:256) <= sb+off))
Proof
  strip_tac >> Cases_on `dyn /\ dimword(:256) <= sb+off`
  >- (gvs[] >> `sb < dimword(:256)` by decide_tac >>
      `B+sb+ao < dimword(:256) /\ B+sb+ao+32 <= s.vs_alloca_next /\
       dimword(:256) <= sb+off` by decide_tac >>
      `abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s = n2w off` by simp[ADD_COMM] >>
      drule_all extcall_decoder_member_setup_wrap_reentry >>
      disch_then (qspec_then `ctx` strip_assume_tac) >> qexistsl_tac [`n`, `Abort Revert_abort t`] >> simp[]) >>
  `dyn ==> sb+off < dimword(:256)` by metis_tac[NOT_LESS] >>
  `dyn ==> eval_operand base_op s = SOME (n2w B) /\
    abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s = n2w off /\
    sb+off < dimword(:256) /\ B+sb+ao < dimword(:256) /\
    B+sb+ao+32 <= s.vs_alloca_next` by metis_tac[] >>
  drule_all extcall_decoder_member_setup_success >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st fin))`,
    `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st fin))`] >>
  conj_tac >- simp[] >> disj1_tac >> qexists_tac `t` >> simp[]
QED

(* The complete recursive Entry at a prepared member.  Physical subwindows
   and executed head guards suffice; no validity of the child is assumed. *)
Theorem extcall_decoder_member_entry[local]:
  di = type_to_abi_dec_info sf ce ty /\ abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi di mid = ((),fin) /\
  fn_has_code mid fin func /\ fn_inst_ids_distinct func /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  hi <> Lit 0w /\ base_op <> Lit 0w /\
  H <= P /\ B+P < dimword(:256) /\ B+P <= s.vs_alloca_next /\
  sb+ao <= H /\
  (dec_info_needs_offset di ==> sb+off < dimword(:256)) /\
  (!clamp. di = DecPrimWord clamp ==> sb+ao+32 <= H) /\
  vo+type_memory_bytes ce ty <= outsz /\
  d+outsz < dimword(:256) /\ d+outsz <= s.vs_alloca_next /\
  LENGTH snap = P /\ mem_bytes_at B P s.vs_memory = snap /\
  abi_footprint_disjoint B P ((d,outsz)::abi_decoder_child_scratch
    (abi_decoder_ids first last) b cap s) /\
  abi_footprint_disjoint d outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  (!id p n. FLOOKUP s.vs_allocas id = SOME (p,n) ==> p+n <= s.vs_alloca_next) /\
  abi_decoder_budget first last b cap s /\ first <= abi_decoder_entry_floor mid /\
  fin.cs_next_id <= last /\ fin.cs_next_var <= limit.cs_next_var /\
  b+cap < dimword(:256) /\ s.vs_alloca_next <= b+cap /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st.cs_next_var <= mid.cs_next_var /\
  abi_decoder_operand_live mid.cs_next_var (FST ops) /\
  abi_decoder_operand_live mid.cs_next_var (SND ops) /\
  abi_decoder_address_frame st.cs_next_var s t /\ fresh_vars_wrt limit t /\
  eval_operand (FST ops) t = SOME (n2w (sb + if dec_info_needs_offset di then off else ao)) /\
  eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
  ~s.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
  t.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  di = type_to_abi_dec_info sf ce ty /\ abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi di mid = ((),fin) /\
  fn_has_code mid fin func /\ fn_inst_ids_distinct func /\
  eval_operand base_op t = SOME (n2w B) /\
  eval_operand (FST ops) t = SOME (n2w (sb + if dec_info_needs_offset di then off else ao)) /\
  eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
  eval_operand hi t = SOME (n2w H) /\ hi <> Lit 0w /\ base_op <> Lit 0w /\
  H <= P /\ B+P < dimword(:256) /\ B+P <= t.vs_alloca_next /\
  sb + (if dec_info_needs_offset di then off else ao) < dimword(:256) /\
  d+vo+type_memory_bytes ce ty < dimword(:256) /\
  d+vo+type_memory_bytes ce ty <= t.vs_alloca_next /\
  LENGTH snap = P /\ mem_bytes_at B P t.vs_memory = snap /\
  (!clamp. di = DecPrimWord clamp ==>
    sb + (if dec_info_needs_offset di then off else ao) + 32 <= H) /\
  abi_footprint_disjoint B P ((d+vo,type_memory_bytes ce ty)::abi_decoder_child_scratch
    (abi_decoder_ids first last) b cap t) /\
  abi_footprint_disjoint (d+vo) (type_memory_bytes ce ty)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap t) /\
  (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==> p+n <= t.vs_alloca_next) /\
  abi_decoder_budget first last b cap t /\ first <= abi_decoder_entry_floor mid /\
  fin.cs_next_id <= last /\ fin.cs_next_var <= limit.cs_next_var /\
  fresh_vars_wrt limit t /\ b+cap < dimword(:256) /\ t.vs_alloca_next <= b+cap /\
  EVERY (abi_decoder_operand_live mid.cs_next_var) [FST ops; SND ops; base_op; hi] /\
  ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
  t.vs_inst_idx = LENGTH mid.cs_current_insts
Proof
  strip_tac >>
  drule_all abi_scratch_address >> strip_tac >>
  `abi_footprint_disjoint B P ((d+vo,type_memory_bytes ce ty)::
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_scratch_disjoint_output_subwindow >> qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  `abi_footprint_disjoint (d+vo) (type_memory_bytes ce ty)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  `abi_decoder_operand_live mid.cs_next_var base_op /\
   abi_decoder_operand_live mid.cs_next_var hi` by
    metis_tac[abi_decoder_operand_live_mono] >>
  qpat_x_assum `abi_decoder_address_frame _ _ _` mp_tac >>
  simp[abi_decoder_address_frame_def] >> strip_tac >>
  simp[] >> rpt conj_tac
  >- (Cases_on `dec_info_needs_offset di` >> gvs[] >> decide_tac)
  >- (rpt strip_tac >> gvs[dec_info_needs_offset_def])
  >- (rpt strip_tac >> qpat_x_assum `!id p n. FLOOKUP _ id = SOME (p,n) ==> _` drule >> decide_tac) >>
  first_x_assum (qspecl_then [`abi_decoder_ids first last`, `[]:(num # num) list`] strip_assume_tac) >> simp[]
QED

(* An indexed discovered prefix survives exactly the next child's footprint.
   The earlier cells lie before its output, even for zero-sized members. *)
Theorem extcall_decoder_member_prefix_advance[local]:
  LENGTH ps = j /\ j < LENGTH tvs /\
  (!i. i < j ==> observed i (EL i ps) /\
    value_has_type (EL i tvs) (EL i ps) /\
    val_in_memory (EL i tvs) (EL i ps)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) s.vs_memory) /\
  observed j v /\ value_has_type (EL j tvs) v /\
  val_in_memory (EL j tvs) v
    (d + SUM (MAP type_memory_size (TAKE j tvs))) t.vs_memory /\
  abi_scratch_effect first last lo hi next limit
    (d + SUM (MAP type_memory_size (TAKE j tvs))) (type_memory_size (EL j tvs)) b cap s t /\
  first <= lo /\ hi <= last /\
  abi_footprint_disjoint d (SUM (MAP type_memory_size tvs))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  abi_footprint_disjoint B P
    ((d,SUM (MAP type_memory_size tvs))::
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  mem_bytes_at B P s.vs_memory = snap ==>
  LENGTH (ps ++ [v]) = SUC j /\ mem_bytes_at B P t.vs_memory = snap /\
  (!i. i < SUC j ==> observed i (EL i (ps ++ [v])) /\
    value_has_type (EL i tvs) (EL i (ps ++ [v])) /\
    val_in_memory (EL i tvs) (EL i (ps ++ [v]))
      (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory)
Proof
  strip_tac >> drule_all abi_scratch_effect_frame >> strip_tac >>
  `SUM (MAP type_memory_size (TAKE j tvs)) + type_memory_size (EL j tvs) <=
    SUM (MAP type_memory_size tvs)` by
    (irule abi_encoder_prefix_sum_bound >> simp[]) >>
  `abi_footprint_disjoint B P
    ((d + SUM (MAP type_memory_size (TAKE j tvs)),type_memory_size (EL j tvs))::
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_scratch_disjoint_output_subwindow >>
     qexistsl_tac [`d`, `SUM (MAP type_memory_size tvs)`] >> simp[]) >>
  drule_all abi_decode_footprint_frame_slice >> strip_tac >> simp[] >>
  qx_gen_tac `i` >> disch_tac >> Cases_on `i = j`
  >- gvs[EL_APPEND2] >>
  `i < j` by decide_tac >> simp[EL_APPEND1] >>
  `SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs) <=
    SUM (MAP type_memory_size (TAKE j tvs))` by
    (qspecl_then [`type_memory_size`, `TAKE j tvs`, `i`] mp_tac abi_encoder_prefix_sum_bound >>
     simp[LENGTH_TAKE, EL_TAKE, TAKE_TAKE] >> decide_tac) >>
  `abi_footprint_disjoint (d + SUM (MAP type_memory_size (TAKE i tvs)))
    (type_memory_size (EL i tvs))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `SUM (MAP type_memory_size tvs)`] >> simp[] >> decide_tac) >>
  `abi_footprint_disjoint (d + SUM (MAP type_memory_size (TAKE i tvs)))
    (type_memory_size (EL i tvs))
    ((d + SUM (MAP type_memory_size (TAKE j tvs)),type_memory_size (EL j tvs))::
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (simp[abi_scratch_disjoint_cons] >> decide_tac) >>
  irule abi_decoder_value_frame >>
  conj_tac >- simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `s` >> simp[]
QED

(* Guarded parent windows bound the next physical head load independently of
   whether any remaining input decodes successfully. *)
Theorem extcall_decoder_member_index_windows[local]:
  ao = (\j. SUM (MAP abi_member_head_size
    (MAP (vyper_to_abi_type env) (TAKE j tys)))) /\
  mo = (\j. SUM (MAP (type_memory_bytes ce) (TAKE j tys))) /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ j < LENGTH tys /\
  sb+ao (LENGTH tys) <= H /\ H <= P /\
  B+P < dimword(:256) /\ B+P <= s.vs_alloca_next ==>
  abi_decoder_coherent ce env sf (EL j tys) (EL j tvs) /\
  ao j + abi_member_head_size (vyper_to_abi_type env (EL j tys)) <= ao (LENGTH tys) /\
  mo j + type_memory_bytes ce (EL j tys) <= mo (LENGTH tys) /\
  (dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys)) ==>
    B+sb+ao j < dimword(:256) /\ B+sb+ao j+32 <= s.vs_alloca_next) /\
  (!clamp. type_to_abi_dec_info sf ce (EL j tys) = DecPrimWord clamp ==>
    sb+ao j+32 <= H)
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf (EL j tys) (EL j tvs)` by
    metis_tac[LIST_REL_EL_EQN] >>
  `ao j + abi_member_head_size (vyper_to_abi_type env (EL j tys)) <= ao (LENGTH tys)` by
    (mp_tac (Q.ISPEC `(abi_member_head_size o vyper_to_abi_type env):type -> num`
       abi_encoder_prefix_sum_bound) >>
     disch_then (qspecl_then [`tys`, `j`] mp_tac) >>
     simp[MAP_MAP_o, combinTheory.o_DEF]) >>
  `mo j + type_memory_bytes ce (EL j tys) <= mo (LENGTH tys)` by
    (mp_tac (Q.ISPEC `(type_memory_bytes ce):type -> num`
       abi_encoder_prefix_sum_bound) >>
     disch_then (qspecl_then [`tys`, `j`] mp_tac) >> simp[]) >>
  qpat_x_assum `ao = _` kall_tac >> qpat_x_assum `mo = _` kall_tac >>
  simp[] >> conj_tac
  >- (strip_tac >>
      `is_dynamic (vyper_to_abi_type env (EL j tys))` by
        metis_tac[abiDecoderOffsetTheory.abi_decoder_needs_offset_iff,
          abiDecoderDynamicTheory.abi_decoder_coherent_dynamic] >>
      fs[abiDecodeRangesTheory.abi_member_head_size_def] >> decide_tac) >>
  rpt strip_tac >>
  drule_all abiDecoderWordTypedTheory.abi_decoder_primitive_cases >> strip_tac >>
  drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
  simp[abiDecoderCoherenceTheory.abi_decoder_header_def] >> strip_tac >>
  fs[abiDecodeRangesTheory.abi_member_head_size_def] >> decide_tac
QED

(* Fixed parent windows and descended maps; only the indexed immediate member
   pairs may use the recursive hypothesis.  Let-bound notation introduces no
   theory constants and expands to the actual Entry and discovered invariant. *)
Theorem extcall_decoder_remaining_members[local]:
  let ao = \j. SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) (TAKE j tys)));
      mo = \j. SUM (MAP (type_memory_bytes ce) (TAKE j tys));
      raw = DROP sb (TAKE H snap);
      good = \ty tv child_sb v.
        child_sb <= H /\
        vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP child_sb (TAKE H snap)) /\
        (is_dynamic (vyper_to_abi_type env ty) \/
          static_length (vyper_to_abi_type env ty) <= LENGTH (DROP child_sb (TAKE H snap))) /\
        abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
          (DROP child_sb (TAKE H snap))) = SOME v /\ value_has_type tv v;
      child_entry = \ty tv dst src a z u child_sb child_d.
        abi_decoder_coherent ce env sf ty tv /\
        compile_abi_decode_to_buf dst src MLOAD base_op hi
          (type_to_abi_dec_info sf ce ty) a = ((),z) /\
        fn_has_code a z func /\ fn_inst_ids_distinct func /\
        eval_operand base_op u = SOME (n2w B) /\
        eval_operand src u = SOME (n2w child_sb) /\
        eval_operand dst u = SOME (n2w child_d) /\ eval_operand hi u = SOME (n2w H) /\
        hi <> Lit 0w /\ base_op <> Lit 0w /\
        H <= P /\ B+P < dimword(:256) /\ B+P <= u.vs_alloca_next /\
        child_sb < dimword(:256) /\ child_d+type_memory_bytes ce ty < dimword(:256) /\
        child_d+type_memory_bytes ce ty <= u.vs_alloca_next /\
        LENGTH snap = P /\ mem_bytes_at B P u.vs_memory = snap /\
        (!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> child_sb+32 <= H) /\
        abi_footprint_disjoint B P ((child_d,type_memory_bytes ce ty)::
          abi_decoder_child_scratch (abi_decoder_ids first last) b cap u) /\
        abi_footprint_disjoint child_d (type_memory_bytes ce ty)
          (abi_decoder_child_scratch (abi_decoder_ids first last) b cap u) /\
        (!id p n. FLOOKUP u.vs_allocas id = SOME (p,n) ==> p+n <= u.vs_alloca_next) /\
        abi_decoder_budget first last b cap u /\ first <= abi_decoder_entry_floor a /\
        z.cs_next_id <= last /\ z.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit u /\
        b+cap < dimword(:256) /\ u.vs_alloca_next <= b+cap /\
        EVERY (abi_decoder_operand_live a.cs_next_var) [src;dst;base_op;hi] /\
        ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
        u.vs_inst_idx = LENGTH a.cs_current_insts;
      observed = \i v.
        let at = vyper_to_abi_type env (EL i tys);
            tail = DROP (ao i) raw;
            xs = if is_dynamic at then DROP (abi_head_word tail) raw else tail in
        vyper_decode_valid_enc at xs /\ (is_dynamic at \/ static_length at <= LENGTH xs) /\
        abi_to_vyper env (EL i tys) (dec at xs) = SOME v;
      inv = \j ps c u.
        LENGTH ps = j /\
        (!i. i < j ==> observed i (EL i ps) /\ value_has_type (EL i tvs) (EL i ps) /\
          val_in_memory (EL i tvs) (EL i ps) (d+mo i) u.vs_memory) /\
        mem_bytes_at B P u.vs_memory = snap /\
        (!id p n. FLOOKUP u.vs_allocas id = SOME (p,n) ==> p+n <= u.vs_alloca_next) /\
        abi_decoder_budget first last b cap u /\ first <= abi_decoder_entry_floor c /\
        c.cs_next_id <= last /\ c.cs_next_var <= limit.cs_next_var /\
        c0.cs_next_id <= c.cs_next_id /\ c0.cs_next_var <= c.cs_next_var /\
        fresh_vars_wrt limit u /\
        u.vs_alloca_next <= b+cap /\ B+P <= u.vs_alloca_next /\
        d+mo (LENGTH tys) <= u.vs_alloca_next /\
        abi_footprint_disjoint B P ((d,mo (LENGTH tys))::
          abi_decoder_child_scratch (abi_decoder_ids first last) b cap u) /\
        abi_footprint_disjoint d (mo (LENGTH tys))
          (abi_decoder_child_scratch (abi_decoder_ids first last) b cap u) /\
        eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d) /\
        eval_operand base_op u = SOME (n2w B) /\ eval_operand hi u = SOME (n2w H) /\
        EVERY (abi_decoder_operand_live c.cs_next_var) [src;dst;base_op;hi] /\
        ~u.vs_halted /\ u.vs_current_bb = c.cs_current_bb /\
        u.vs_inst_idx = LENGTH c.cs_current_insts /\
        abi_scratch_effect first last c0.cs_next_id c.cs_next_id c0.cs_next_var limit
          d (mo (LENGTH tys)) b cap s0 u
  in
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  (!i child_dst child_src a z u child_sb child_d.
    i < LENGTH tys /\ child_entry (EL i tys) (EL i tvs)
      child_dst child_src a z u child_sb child_d ==>
    ?k r. gas_path_mem ctx func u k r /\
      ((?t v. r = OK t /\ good (EL i tys) (EL i tvs) child_sb v /\
        val_in_memory (EL i tvs) v child_d t.vs_memory /\
        abi_scratch_effect first last a.cs_next_id z.cs_next_id a.cs_next_var limit
          child_d (type_memory_bytes ce (EL i tys)) b cap u t /\
        mem_bytes_at B P t.vs_memory = snap /\
        (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==> p+n <= t.vs_alloca_next) /\
        t.vs_current_bb = z.cs_current_bb /\ t.vs_inst_idx = LENGTH z.cs_current_insts /\
        ~t.vs_halted) \/
       (?t. r = Abort Revert_abort t /\ ~(?v. good (EL i tys) (EL i tvs) child_sb v)))) /\
  j <= LENGTH tys /\ sb+ao (LENGTH tys) <= H /\
  H <= P /\ LENGTH snap = P /\ B+P < dimword(:256) /\
  d+mo (LENGTH tys) < dimword(:256) /\ b+cap < dimword(:256) /\
  hi <> Lit 0w /\ base_op <> Lit 0w /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (abi_decoder_member_infos sf ce (DROP j tys)) (ao j) (mo j) st = ((),fin) /\
  fn_has_code st fin func /\ fn_inst_ids_distinct func /\
  fin.cs_next_id <= last /\ fin.cs_next_var <= limit.cs_next_var /\ inv j ps st s ==>
  ?k r. gas_path_mem ctx func s k r /\
    ((?t qs. r = OK t /\ LENGTH qs = LENGTH tys-j /\ inv (LENGTH tys) (ps++qs) fin t) \/
     (?t. r = Abort Revert_abort t /\
       ~(?ws. vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw raw /\
         abi_to_vyper_list env tys
           (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw raw) = SOME ws)))
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  map_every (fn q => qpat_x_assum q mp_tac) [`inv' j ps st s`,
    `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ st = _`,
    `fn_has_code st fin func`, `fin.cs_next_id <= last`,
    `fin.cs_next_var <= limit.cs_next_var`, `j <= LENGTH tys`] >>
  map_every qid_spec_tac [`ps`, `s`, `st`, `fin`] >>
  measureInduct_on `(\j. LENGTH tys-j) j` >> rpt strip_tac >>
  Cases_on `j = LENGTH tys`
  >- (gvs[abiDecoderMemberInfosTheory.abi_decoder_member_infos_def,
        compile_abi_decode_to_buf_def, comp_return_def] >>
      qexistsl_tac [`0`, `OK s`] >>
      conj_tac >- metis_tac[gas_path_mem_rules] >>
      disj1_tac >> simp[]) >>
  suspend "next_member"
QED

Resume extcall_decoder_remaining_members[next_member]:
  `j < LENGTH tys` by decide_tac >>
  `DROP j tys = EL j tys :: DROP (SUC j) tys` by
    metis_tac[DROP_CONS_EL] >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ st = _` mp_tac >>
  qpat_assum `DROP j tys = _` (fn th => once_rewrite_tac [th]) >>
  strip_tac >>
  drule abiDecoderMemberConsTheory.abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderMemberConsTheory.abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code st middle func /\ fn_has_code middle end_st func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[Abbr `inv'`] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st middle) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule exprSimConcatPathTheory.concat_code_prefix >>
     simp[] >>
     qpat_assum `middle.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[exprLoweringPropsTheory.emitted_insts_def, GSYM APPEND_ASSOC,
       DROP_APPEND]) >>

  `sb < dimword(:256) /\ B+P <= s.vs_alloca_next /\
   eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
   eval_operand base_op s = SOME (n2w B) /\ fresh_vars_wrt limit s /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi]` by
    (fs[Abbr `inv'`] >> decide_tac) >>
  `ao = (\j. SUM (MAP abi_member_head_size
      (MAP (vyper_to_abi_type env) (TAKE j tys)))) /\
   mo = (\j. SUM (MAP (type_memory_bytes ce) (TAKE j tys)))` by
    simp[Abbr `ao`, Abbr `mo`] >>
  drule_all extcall_decoder_member_index_windows >> strip_tac >>
  qpat_x_assum `ao = _` kall_tac >> qpat_x_assum `mo = _` kall_tac >>
  `middle.cs_next_var <= limit.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var base_op` by
    (qpat_assum `EVERY (abi_decoder_operand_live st.cs_next_var) _` mp_tac >>
     simp_tac (srw_ss()) []) >>
  qabbrev_tac `off = w2n (abi_decode_load MLOAD (n2w (B+(sb+ao j)):bytes32) s)` >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys)) ==>
   eval_operand base_op s = SOME (n2w B) /\
   abi_decode_load MLOAD (n2w (B+(sb+ao j)):bytes32) s = n2w off /\
   off < dimword(:256) /\ B+sb+ao j < dimword(:256) /\
   B+sb+ao j+32 <= s.vs_alloca_next` by
    (simp[Abbr `off`, w2n_lt]) >>
  drule_all extcall_decoder_member_setup_paths >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "setup_result"
QED

Resume extcall_decoder_remaining_members[setup_result]:
  markerLib.RESUME_TAC
  >- suspend "member_success" >>
  suspend "setup_abort"
QED

Resume extcall_decoder_remaining_members[member_success]:
  markerLib.RESUME_TAC >>
  qmatch_asmsub_abbrev_tac `r = OK u` >>
  `abi_decoder_address_frame st.cs_next_var s u /\
   fresh_vars_wrt limit u /\
   eval_operand (FST ops) u = SOME (n2w (sb +
     if dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys)) then off else ao j)) /\
   eval_operand (SND ops) u = SOME (n2w (d+mo j)) /\
   u.vs_current_bb = middle.cs_current_bb /\
   u.vs_inst_idx = LENGTH middle.cs_current_insts` by
    (simp[Abbr `u`, fresh_vars_wrt_def, abi_decoder_address_frame_def,
       eval_operand_def, exprLoweringPropsTheory.emitted_insts_def] >>
     fs[abi_decoder_address_frame_def, fresh_vars_wrt_def]) >>
  `child_entry (EL j tys) (EL j tvs) (SND ops) (FST ops) middle end_st u
    (sb + if dec_info_needs_offset (type_to_abi_dec_info sf ce (EL j tys))
          then off else ao j) (d+mo j)` by
    (qunabbrev_tac `child_entry` >> BETA_TAC >>
     irule (PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]
       (Q.INST [`di` |-> `type_to_abi_dec_info sf ce ty`]
         (SPEC_ALL extcall_decoder_member_entry))) >>
     qpat_x_assum `inv' j ps st s` mp_tac >>
     simp[Abbr `inv'`] >> strip_tac >>
     simp[] >>
     conj_tac
     >- (fs[abiDecoderTypedContractTheory.abi_decoder_entry_floor_def, cs_extends_def] >> decide_tac) >>
     qexistsl_tac [`mo (LENGTH tys)`, `s`, `st`] >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `!i child_dst child_src a z uu child_sb child_d. _`
    (drule_all_then strip_assume_tac) >>
  suspend "child_result"
QED

Resume extcall_decoder_remaining_members[child_result]:
  markerLib.RESUME_TAC
  >- suspend "child_abort" >>
  suspend "child_success"
QED

Resume extcall_decoder_remaining_members[child_abort]:
  markerLib.RESUME_TAC >>
  qexistsl_tac [`k+k'`, `r'`] >>
  conj_tac >- (irule gas_path_mem_then >> metis_tac[]) >>
  disj2_tac >> qexists_tac `t'` >> simp[] >>
  rpt strip_tac >>
  `sb <= H /\ mem_bytes_at B P s.vs_memory = snap` by fs[Abbr `inv'`] >>
  fs[Abbr `raw`] >>
  drule_all decoder_indexed_member_snapshot >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!v. ~good _ _ _ v` (qspec_then `EL j ws` mp_tac) >>
  gvs[Abbr `good`, Abbr `off`, Abbr `ao`] >>
  metis_tac[]
QED

Resume extcall_decoder_remaining_members[child_success]:
  markerLib.RESUME_TAC >>
  `observed j v` by
    (qunabbrev_tac `observed` >>
     simp_tac (srw_ss()) [markerTheory.Abbrev_def, Abbr `raw`] >>
     irule (SIMP_RULE bool_ss [LET_THM] decoder_member_snapshot_observed) >>
     conj_tac >- fs[Abbr `inv'`] >>
     conj_tac >- decide_tac >>
     qexistsl_tac [`B`, `P`, `ce`, `s`, `sf`, `EL j tvs`] >>
     fs[Abbr `inv'`, Abbr `good`, Abbr `off`] >> gvs[]) >>
  suspend "prefix_resources"
QED

Resume extcall_decoder_remaining_members[setup_abort]:
  markerLib.RESUME_TAC >>
  qexistsl_tac [`k`, `r`] >> simp[] >>
  rpt strip_tac >>
  `sb <= H /\ mem_bytes_at B P s.vs_memory = snap` by fs[Abbr `inv'`] >>
  fs[Abbr `raw`] >>
  drule_all decoder_indexed_member_snapshot >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[Abbr `ao`] >> decide_tac
QED

Resume extcall_decoder_remaining_members[prefix_resources]:
  markerLib.RESUME_TAC >>
  `abi_scratch_effect first last middle.cs_next_id end_st.cs_next_id st.cs_next_var limit
    d (mo (LENGTH tys)) b cap s t'` by
    (irule abi_scratch_effect_after_address >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `abi_scratch_effect first last middle.cs_next_id end_st.cs_next_id st.cs_next_var limit
    (d+mo j) (type_memory_bytes ce (EL j tys)) b cap s t'` by
    (irule abi_scratch_effect_after_address >>
     qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ u t'`
       (irule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  suspend "prefix_invariant"
QED

Resume extcall_decoder_remaining_members[prefix_invariant]:
  markerLib.RESUME_TAC >>
  `!i. SUM (MAP type_memory_size (TAKE i tvs)) = mo i` by
    (gen_tac >> simp[Abbr `mo`, MAP_TAKE]) >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `type_memory_size (EL j tvs) = type_memory_bytes ce (EL j tys)` by
    (qpat_assum `MAP type_memory_size tvs = _` mp_tac >>
     simp_tac bool_ss [LIST_EQ_REWRITE, LENGTH_MAP] >>
     disch_then (qspec_then `j` mp_tac o CONJUNCT2) >> simp[EL_MAP]) >>
  `mo (LENGTH tys) = SUM (MAP type_memory_size tvs)` by simp[Abbr `mo`] >>
  `first <= middle.cs_next_id` by
    (fs[Abbr `inv'`, abiDecoderTypedContractTheory.abi_decoder_entry_floor_def] >> decide_tac) >>
  `LENGTH (ps++[v]) = SUC j /\ mem_bytes_at B P t'.vs_memory = snap /\
    (!i. i < SUC j ==> observed i (EL i (ps++[v])) /\
      value_has_type (EL i tvs) (EL i (ps++[v])) /\
      val_in_memory (EL i tvs) (EL i (ps++[v])) (d+mo i) t'.vs_memory)` by
    (qpat_assum `!i. SUM _ = mo i` (fn th => rewrite_tac [GSYM th]) >>
     irule extcall_decoder_member_prefix_advance >>
     fs[Abbr `inv'`, Abbr `good`] >>
     qpat_assum `abi_scratch_effect _ _ _ _ _ _ (d+mo j) _ _ _ s t'`
       (irule_at Any) >> simp[] >>
     qpat_assum `MAP type_memory_size tvs = _`
       (fn th => rewrite_tac [GSYM th]) >> simp[]) >>
  suspend "next_invariant"
QED

Resume extcall_decoder_remaining_members[next_invariant]:
  markerLib.RESUME_TAC >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ d _ _ _ s t'` mp_tac >>
  simp_tac bool_ss [abiScratchEncoderContractTheory.abi_scratch_effect_def] >> strip_tac >>
  `inv' (SUC j) (ps++[v]) end_st t'` by
    (simp_tac bool_ss [Abbr `inv'`] >>
     fs[] >>
     qpat_assum `MAP type_memory_size tvs = _`
       (fn th => rewrite_tac [GSYM th]) >>
     rpt conj_tac
     >- metis_tac[ADD_COMM]
     >- (simp[abiDecoderTypedContractTheory.abi_decoder_entry_floor_def] >> decide_tac)
     >- fs[abi_scratch_evolution_def]
     >- (fs[abi_scratch_evolution_def] >> decide_tac)
     >- (fs[abi_scratch_evolution_def] >>
         qpat_assum `MAP type_memory_size tvs = _`
           (fn th => fs[GSYM th]) >> decide_tac)
     >- (`abi_footprint_disjoint B P
            (abi_decoder_child_scratch (abi_decoder_ids first last) b cap t')` by
           (irule abi_scratch_disjoint_advance >> simp[] >>
            goal_assum (drule_at Any) >> simp[] >>
            fs[abi_footprint_disjoint_def]) >>
         fs[abi_footprint_disjoint_def] >> metis_tac[])
     >- (irule abi_scratch_disjoint_advance >> simp[] >>
         goal_assum (drule_at Any) >> simp[] >>
         qpat_assum `MAP type_memory_size tvs = _`
           (fn th => rewrite_tac [GSYM th]) >> simp[])
     >- (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> decide_tac)
     >- (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> decide_tac)
     >- (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> decide_tac)
     >- (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> decide_tac)
     >> `abi_scratch_effect first last c0.cs_next_id end_st.cs_next_id c0.cs_next_var limit
           d (SUM (MAP type_memory_size tvs)) b cap s0 s` by
          (irule abi_scratch_effect_widen >>
           qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ s0 s` (irule_at Any) >>
           simp[] >> decide_tac)
     >> irule abi_scratch_effect_trans_tail
     >> qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ s0 s` (irule_at Any)
     >> qpat_assum `abi_scratch_effect _ _ _ _ _ _ d _ _ _ s t'` (irule_at Any)
     >> decide_tac) >>
  suspend "recurse"
QED

Resume extcall_decoder_remaining_members[recurse]:
  markerLib.RESUME_TAC >>
  `ao (SUC j) = ao j + abi_embedded_static_size ce.ce_struct_fields (EL j tys) /\
   mo (SUC j) = mo j + type_memory_bytes ce (EL j tys)` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     simp[abiDecoderCoherenceTheory.abi_decoder_header_def] >> strip_tac >>
     simp[Abbr `ao`, Abbr `mo`, TAKE_SUC_BY_TAKE, MAP_SNOC, SUM_SNOC]) >>
  qpat_x_assum `!y. LENGTH tys - y < LENGTH tys - j ==> _`
    (qspec_then `SUC j` mp_tac) >>
  simp_tac (srw_ss()) [] >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`fin`, `end_st`, `t'`, `ps++[v]`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[] >> strip_tac >>
  `gas_path_mem ctx func s (k + k') (OK t')` by
    (irule gas_path_mem_then >> metis_tac[]) >>
  suspend "compose_tail"
QED

Resume extcall_decoder_remaining_members[compose_tail]:
  markerLib.RESUME_TAC >>
  qexistsl [`(k + k') + k''`, `r''`] >>
  (conj_tac >- (irule gas_path_mem_then >> metis_tac[])) >>
  simp[] >> qexists_tac `v::qs` >>
  conj_tac >- (simp[] >> decide_tac) >>
  qpat_x_assum `inv' _ (ps ++ [v] ++ qs) _ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Finalise extcall_decoder_remaining_members


(* One guarded traversal, shared by the concrete aggregate constructors. *)
Theorem extcall_decoder_complex_members[local]:
  let ao = \j. SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) (TAKE j tys)));
      mo = \j. SUM (MAP (type_memory_bytes ce) (TAKE j tys));
      raw = DROP sb (TAKE H snap);
      good = \ty tv child_sb v.
        child_sb <= H /\
        vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP child_sb (TAKE H snap)) /\
        (is_dynamic (vyper_to_abi_type env ty) \/
          static_length (vyper_to_abi_type env ty) <= LENGTH (DROP child_sb (TAKE H snap))) /\
        abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
          (DROP child_sb (TAKE H snap))) = SOME v /\ value_has_type tv v;
      child_entry = \ty tv dst src a z u child_sb child_d.
        abi_decoder_coherent ce env sf ty tv /\
        compile_abi_decode_to_buf dst src MLOAD base_op hi
          (type_to_abi_dec_info sf ce ty) a = ((),z) /\
        fn_has_code a z func /\ fn_inst_ids_distinct func /\
        eval_operand base_op u = SOME (n2w B) /\
        eval_operand src u = SOME (n2w child_sb) /\
        eval_operand dst u = SOME (n2w child_d) /\ eval_operand hi u = SOME (n2w H) /\
        hi <> Lit 0w /\ base_op <> Lit 0w /\
        H <= P /\ B+P < dimword(:256) /\ B+P <= u.vs_alloca_next /\
        child_sb < dimword(:256) /\ child_d+type_memory_bytes ce ty < dimword(:256) /\
        child_d+type_memory_bytes ce ty <= u.vs_alloca_next /\
        LENGTH snap = P /\ mem_bytes_at B P u.vs_memory = snap /\
        (!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> child_sb+32 <= H) /\
        abi_footprint_disjoint B P ((child_d,type_memory_bytes ce ty)::
          abi_decoder_child_scratch (abi_decoder_ids first last) b cap u) /\
        abi_footprint_disjoint child_d (type_memory_bytes ce ty)
          (abi_decoder_child_scratch (abi_decoder_ids first last) b cap u) /\
        (!id p n. FLOOKUP u.vs_allocas id = SOME (p,n) ==> p+n <= u.vs_alloca_next) /\
        abi_decoder_budget first last b cap u /\ first <= abi_decoder_entry_floor a /\
        z.cs_next_id <= last /\ z.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit u /\
        b+cap < dimword(:256) /\ u.vs_alloca_next <= b+cap /\
        EVERY (abi_decoder_operand_live a.cs_next_var) [src;dst;base_op;hi] /\
        ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
        u.vs_inst_idx = LENGTH a.cs_current_insts;
      observed = \i v.
        let at = vyper_to_abi_type env (EL i tys);
            tail = DROP (ao i) raw;
            xs = if is_dynamic at then DROP (abi_head_word tail) raw else tail in
        vyper_decode_valid_enc at xs /\ (is_dynamic at \/ static_length at <= LENGTH xs) /\
        abi_to_vyper env (EL i tys) (dec at xs) = SOME v
  in
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  (!i child_dst child_src a z u child_sb child_d.
    i < LENGTH tys /\ child_entry (EL i tys) (EL i tvs)
      child_dst child_src a z u child_sb child_d ==>
    ?k r. gas_path_mem ctx func u k r /\
      ((?t v. r = OK t /\ good (EL i tys) (EL i tvs) child_sb v /\
        val_in_memory (EL i tvs) v child_d t.vs_memory /\
        abi_scratch_effect first last a.cs_next_id z.cs_next_id a.cs_next_var limit
          child_d (type_memory_bytes ce (EL i tys)) b cap u t /\
        mem_bytes_at B P t.vs_memory = snap /\
        (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==> p+n <= t.vs_alloca_next) /\
        t.vs_current_bb = z.cs_current_bb /\ t.vs_inst_idx = LENGTH z.cs_current_insts /\
        ~t.vs_halted) \/
       (?t. r = Abort Revert_abort t /\ ~(?v. good (EL i tys) (EL i tvs) child_sb v)))) /\
  H <= P /\ LENGTH snap = P /\ B+P < dimword(:256) /\ sb < dimword(:256) /\
  d+mo (LENGTH tys) < dimword(:256) /\ b+cap < dimword(:256) /\
  hi <> Lit 0w /\ base_op <> Lit 0w /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),fin) /\
  fn_has_code st fin func /\ fn_inst_ids_distinct func /\
  fin.cs_next_id <= last /\ fin.cs_next_var <= limit.cs_next_var /\
  mem_bytes_at B P s.vs_memory = snap /\
  (!id p n. FLOOKUP s.vs_allocas id = SOME (p,n) ==> p+n <= s.vs_alloca_next) /\
  abi_decoder_budget first last b cap s /\ first <= abi_decoder_entry_floor st /\
  fresh_vars_wrt limit s /\ s.vs_alloca_next <= b+cap /\
  B+P <= s.vs_alloca_next /\ d+mo (LENGTH tys) <= s.vs_alloca_next /\
  abi_footprint_disjoint B P ((d,mo (LENGTH tys))::
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  abi_footprint_disjoint d (mo (LENGTH tys))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?k r. gas_path_mem ctx func s k r /\
    ((?t vs. r = OK t /\ sb <= H /\ sb + ao (LENGTH tys) <= H /\ LENGTH vs = LENGTH tys /\
       (!i. i < LENGTH tys ==> observed i (EL i vs) /\
          value_has_type (EL i tvs) (EL i vs) /\
          val_in_memory (EL i tvs) (EL i vs) (d+mo i) t.vs_memory) /\
       abi_scratch_effect first last st.cs_next_id fin.cs_next_id st.cs_next_var limit
         d (mo (LENGTH tys)) b cap s t /\
       mem_bytes_at B P t.vs_memory = snap /\
       (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==> p+n <= t.vs_alloca_next) /\
       t.vs_current_bb = fin.cs_current_bb /\ t.vs_inst_idx = LENGTH fin.cs_current_insts /\
       ~t.vs_halted) \/
     (?t. r = Abort Revert_abort t /\
       ~(?vs. sb <= H /\ vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw raw /\
         abi_to_vyper_list env tys
           (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw raw) = SOME vs)))
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  drule abiDecoderMemberInfosTheory.abi_decoder_member_infos_layout >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_complex_phases, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),mid)` >>
  `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) < dimword(:256)` by
    (drule extcall_decoder_members_head_bound >> simp[] >> strip_tac >>
     fs[Abbr `mo`] >> decide_tac) >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderComplexExecuteTheory.abi_decoder_complex_code >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule exprSimConcatPathTheory.concat_code_prefix >> simp[] >>
     fs[IS_PREFIX_APPEND] >> simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var hi` by fs[] >>
  Cases_on `sb+ao (LENGTH tys) <= H`
  >- suspend "guard_success" >>
  suspend "guard_reject"
QED

Resume extcall_decoder_complex_members[guard_reject]:
  `H < dimword(:256) /\ H < sb + SUM (MAP abi_member_head_size
      (MAP (vyper_to_abi_type env) tys))` by (fs[Abbr `ao`] >> decide_tac) >>
  drule_all extcall_decoder_complex_guard_reject >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`k`, `Abort Revert_abort t`] >> simp[] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  drule abiValidMembersTheory.abi_valid_members_view >>
  simp[Abbr `raw`, LENGTH_DROP, LENGTH_TAKE] >> decide_tac
QED

Resume extcall_decoder_complex_members[guard_success]:
  `H < dimword(:256) /\ sb <= H /\
   sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= H /\
   mid.cs_next_var <= limit.cs_next_var` by (fs[Abbr `ao`] >> gvs[]) >>
  drule_all extcall_decoder_complex_guard_success >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s k (OK ready)` >>
  `abi_decoder_address_frame st.cs_next_var s ready /\ fresh_vars_wrt limit ready` by
    (fs[Abbr `ready`, abi_decoder_address_frame_def, fresh_vars_wrt_def]) >>
  `abi_scratch_effect first last st.cs_next_id mid.cs_next_id st.cs_next_var limit
     d (mo (LENGTH tys)) b cap s ready` by
    (irule abi_scratch_address_effect >> simp[]) >>
  drule_all abi_scratch_address >>
  disch_then (qspecl_then [`abi_decoder_ids first last`, `[]`] strip_assume_tac) >>
  mp_tac (Q.INST [`j` |-> `0`, `ps` |-> `[]`, `c0` |-> `st`,
    `s0` |-> `s`, `st` |-> `mid`, `s` |-> `ready`, `P` |-> `LENGTH snap`]
    extcall_decoder_remaining_members) >>
  rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `_ ==> ?k r. gas_path_mem ctx func ready k r /\ _` mp_tac >>
  impl_tac >- suspend "traversal_initial" >>
  suspend "traversal_result"
QED

Resume extcall_decoder_complex_members[traversal_initial]:
  `child_entry' = child_entry /\ good' = good` by
    (simp[Abbr `child_entry'`, Abbr `child_entry`, Abbr `good'`, Abbr `good`, ADD_COMM]) >>
  simp[Abbr `ao'`, Abbr `mo'`, Abbr `ao`, Abbr `mo`] >>
  simp[Abbr `inv'`] >>
  `first <= abi_decoder_entry_floor mid` by
    (fs[abiDecoderTypedContractTheory.abi_decoder_entry_floor_def] >> decide_tac) >>
  fs[abi_decoder_address_frame_def] >>
  simp[Abbr `ready`, abi_decoder_operand_live_mono] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[abi_decoder_operand_live_mono, DECIDE ``n <= n+6``] >>
  fs[IS_PREFIX_APPEND, emitted_insts_def]
QED

Resume extcall_decoder_complex_members[traversal_result]:
  strip_tac >>
  qexistsl_tac [`k+k'`, `r`] >>
  (conj_tac >- (irule gas_path_mem_then >> metis_tac[])) >>
  gvs[Abbr `inv'`] >> metis_tac[]
QED

Finalise extcall_decoder_complex_members

(* Shared statement syntax only; these quotations introduce no HOL constants. *)
val decoder_entry_syntax = ``\ce env sf ty tv dst src st fin s sb d.
  abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) st = ((),fin) /\
  fn_has_code st fin func /\ fn_inst_ids_distinct func /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand hi s = SOME (n2w H) /\
  hi <> Lit 0w /\ base_op <> Lit 0w /\
  H <= P /\ B+P < dimword(:256) /\ B+P <= s.vs_alloca_next /\
  sb < dimword(:256) /\ d+type_memory_bytes ce ty < dimword(:256) /\
  d+type_memory_bytes ce ty <= s.vs_alloca_next /\
  LENGTH snap = P /\ mem_bytes_at B P s.vs_memory = snap /\
  (!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> sb+32 <= H) /\
  abi_footprint_disjoint B P ((d,type_memory_bytes ce ty)::
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  abi_footprint_disjoint d (type_memory_bytes ce ty)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  (!id p n. FLOOKUP s.vs_allocas id = SOME (p,n) ==> p+n <= s.vs_alloca_next) /\
  abi_decoder_budget first last b cap s /\ first <= abi_decoder_entry_floor st /\
  fin.cs_next_id <= last /\ fin.cs_next_var <= limit.cs_next_var /\
  fresh_vars_wrt limit s /\ b+cap < dimword(:256) /\ s.vs_alloca_next <= b+cap /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts``;

val decoder_good_syntax = ``\env ty tv sb v.
  let at = vyper_to_abi_type env ty; xs = DROP sb (TAKE H snap) in
  sb <= H /\ vyper_decode_valid_enc at xs /\
  (is_dynamic at \/ static_length at <= LENGTH xs) /\
  abi_to_vyper env ty (dec at xs) = SOME v /\ value_has_type tv v``;

val decoder_result_syntax = ``\ce env ty tv st fin s sb d.
  ?k r. gas_path_mem ctx func s k r /\
    ((?t v. r = OK t /\ ^decoder_good_syntax env ty tv sb v /\
      val_in_memory tv v d t.vs_memory /\
      abi_scratch_effect first last st.cs_next_id fin.cs_next_id st.cs_next_var limit
        d (type_memory_bytes ce ty) b cap s t /\
      mem_bytes_at B P t.vs_memory = snap /\
      (!id p n. FLOOKUP t.vs_allocas id = SOME (p,n) ==> p+n <= t.vs_alloca_next) /\
      t.vs_current_bb = fin.cs_current_bb /\ t.vs_inst_idx = LENGTH fin.cs_current_insts /\
      ~t.vs_halted) \/
     (?t. r = Abort Revert_abort t /\ ~(?v. ^decoder_good_syntax env ty tv sb v)))``;

Theorem extcall_decoder_tuple_memory:
  let entry = ^decoder_entry_syntax;
      result = ^decoder_result_syntax
  in
  (!i child_dst child_src a z u child_sb child_d.
    i < LENGTH tys /\ entry ce env sf (EL i tys) (EL i tvs)
      child_dst child_src a z u child_sb child_d ==>
    result ce env (EL i tys) (EL i tvs) a z u child_sb child_d) /\
  entry ce env sf (TupleT tys) (TupleTV tvs) dst src st fin s sb d ==>
  result ce env (TupleT tys) (TupleTV tvs) st fin s sb d
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `entry ce env sf (TupleT tys) _ _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `entry`] >> strip_tac >>
  `evaluate_type env (TupleT tys) = SOME (TupleTV tvs) /\
   type_memory_size (TupleTV tvs) = type_memory_bytes ce (TupleT tys)` by
    metis_tac[abiDecoderCoherenceTheory.abi_decoder_coherent_header,
      abiDecoderCoherenceTheory.abi_decoder_header_def] >>
  `LENGTH tys < dimword(:256)` by
    (drule_all extcall_decoder_tuple_budget_bound >> simp[]) >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
    fs[abiDecoderCoherenceTheory.abi_decoder_coherent_tuple_iff] >>
  `MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys` by
    (`LENGTH tvs = LENGTH tys` by metis_tac[LIST_REL_LENGTH] >>
     irule LIST_EQ >> simp[] >> rpt strip_tac >>
     drule_all abiDecoderCoherenceTheory.abi_decoder_coherent_tuple_child >>
     disch_then (strip_assume_tac o MATCH_MP abiDecoderCoherenceTheory.abi_decoder_coherent_header) >>
     fs[abiDecoderCoherenceTheory.abi_decoder_header_def, EL_MAP]) >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)` by
    (qpat_x_assum `type_memory_size (TupleTV tvs) = _` mp_tac >>
     simp[valueEncodingTheory.type_memory_size_def,
       valueEncodingProofsTheory.type_memory_size_list_sum]) >>
  mp_tac (Q.INST [`dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`]
    extcall_decoder_complex_members) >>
  rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `_ ==> ?k r. gas_path_mem ctx func s k r /\ _` mp_tac >>
  impl_tac >- suspend "tuple_initial" >>
  suspend "tuple_result"
QED

Resume extcall_decoder_tuple_memory[tuple_initial]:
  fs[abiDecoderMemberInfosTheory.abi_decoder_tuple_infos] >>
  simp[Abbr `mo`] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i child_dst child_src a z u child_sb child_d. _` mp_tac >>
  simp[Abbr `child_entry`, Abbr `result`, Abbr `good`, markerTheory.Abbrev_def] >>
  metis_tac[]
QED

Resume extcall_decoder_tuple_memory[tuple_result]:
  strip_tac >>
  simp[Abbr `result`, markerTheory.Abbrev_def] >>
  qexistsl_tac [`k`, `r`] >> simp[]
  >- suspend "tuple_success" >>
  suspend "tuple_reject"
QED

Resume extcall_decoder_tuple_memory[tuple_success]:
  qpat_x_assum `!i child_dst child_src a z u child_sb child_d. _` kall_tac >>
  `LENGTH raw = H - sb` by simp[Abbr `raw`, LENGTH_TAKE, MIN_DEF] >>
  `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= LENGTH raw` by
    (fs[Abbr `ao`] >> decide_tac) >>
  mp_tac (MATCH_MP decoder_members_completed_prefix
    (CONJ static_decode_valid_suffix static_dec_suffix)) >>
  disch_then (qspecl_then [`tys`, `vs`, `raw`] mp_tac) >>
  impl_tac >- (fs[Abbr `observed`, Abbr `ao`, markerTheory.Abbrev_def] >> metis_tac[]) >>
  strip_tac >>
  drule_all decoder_tuple_completion >> strip_tac >>
  `tuple_in_memory vs tvs d t.vs_memory` by
    (irule tuple_in_memory_from_elements >>
     `LENGTH tvs = LENGTH tys` by metis_tac[LIST_REL_LENGTH] >>
     simp[] >> rpt strip_tac >>
     `SUM (MAP type_memory_size (TAKE i tvs)) = mo i` by
       (asm_simp_tac std_ss [Abbr `mo`, MAP_TAKE]) >>
     metis_tac[]) >>
  qexists_tac `ArrayV (TupleV vs)` >>
  gvs[Once vyperABITheory.vyper_to_abi_type_def,
    abiDecoderMembersTheory.vyper_to_abi_types_MAP,
    Once contractABITheory.dec_def, valueEncodingDefsTheory.val_in_memory_def,
    abiValidMembersTheory.abi_decode_members_value, Abbr `mo`, Abbr `raw`] >>
  first_assum ACCEPT_TAC
QED

Resume extcall_decoder_tuple_memory[tuple_reject]:
  qpat_x_assum `!i child_dst child_src a z u child_sb child_d. _` kall_tac >>
  gvs[Abbr `raw`] >> rpt strip_tac >>
  qpat_x_assum `!vs. abi_to_vyper_list _ _ _ = SOME vs ==> _` mp_tac >>
  qpat_x_assum `abi_to_vyper env (TupleT tys) _ = SOME v` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[Once vyperABITheory.abi_to_vyper_def,
    abiDecoderMembersTheory.vyper_to_abi_types_MAP,
    abiValidMembersTheory.abi_decode_members_value, AllCaseEqs(),
    Once vyperABITheory.vyper_decode_valid_enc_def] >>
  metis_tac[]
QED

Finalise extcall_decoder_tuple_memory
