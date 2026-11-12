(* Conditional composite decoder replay: concrete guarded entry phases. *)
Theory extcallDecoderCompositeMemory
Ancestors
  extcallDecoderPreparationMemory extcallDecoderMemberPreparationMemory extcallDecoderHeadBounds
  extcallDecoderMemberSemantics extcallDecoderArraySemantics extcallDecoderStaticSuffix
  extcallDecoderPrefixMemory extcallDecoderBulkMemory extcallDecoderLoopEdgesMemory
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMemberBound
  abiDecoderMemberSetup abiDecoderMemberCode freshWrites exprSimCalldataSlice
  abiDecoderReentry abiDecoderReentryPointer abiDecoderReservation abiDecoderVarSequence abiDecoderDynamicLoopSetup
  loweringStateRelDefs varsExt abiScratchAddress abiScratchDecoderSubwindow abiEncoderArrayFrame
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
    fresh_vars_wrt limit t /\ abi_decoder_address_frame st.cs_next_var s t
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
      inst_extends st fin) \/
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
