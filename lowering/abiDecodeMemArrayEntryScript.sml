(* Guarded nonbulk-array constructor entry, before its finite loop. *)
Theory abiDecodeMemArrayEntry
Ancestors
  abiDecodeMemBulkPrefix abiDecodeMemBulkBody abiDecodeMemScratch abiDecodeMemArrayHeaderFrame
  abiDecoderReentry abiDecoderArrayLoopInit abiDecoderFrameCompose abiDecoderFrame
  abiDecoderDynarrayBound abiDecoderDynarrayPrefix abiDecoderIndexInit
  abiDecoderReservation abiDecoderComposition abiDecoderArrayHeader abiDecoderContract abiDecoderGuards abiDecoderRange
  entryDecoderHistoryFrame allocaHistoryFragment allocaFootprint localPtrsProps
  fragGasPathMem fragGasMode fragGasSeqMem fragExecMem fragExec entrySinkExtraction
  emitHelperProps exprLoweringProps loweringStateRelDefs compileEnv emitHelper
  venomExecSemantics venomState venomInst finite_map words arithmetic list rich_list

Theorem abi_decode_array_header_path_mem[local]:
  abi_decode_array_header dst addr MLOAD st = (cnt,st') /\
  eval_operand addr s = SOME a /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ w2n a+32 <= s.vs_alloca_next /\
  d+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand cnt t = SOME (abi_decode_load MLOAD a s) /\
    mem_word_at d t.vs_memory = abi_decode_load MLOAD a s /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    alloca_history func t /\ ~t.vs_halted /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  drule_all abi_decode_array_header_mem_ok >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op (t with vs_inst_idx := LENGTH st'.cs_current_insts) = eval_operand op s` by
    (rpt strip_tac >> irule abi_decode_array_header_live_frame >> metis_tac[]) >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
      (emitted_insts st st')` by fs[EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, abi_decode_frame_def] >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem nonbulk_slot_separation[local]:
  b+h <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
  (!q. protected q ==> q+32 <= s.vs_alloca_next) /\
  (!q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    (b+h <= q \/ q+32 <= b) /\ (d+cap <= q \/ q+32 <= d) /\
    (!x. protected x ==> x+32 <= q \/ q+32 <= x)) /\
  (case FLOOKUP s.vs_allocas id of NONE => slot = s.vs_alloca_next
     | SOME (q,k) => slot = q) ==>
  (b+h <= slot \/ slot+32 <= b) /\ (d+cap <= slot \/ slot+32 <= d) /\
  (!q. protected q ==> q+32 <= slot \/ slot+32 <= q)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (gvs[] >> metis_tac[]) >>
  PairCases_on `x` >> gvs[] >> metis_tac[]
QED

Theorem nonbulk_two_region_frame[local]:
  abi_decode_frame d 32 s1 s2 /\ abi_decode_frame slot 32 s2 t /\
  s1.vs_memory = s.vs_memory /\ s1.vs_call_ctx = s.vs_call_ctx /\
  s1.vs_data_section = s.vs_data_section /\ 32 <= cap ==>
  abi_decode_footprint_frame [(d,cap);(slot,32)] s t
Proof
  strip_tac >>
  `abi_decode_footprint_frame [(d,cap);(slot,32)] s1 t` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `s2` >> conj_tac >>
     irule abi_decode_footprint_frame_weaken
     >- (qexists_tac `[(d,32)]` >> simp[GSYM abi_decode_frame_footprint, MEM] >>
         rpt strip_tac >> qexistsl_tac [`d`,`cap`] >> simp[]) >>
     qexists_tac `[(slot,32)]` >> simp[GSYM abi_decode_frame_footprint, MEM] >>
     rpt strip_tac >> qexistsl_tac [`slot`,`32`] >> simp[]) >>
  gvs[abi_decode_footprint_frame_def]
QED

Theorem nonbulk_frame_observations[local]:
  abi_decode_footprint_frame [(d,cap);(slot,32)] s t /\
  abi_decode_frame slot 32 s2 t /\ mload d s2 = cw /\
  mload (b+p) s = cw /\ p+32 <= h /\ 32 <= cap /\
  (b+h <= d \/ d+cap <= b) /\
  (b+h <= slot \/ slot+32 <= b) /\ (d+cap <= slot \/ slot+32 <= d) /\
  (!q. protected q ==> (q+32 <= d \/ d+cap <= q) /\
     (q+32 <= slot \/ slot+32 <= q)) ==>
  mem_bytes_at b h t.vs_memory = mem_bytes_at b h s.vs_memory /\
  (!q. protected q ==> mload q t = mload q s) /\
  mload d t = cw /\ mload (b+p) t = cw
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint b h [(d,cap);(slot,32)]` by
    (simp[abi_footprint_disjoint_def, MEM] >> metis_tac[]) >>
  conj_tac >- (irule abi_decode_footprint_frame_slice >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule abi_decode_footprint_frame_mload >>
      qexists_tac `[(d,cap);(slot,32)]` >>
      simp[abi_footprint_disjoint_def, MEM] >> metis_tac[]) >>
  conj_tac
  >- (`mload d t = mload d s2` suffices_by simp[] >>
      rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
      irule abi_decode_frame_mem_word >> qexistsl_tac [`slot`,`32`] >>
      asm_rewrite_tac[] >> decide_tac) >>
  `mload (b+p) t = mload (b+p) s` suffices_by simp[] >>
  irule abi_decode_footprint_frame_mload >> qexists_tac `[(d,cap);(slot,32)]` >>
  simp[abi_footprint_disjoint_def, MEM] >> rpt strip_tac >> decide_tac
QED

Theorem nonbulk_header_index_path[local]:
  abi_decode_array_header dst addr MLOAD st = (cnt,mid) /\
  abi_decode_index_init mid = (ip,last) /\
  eval_operand addr s = SOME (n2w (b+p)) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load MLOAD (n2w (b+p):bytes32) s = n2w c /\
  abi_decoder_operand_live st.cs_next_var dst /\
  b+p < dimword (:256) /\ d < dimword (:256) /\ p+32 <= h /\ 32 <= cap /\
  b+h <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
  (b+h <= d \/ d+cap <= b) /\
  (!q. protected q ==> q+32 <= s.vs_alloca_next /\ (q+32 <= d \/ d+cap <= q)) /\
  (!q k. FLOOKUP s.vs_allocas mid.cs_next_id = SOME (q,k) ==>
    k = 32 /\ (b+h <= q \/ q+32 <= b) /\ (d+cap <= q \/ q+32 <= d) /\
    (!x. protected x ==> x+32 <= q \/ q+32 <= x)) /\
  fresh_vars_wrt st s /\ fn_has_code st mid func /\ fn_has_code mid last func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = last.cs_current_bb /\ t.vs_inst_idx = LENGTH last.cs_current_insts /\
    ~t.vs_halted /\ fresh_vars_wrt last t /\
    eval_operand ip t = SOME (n2w slot) /\ mload slot t = 0w /\
    eval_operand cnt t = SOME (n2w c) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    mload d t = n2w c /\ mload (b+p) t = n2w c /\
    b+h <= t.vs_alloca_next /\ d+cap <= t.vs_alloca_next /\
    slot+32 <= t.vs_alloca_next /\ slot+32 < dimword (:256) /\
    (b+h <= slot \/ slot+32 <= b) /\ (d+cap <= slot \/ slot+32 <= d) /\
    (!q. protected q ==> q+32 <= slot \/ slot+32 <= q) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas mid.cs_next_id = SOME (slot,32) /\
    (!q. q <> mid.cs_next_id ==> FLOOKUP t.vs_allocas q = FLOOKUP s.vs_allocas q) /\
    alloca_room ctx func t /\ alloca_inv t /\ alloca_history func t /\
    mem_bytes_at b h t.vs_memory = mem_bytes_at b h s.vs_memory /\
    (!q. protected q ==> mload q t = mload q s) /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    abi_decode_footprint_frame [(d,cap);(slot,32)] s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `w2n (n2w (b+p):bytes32)+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next`
    by (asm_simp_tac pure_ss [w2n_n2w, LESS_MOD] >> decide_tac) >>
  drule_all abi_decode_array_header_path_mem >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s 0 (OK u)` >>
  `alloca_inv u /\ alloca_room ctx func u` by
    (conj_tac >- (irule alloca_inv_fields >> metis_tac[]) >>
     irule alloca_room_fields >> metis_tac[]) >>
  `fresh_vars_wrt last u` by
    (irule fresh_vars_wrt_mono >> qexists_tac `mid` >> asm_rewrite_tac[] >> decide_tac) >>
  `!q k. FLOOKUP u.vs_allocas mid.cs_next_id = SOME (q,k) ==> k = 32` by metis_tac[] >>
  `mid.cs_next_var < last.cs_next_var` by decide_tac >>
  drule_all abi_decode_index_init_path_mem >> strip_tac >>
  rename1 `gas_path_mem ctx func u 0 (OK t)` >> rename1 `FLOOKUP t.vs_allocas mid.cs_next_id = SOME (slot,32)` >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> `abi_decoder_operand_live mid.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
        asm_rewrite_tac[] >> decide_tac) >> metis_tac[]) >>
  `abi_decoder_operand_live mid.cs_next_var cnt` by (irule abi_decoder_operand_live_fresh >>
     qexistsl_tac [`u`,`abi_decode_load MLOAD (n2w (b+p):bytes32) s`] >> asm_rewrite_tac[]) >>
  `eval_operand cnt t = SOME (n2w c)` by metis_tac[] >>
  `mload d u = n2w c` by metis_tac[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `mload (b+p) s = n2w c` by (qpat_x_assum `abi_decode_load MLOAD _ s = _` mp_tac >>
     qpat_x_assum `b+p < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_load_def, w2n_n2w, LESS_MOD]) >>
  `!q k. FLOOKUP u.vs_allocas mid.cs_next_id = SOME (q,k) ==>
    (b+h <= q \/ q+32 <= b) /\ (d+cap <= q \/ q+32 <= d) /\
    (!x. protected x ==> x+32 <= q \/ q+32 <= x)` by metis_tac[] >>
  `(b+h <= slot \/ slot+32 <= b) /\ (d+cap <= slot \/ slot+32 <= d) /\
    (!q. protected q ==> q+32 <= slot \/ slot+32 <= q)` by
    (irule nonbulk_slot_separation >> qexistsl_tac [`mid.cs_next_id`,`u`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `abi_decode_footprint_frame [(d,cap);(slot,32)] s t` by (qpat_x_assum `abi_decode_frame d 32 s u` mp_tac >>
     qpat_x_assum `abi_decode_frame slot 32 u t` mp_tac >>
     qpat_x_assum `32 <= cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[nonbulk_two_region_frame]) >>
  `!q. protected q ==> (q+32 <= d \/ d+cap <= q) /\ (q+32 <= slot \/ slot+32 <= q)` by metis_tac[] >>
  `mem_bytes_at b h t.vs_memory = mem_bytes_at b h s.vs_memory /\
   (!q. protected q ==> mload q t = mload q s) /\
   mload d t = n2w c /\ mload (b+p) t = n2w c` by
    (irule nonbulk_frame_observations >> asm_rewrite_tac[] >>
     qexistsl_tac [`cap`,`u`,`slot`] >> asm_rewrite_tac[]) >>
  `gas_path_mem ctx func s 0 (OK t)` by metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  qpat_assum `abi_decode_footprint_frame _ s t` (strip_assume_tac o REWRITE_RULE [abi_decode_footprint_frame_def]) >>
  `!q. q <> mid.cs_next_id ==> FLOOKUP t.vs_allocas q = FLOOKUP s.vs_allocas q` by metis_tac[] >>
  qexistsl_tac [`t`,`slot`] >> asm_rewrite_tac[] >> rpt conj_tac >> decide_tac
QED

Theorem abi_decode_mem_nonbulk_entry:
  abi_decode_dynarray_position_prefix pos MLOAD base_op hi maxn asz st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand hi s = SOME (n2w h) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  p < dimword (:256) /\ b+h < dimword (:256) /\ b+h <= s.vs_alloca_next /\
  maxn < dimword (:256) /\ maxn*asz < dimword (:256) /\
  32+maxn*msz <= cap /\ d+cap < dimword (:256) /\ d+cap <= s.vs_alloca_next /\
  (b+h <= d \/ d+cap <= b) /\
  (!q. protected q ==> q+32 <= s.vs_alloca_next /\ (q+32 <= d \/ d+cap <= q)) /\
  (!q k. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (q,k) ==>
     k = 32 /\ (b+h <= q \/ q+32 <= b) /\ (d+cap <= q \/ q+32 <= d) /\
     (!x. protected x ==> x+32 <= q \/ q+32 <= x)) /\
  fresh_vars_wrt st s /\ fn_has_code st loop_st func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) \/
  (?c t slot. c <= maxn /\ c < dimword (:256) /\ p+32+c*asz <= h /\
    32+c*msz <= cap /\ mload (b+p) s = n2w c /\
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = loop_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~t.vs_halted /\
    fresh_vars_wrt loop_st t /\
    eval_operand ip t = SOME (n2w slot) /\ mload slot t = 0w /\
    eval_operand cnt t = SOME (n2w c) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    eval_operand dst t = SOME (n2w d) /\ eval_operand pos t = SOME (n2w p) /\
    eval_operand base_op t = SOME (n2w b) /\ eval_operand hi t = SOME (n2w h) /\
    mload d t = n2w c /\ mload (b+p) t = n2w c /\
    b+h <= t.vs_alloca_next /\ d+cap <= t.vs_alloca_next /\
    slot+32 <= t.vs_alloca_next /\ slot+32 < dimword (:256) /\
    (b+h <= slot \/ slot+32 <= b) /\ (d+cap <= slot \/ slot+32 <= d) /\
    (!q. protected q ==> q+32 <= slot \/ slot+32 <= q) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (slot,32) /\
    (!q. q <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas q = FLOOKUP s.vs_allocas q) /\
    alloca_room ctx func t /\ alloca_inv t /\ alloca_history func t /\
    mem_bytes_at b h t.vs_memory = mem_bytes_at b h s.vs_memory /\
    (!q. protected q ==> mload q t = mload q s) /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    abi_decode_footprint_frame [(d,cap);(slot,32)] s t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  `cs_extends st guard_st /\ cs_extends guard_st header_st /\ cs_extends header_st loop_st`
    by (rpt conj_tac >> pure_rewrite_tac[cs_extends_def] >> qexists_tac `[]` >>
        asm_rewrite_tac[APPEND, NOT_CONS_NIL, inst_extends_def] >>
        metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
  `fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
   fn_has_code header_st loop_st func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_decode_dynarray_position_prefix_path_mem >> disch_then (qspec_then `ctx` strip_assume_tac)
  >- (disj1_tac >> metis_tac[]) >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  `b+p < dimword (:256) /\ d < dimword (:256) /\ p+32 <= h /\ 32 <= cap` by decide_tac >>
  `eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `alloca_inv s1 /\ alloca_room ctx func s1` by
    (conj_tac >- (irule alloca_inv_fields >> metis_tac[]) >>
     irule alloca_room_fields >> metis_tac[]) >>
  `abi_decode_load MLOAD (n2w (b+p):bytes32) s1 = n2w c`
    by metis_tac[abi_decode_load_def, mload_def, w2n_n2w] >>
  `abi_decoder_operand_live guard_st.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_rewrite_tac[]) >>
  `b+h <= s1.vs_alloca_next /\ d+cap <= s1.vs_alloca_next /\
    (!q. protected q ==> q+32 <= s1.vs_alloca_next /\ (q+32 <= d \/ d+cap <= q)) /\
    (!q k. FLOOKUP s1.vs_allocas header_st.cs_next_id = SOME (q,k) ==>
     k = 32 /\ (b+h <= q \/ q+32 <= b) /\ (d+cap <= q \/ q+32 <= d) /\
     (!x. protected x ==> x+32 <= q \/ q+32 <= x))` by metis_tac[] >>
  drule_all nonbulk_header_index_path >> strip_tac >> rename1 `gas_path_mem ctx func s1 0 (OK t)` >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> `abi_decoder_operand_live guard_st.cs_next_var op` by
      (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_rewrite_tac[]) >>
     metis_tac[]) >>
  `c < dimword (:256) /\ 32+c*msz <= cap` by
    (`c*msz <= maxn*msz` by metis_tac[LE_MULT_RCANCEL] >> decide_tac) >>
  `mload (b+p) s = n2w c` by (qpat_x_assum `abi_decode_load MLOAD _ s = _` mp_tac >>
     qpat_x_assum `b+p < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_load_def, w2n_n2w]) >>
  `gas_path_mem ctx func s 0 (OK t)` by metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `abi_decode_footprint_frame [(d,cap);(slot,32)] s t` by (qpat_x_assum `abi_decode_footprint_frame _ s1 t` mp_tac >>
     qpat_x_assum `s1.vs_memory = _` mp_tac >>
     qpat_x_assum `s1.vs_call_ctx = _` mp_tac >>
     qpat_x_assum `s1.vs_data_section = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_footprint_frame_def]) >>
  `!q. protected q ==> mload q t = mload q s` by
    (rpt strip_tac >> qpat_x_assum `!q. protected q ==> mload q t = _` drule >>
     qpat_x_assum `s1.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[mload_def]) >>
  disj2_tac >> qexistsl_tac [`c`,`t`,`slot`] >> asm_rewrite_tac[] >> rpt conj_tac >> metis_tac[LESS_EQ_TRANS]
QED
