(* Uniform memory execution for scratch-free decoder constructors. *)
Theory abiDecodeMemNoScratch
Ancestors
  abiDecodeMemPrimitiveReentry abiDecodeMemBytesReentry abiDecodeMemBulkReentry
  abiDecodeMemPrimitive abiDecoderBytesFrame abiDecoderBytesPhases abiDecoderBulk
  abiDecoderBulkExecute abiDecoderContract abiDecoderClamp abiDecoderReentry
  abiDecoderFrame abiDecoderFrameCompose abiDecoderVarSequence
  moduleLoweringProps localPtrsProps freshWrites
  entryDecoderHistoryFrame entrySinkExtraction allocaHistoryFragment
  fragGasPathMem fragGasSeqMem fragGasMode fragGasSeqAbort fragExecMem fragExec
  bodyUnopFragMemory exprLoweringProps loweringStateRelDefs
  abiEncoder emitHelperProps compileEnv venomExecSemantics venomState venomInst
  venomMemDefs valueEncodingProps words arithmetic list rich_list

Theorem abi_decode_mem_noscratch_sequence[local]:
  compile_abi_decode_to_buf dst src MLOAD bop hi di st = ((),en) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\ abi_decoder_operand_live st.cs_next_var hi /\
  eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand bop s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  bop <> Lit 0w /\ hi <> Lit 0w /\ p < dimword (:256) /\
  B+H < dimword (:256) /\ B+H <= s.vs_alloca_next /\
  d+N < dimword (:256) /\ d+N <= s.vs_alloca_next /\
  ((?clamp. di = DecPrimWord clamp /\ N = 32 /\ p+32 <= H) \/
   (?n. di = DecBytestring n /\ N = 32+32*((n+31) DIV 32)) \/
   (?ei asz msz maxn. di = DecDynArray ei asz msz F maxn /\ ~dec_info_needs_clamp ei /\
     asz = msz /\ N = 32+maxn*msz /\ maxn < dimword (:256) /\ maxn*asz < dimword (:256))) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\
  ((?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
   (?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    abi_decode_frame d N s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?clamp. _) \/ _` strip_assume_tac
  >- suspend "word" >- suspend "bytes" >> suspend "bulk"
QED
Resume abi_decode_mem_noscratch_sequence[word]:
  gvs[] >>
  `B+p < dimword (:256) /\ B+p+32 <= s.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `src`, `bop` |-> `bop`, `hi` |-> `hi`,
    `clamp` |-> `clamp`, `st` |-> `st`, `en` |-> `en`, `limit_st` |-> `limit_st`,
    `s` |-> `s`, `p` |-> `p`, `B` |-> `B`, `d` |-> `d`]
    abi_decode_primitive_reentry_sequence_mem) >> simp[] >>
  Cases_on `abi_clamp_ok clamp (mload (B+p) s)` >> simp[] >> metis_tac[]
QED
Resume abi_decode_mem_noscratch_sequence[bytes]:
  gvs[] >>
  mp_tac (Q.INST [`dst` |-> `dst`, `pos` |-> `src`, `base_op` |-> `bop`, `hi` |-> `hi`,
    `n` |-> `n`, `st` |-> `st`, `en` |-> `en`, `limit_st` |-> `limit_st`,
    `s` |-> `s`, `p` |-> `p`, `b` |-> `B`, `h` |-> `H`, `d` |-> `d`]
    abi_decode_bytes_reentry_sequence_mem) >> simp[]
QED
Resume abi_decode_mem_noscratch_sequence[bulk]:
  gvs[] >>
  `maxn*asz < dimword (:256)` by (simp[MULT_COMM] >> decide_tac) >>
  mp_tac (Q.INST [`dst` |-> `dst`, `pos` |-> `src`, `base_op` |-> `bop`, `hi` |-> `hi`,
    `ei` |-> `ei`, `msz` |-> `asz`, `maxn` |-> `maxn`,
    `st` |-> `st`, `en` |-> `en`, `limit_st` |-> `limit_st`,
    `s` |-> `s`, `p` |-> `p`, `b` |-> `B`, `h` |-> `H`, `d` |-> `d`]
    abi_decode_bulk_reentry_sequence_mem) >> simp[MULT_COMM]
QED
Finalise abi_decode_mem_noscratch_sequence[local]

Theorem abi_decode_mem_noscratch_shape[local]:
  compile_abi_decode_to_buf dst src MLOAD bop hi di st = ((),en) /\
  ((?clamp. di = DecPrimWord clamp /\ N = 32 /\ p+32 <= H) \/
   (?n. di = DecBytestring n /\ N = 32+32*((n+31) DIV 32)) \/
   (?ei asz msz maxn. di = DecDynArray ei asz msz F maxn /\ ~dec_info_needs_clamp ei /\
     asz = msz /\ N = 32+maxn*msz /\ maxn < dimword (:256) /\ maxn*asz < dimword (:256))) ==>
  en.cs_blocks = st.cs_blocks /\ en.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts en.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `(?clamp. _) \/ _` strip_assume_tac
  >- (gvs[] >> drule abi_decode_primitive_shape >> strip_tac >> simp[IS_PREFIX_APPEND])
  >- (gvs[] >> drule_all abi_decode_bytes_position_shape >> strip_tac >>
      drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
      fs[inst_extends_def, EVERY_MEM] >> rpt strip_tac >> res_tac >>
      Cases_on `i.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def]) >>
  gvs[] >> drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  Cases_on `i.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_mem_noscratch_frame[local]:
  compile_abi_decode_to_buf dst src MLOAD bop hi di st = ((),en) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\ abi_decoder_operand_live st.cs_next_var hi /\
  eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand bop s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  bop <> Lit 0w /\ hi <> Lit 0w /\ p < dimword (:256) /\
  B+H < dimword (:256) /\ B+H <= s.vs_alloca_next /\
  d+N < dimword (:256) /\ d+N <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ((?clamp. di = DecPrimWord clamp /\ N = 32 /\ p+32 <= H) \/
   (?n. di = DecBytestring n /\ N = 32+32*((n+31) DIV 32)) \/
   (?ei asz msz maxn. di = DecDynArray ei asz msz F maxn /\ ~dec_info_needs_clamp ei /\
     asz = msz /\ N = 32+maxn*msz /\ maxn < dimword (:256) /\ maxn*asz < dimword (:256))) ==>
  (?t. gas_path_mem ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    abi_decode_frame d N s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t) \/
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_mem_noscratch_shape >> strip_tac >>
  drule_all abi_decode_mem_noscratch_sequence >> strip_tac
  >- suspend "reject" >> suspend "accept"
QED
Resume abi_decode_mem_noscratch_frame[reject]:
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Resume abi_decode_mem_noscratch_frame[accept]:
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st en)) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st en) = LENGTH en.cs_current_insts` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  disj1_tac >> qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, fresh_vars_wrt_def, abi_decode_frame_def] >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def] >> metis_tac[]
QED
Finalise abi_decode_mem_noscratch_frame[local]

Theorem abi_decode_mem_noscratch:
  !(protected:num -> bool).
  compile_abi_decode_to_buf dst src MLOAD bop hi di st = ((),en) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ alloca_room ctx func s /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var hi /\
  eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand bop s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w H) /\
  bop <> Lit 0w /\ hi <> Lit 0w /\ p < dimword (:256) /\
  B+H < dimword (:256) /\ B+H <= s.vs_alloca_next /\
  d+N < dimword (:256) /\ d+N <= s.vs_alloca_next /\
  (B+H <= d \/ d+N <= B) /\
  (!q. protected q ==> q+32 <= s.vs_alloca_next /\ (q+32 <= d \/ d+N <= q)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ((?clamp. di = DecPrimWord clamp /\ N = 32 /\ p+32 <= H) \/
   (?n. di = DecBytestring n /\ N = 32+32*((n+31) DIV 32)) \/
   (?ei asz msz maxn.
      di = DecDynArray ei asz msz F maxn /\ ~dec_info_needs_clamp ei /\
      asz = msz /\ N = 32+maxn*msz /\ maxn < dimword (:256) /\
      maxn*asz < dimword (:256))) ==>
  (?t. gas_path_mem ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    mem_bytes_at B H t.vs_memory = mem_bytes_at B H s.vs_memory /\
    (!q. protected q ==> mload q t = mload q s) /\
    abi_decode_frame d N s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\ alloca_inv t /\ alloca_room ctx func t) \/
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  qx_gen_tac `protected` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_mem_noscratch_frame >>
  disch_then (qspec_then `ctx` strip_assume_tac)
  >- (disj1_tac >> qexists_tac `t` >> simp[] >>
      `alloca_inv t /\ alloca_room ctx func t` by
        (conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
         irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
      simp[] >> conj_tac
      >- (fs[abi_decode_frame_def, venomMemDefsTheory.regions_disjoint_def] >>
          first_x_assum irule >> simp[]) >>
      rpt strip_tac >>
      irule abi_decode_footprint_frame_mload >> qexists_tac `[(d,N)]` >>
      simp[GSYM abi_decode_frame_footprint, abi_footprint_disjoint_def] >>
      qpat_x_assum `!q. protected q ==> _` (qspec_then `q` mp_tac) >>
      simp[ADD_COMM]) >>
  metis_tac[]
QED
