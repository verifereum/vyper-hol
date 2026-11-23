(* Passing post-read indexed element setup, without a child-validity premise. *)
Theory abiDecodeRejectIndexedPass
Ancestors
  decoderArraySetupPtr abiValidAllocatedResource abiMalformedTraversal
  abiDecoderIndexedAddress calldataDynOwned abiDecoderReentry
  emitHelperProps fragExec fragExecPtr fragGasOriginPtr venomExecSemantics
  venomState bodyPtrDefs ptrDiscipline finite_map pred_set words list arithmetic
  abiDecoderGuard abiDecoderComplexGuard abiDecoderVarSequence
  abiDecoderReentryPointer abiDecoderComplexHead abiEncoder compileEnv
  exprSimAbiDecodeArrayRuntimeSetup bodyFullBopWordSuccess bodyPtrBopScalarSeq
  bodyPtrBopScalarOutcome rich_list emitHelper venomInst exprLoweringProps
  abiDecoderReentryAddress abiDecoderRange abiDecoderDynamicLoopSetup placeMemoryCodeLayout
  entryDecoderHistoryFrame fragExecMem instMemFrontier memSafeRun fragGasCopyLoop fragGasSeqPtr
  fragGasCopySeqLiftProps
  abiMalformedConstructorContract abiMalformedBulkConstructor abiMalformedMemberSetup
  abiMalformedRecursiveInterface abiDecodePtrMemberFrame decoderGhostFramePtr fragGasOriginPtrLoop

Theorem indexed_destination_raw_frame[local]:
  !base_op. abi_decode_indexed_address base_op idx stride st = (out,en) /\
  run_inst_seq (emitted_insts st en) s = OK raw ==>
  raw = (s with vs_vars := raw.vs_vars)
Proof
  gen_tac >> simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  `inst_extends st en` by metis_tac[inst_extends_emit_op, inst_extends_trans] >>
  `EVERY (\i. (fresh_write_op i.inst_opcode \/ abi_decode_source_opcode i.inst_opcode) /\
              EVERY (\x. ~not_fresh_at st x) i.inst_outputs) (emitted_insts st en)` by
    (gvs[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     simp[freshWritesTheory.fresh_write_op_def, mk_inst_def,
          loweringStateRelDefsTheory.not_fresh_at_def]) >>
  drule_all abi_malformed_read_sequence_frame >> simp[]
QED

(* The raw reentry run determines the physical witness. The pointer proof
   certifies that same run at the fetched PC, not a replay with pruned vars. *)
Theorem indexed_pass_destination_cut[local]:
  !total. abi_decode_indexed_address (Var root) idx stride st = (out,en) /\
  lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s total /\
  eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var idx /\ not_fresh_at st root /\
  op_taint tn idx = {} /\ op_prov G idx = NONE /\
  32 + j * stride + stride <= total /\
  d + 32 + j * stride < dimword (:256) /\ stride < dimword (:256) /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code st en func /\ allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?raw u Gu tu child.
    run_inst_seq (emitted_insts st en) s = OK raw /\
    raw = (s with vs_vars := raw.vs_vars) /\
    u = (raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
    out = Var child /\ ptr_covers Gu tu child u stride /\
    eval_operand out u = SOME (n2w (d + 32 + j * stride)) /\
    abi_decoder_operand_live en.cs_next_var out /\
    fresh_vars_wrt ceiling u /\
    u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_data_section = s.vs_data_section /\ u.vs_halted = s.vs_halted /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op u = eval_operand op s) /\
    (!x. not_fresh_at st x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      FLOOKUP tu.t_var x = FLOOKUP tn.t_var x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
                   (s,G,tn) [] (OK u,Gu,tu))
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  `!x. idx = Var x ==> not_fresh_at st x` by
    metis_tac[calldata_operand_live_not_fresh] >>
  drule_all abi_decode_indexed_address_reentry >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  drule_all indexed_destination_raw_frame >> strip_tac >>
  drule_all indexed_destination_structure >> strip_tac >>
  `LENGTH en.cs_current_insts = 3 + s.vs_inst_idx` by
    (fs[inst_extends_def] >> decide_tac) >>
  drule_all indexed_destination_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  qexists `raw` >> qexists `raw with vs_inst_idx := LENGTH en.cs_current_insts` >>
  rename1 `ptr_covers Gu tu child _ stride` >> qexistsl [`Gu`,`tu`,`child`] >>
  gvs[abiEncoderPathPropsTheory.fresh_vars_wrt_inst_idx,
      cj 4 moduleLoweringPropsTheory.control_moves_keep_vars]
QED

(* The three lower-bound instructions can be evaluated on a pruned
   state; the reentry lemma transports that run to the physical state. *)
Theorem indexed_pass_ge_reentry[local]:
  abi_decode_ge_guard a b sa = ((),sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n vb <= w2n va /\
  abi_decoder_operand_live sa.cs_next_var a /\
  abi_decoder_operand_live sa.cs_next_var b /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      fresh_vars_wrt ceiling t /\ inst_extends sa sb /\
      (!op w. abi_decoder_operand_live sa.cs_next_var op /\
              eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     simp[abi_decode_ge_guard_def, comp_bind_def, emit_op_def, emit_void_def,
          comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
     strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]) >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  qabbrev_tac `clean = abi_decoder_prune_vars sa.cs_next_var s` >>
  `eval_operand a clean = SOME va /\ eval_operand b clean = SOME vb /\
   fresh_vars_wrt sa clean` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  qunabbrev_tac `clean` >>
  drule_all abi_decoder_sequence_reentry_prefix >> metis_tac[]
QED

(* Exact scalar certificate for the bounded suffix after the offset read.
   The intermediate states isolate the ADD, lower guard and head guard. *)
Theorem indexed_pass_indirect_code[local]:
  emit_op ADD [data;off] sa = (pos,sb) /\
  abi_decode_ge_guard pos data sb = ((),sc) /\
  abi_decode_complex_head_guard pos hi k sc = ((),sd) /\ hi <> Lit 0w ==>
  ?A. bop_scalar_seq {x | not_fresh_at sa x} {data;off;hi;Lit (n2w k)}
         (emitted_insts sa sd) A /\ pos IN A
Proof
  strip_tac >>
  gvs[abi_decode_ge_guard_def, abi_decode_complex_head_guard_def,
      compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
      emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  ntac 11 (simp[Once bop_scalar_seq_def, mk_inst_def]) >>
  simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem indexed_pass_indirect_reentry[local]:
  emit_op ADD [data;off] sa = (pos,sb) /\
  abi_decode_ge_guard pos data sb = ((),sc) /\
  abi_decode_complex_head_guard pos hi k sc = ((),sd) /\ hi <> Lit 0w /\
  eval_operand data s = SOME (n2w a) /\ eval_operand off s = SOME (n2w delta) /\
  eval_operand hi s = SOME (n2w L) /\
  abi_decoder_operand_live sa.cs_next_var data /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  a + delta + k <= L /\ L < dimword (:256) /\
  sd.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?t. run_inst_seq (emitted_insts sa sd) s = OK t /\ inst_extends sa sd /\
      fresh_vars_wrt ceiling t /\ eval_operand pos t = SOME (n2w (a+delta)) /\
      abi_decoder_operand_live sd.cs_next_var pos /\ sd.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  drule emit_op_next_var >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule loweringShapeRulesTheory.emit_op_facts >> metis_tac[]) >>
  `sc.cs_next_var = sb.cs_next_var + 2 /\ sc.cs_current_bb = sb.cs_current_bb` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     simp[abi_decode_ge_guard_def, comp_bind_def, comp_ignore_bind_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_return_def] >> strip_tac >> gvs[] >> decide_tac) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `sb.cs_next_var <= ceiling.cs_next_var /\ sc.cs_next_var <= ceiling.cs_next_var /\
   sc.cs_next_var <= sd.cs_next_var /\
   sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var` by
    gvs[] >>
  `?t1. run_inst_seq (emitted_insts sa sb) s = OK t1 /\ inst_extends sa sb /\
        eval_operand pos t1 = SOME (n2w (a+delta)) /\ fresh_vars_wrt ceiling t1 /\
        (!op. abi_decoder_operand_live sa.cs_next_var op ==>
              eval_operand op t1 = eval_operand op s)` by
    (drule abi_decoder_binary_reentry >> simp[] >>
     disch_then (qspecl_then [`s`,`ceiling`] mp_tac) >>
     simp[word_add_n2w] >> metis_tac[]) >>
  `abi_decoder_operand_live sb.cs_next_var pos` by metis_tac[abi_decoder_operand_live_emit] >>
  `abi_decoder_operand_live sb.cs_next_var data /\ abi_decoder_operand_live sb.cs_next_var hi /\
   abi_decoder_operand_live sc.cs_next_var pos /\ abi_decoder_operand_live sc.cs_next_var hi /\
   abi_decoder_operand_live sd.cs_next_var pos` by metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand data t1 = SOME (n2w a) /\ eval_operand hi t1 = SOME (n2w L)` by simp[] >>
  `w2n (n2w a : bytes32) <= w2n (n2w (a+delta) : bytes32)` by
    (`a + delta < dimword (:256) /\ a < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
  drule_all indexed_pass_ge_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sc) t1 = OK t2` >>
  `eval_operand pos t2 = SOME (n2w (a+delta)) /\ eval_operand hi t2 = SOME (n2w L)` by simp[] >>
  `?t. run_inst_seq (emitted_insts sc sd) t2 = OK t /\ fresh_vars_wrt ceiling t /\
       abi_decoder_address_frame sc.cs_next_var t2 t /\ inst_extends sc sd` by
    (irule abi_decoder_complex_guard_reentry >> metis_tac[]) >>
  `eval_operand pos t = SOME (n2w (a+delta))` by fs[abi_decoder_address_frame_def] >>
  `run_inst_seq (emitted_insts sa sc) s = OK t2 /\ inst_extends sa sc` by
    (irule abi_decode_sequence_chain >> qexistsl [`t1`,`sb`] >> simp[]) >>
  qexists `t` >> simp[] >> irule abi_decode_sequence_chain >>
  qexistsl [`t2`,`sc`] >> simp[]
QED

(* Certify the physical reentry run at its actual PC. *)
Theorem indexed_pass_scalar_path[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lower s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sa sb) s = OK raw ==>
  ?G' tn'.
    raw = (s with vs_vars := raw.vs_vars) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x raw = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn'))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[IS_PREFIX_APPEND, emitted_insts_def] >> simp[DROP_LENGTH_APPEND]) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all bop_scalar_seq_run >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`,`PG`,`ARB`] strip_assume_tac th) >>
  rename1 `inst_seq_ptr _ 0 ctx func PG G tn _ s Gf tnf` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >>
     qpat_assum `!fn PG D. _` (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >>
     rpt gen_tac >> strip_tac >> gen_tac >> drule_all bop_scalar_seq_outputs >> strip_tac >>
     conj_tac >- (irule below_frontier_no_ranges >> gvs[]) >>
     irule inst_dload_in_section_other >> gvs[]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
      emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     `MEM i (emitted_insts sa sb)` by simp[] >>
     irule dalloca_no_wrap_non_dalloca >>
     drule_all bop_scalar_seq_outputs >> simp[] >> strip_tac >> gvs[]) >>
  qexistsl [`Gf`,`tnf`] >> simp[lookup_var_def, op_taint_def] >>
  rpt gen_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  qpat_assum `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf`
    (qspec_then `D` assume_tac) >>
  drule_all run_inst_seq_origin_ptr_lift >> simp[]
QED

(* Execute and certify the passing bounded indirect checks on the physical
   post-read state. The same witness serves all gas horizons. *)
Theorem indexed_pass_indirect_cut[local]:
  emit_op ADD [data;off] sa = (pos,sb) /\
  abi_decode_array_pointer_guard pos data hi k sb = ((),sg) /\ hi <> Lit 0w /\
  eval_operand data s = SOME (n2w a) /\ eval_operand off s = SOME (n2w delta) /\
  eval_operand hi s = SOME (n2w L) /\
  abi_decoder_operand_live sa.cs_next_var data /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  a < dimword (:256) /\ delta < dimword (:256) /\ L < dimword (:256) /\
  ~(w2n (n2w (a+delta) : bytes32) < a \/
    L < w2n (n2w (a+delta) : bytes32) + k) /\
  sg.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sg func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ allocas_from lower s /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!op. op IN {data;off;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}) ==>
  ?u Gu tu.
    a+delta+k <= L /\
    inst_extends sa sg /\ sg.cs_current_bb = sa.cs_current_bb /\
    u = (s with <| vs_vars := u.vs_vars; vs_inst_idx := LENGTH sg.cs_current_insts |>) /\
    fresh_vars_wrt ceiling u /\ eval_operand pos u = SOME (n2w (a+delta)) /\
    abi_decoder_operand_live sg.cs_next_var pos /\
    op_prov Gu pos = NONE /\ op_taint tu pos = {} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      FLOOKUP tu.t_var x = FLOOKUP tn.t_var x /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\
    tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
                  (OK u,Gu,tu))
Proof
  strip_tac >>
  drule_all abi_array_pointer_check_bounds >> strip_tac >>
  `?sc. abi_decode_ge_guard pos data sb = ((),sc) /\
        abi_decode_complex_head_guard pos hi k sc = ((),sg)` by
    (qpat_x_assum `abi_decode_array_pointer_guard _ _ _ _ _ = _` mp_tac >>
     Cases_on `abi_decode_ge_guard pos data sb` >>
     gvs[abi_array_pointer_guard_phases, comp_ignore_bind_def, comp_bind_def] >>
     Cases_on `q` >> simp[]) >>
  drule_all indexed_pass_indirect_reentry >> strip_tac >>
  drule_all indexed_pass_indirect_code >> strip_tac >>
  `!op. op IN {data;off;hi;Lit (n2w k)} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (gen_tac >> simp[] >> strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all indexed_pass_scalar_path >>
  disch_then (qspec_then `PG` (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))) >>
  rename1 `run_inst_seq (emitted_insts sa sg) s = OK raw` >>
  qexistsl [`raw with vs_inst_idx := LENGTH sg.cs_current_insts`,`Gu`,`tu`] >>
  simp[abiEncoderPathPropsTheory.fresh_vars_wrt_inst_idx,
       cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >>
  qpat_x_assum `raw = _` (fn th => CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV th)))) >>
  simp[]
QED

Theorem indexed_pass_operand_frame:
  !arg. (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tu (Var x) = op_taint tn (Var x)) /\
  abi_decoder_operand_live sa.cs_next_var arg /\ t.vs_labels = s.vs_labels ==>
  eval_operand arg t = eval_operand arg s /\
  op_prov H arg = op_prov G arg /\ op_taint tu arg = op_taint tn arg
Proof
  Cases_on `arg` >> strip_tac >>
  gvs[calldata_operand_live_not_fresh, eval_operand_def, op_prov_def, op_taint_def]
QED

(* Re-establish the source-level entry at the same normalized PC used by
   the path. The only runtime writes in this remainder are to registers. *)
Theorem indexed_pass_child_entry[local]:
  abi_malformed_entry H ctx func cenv cx es sa sites dstid live
    (Var source) hi src (Var root) B L xs p d outsz s /\
  child_sites SUBSET sites /\ sa.cs_next_var <= child.cs_next_var /\
  u = (s with <| vs_vars := u.vs_vars; vs_inst_idx := LENGTH child.cs_current_insts |>) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  32 + j * mem_sz + mem_sz <= outsz /\ posN < dimword (:256) /\
  eval_operand pos u = SOME (n2w posN) /\
  eval_operand dst u = SOME (n2w (d+32+j*mem_sz)) /\
  abi_decoder_operand_live child.cs_next_var pos /\ abi_decoder_operand_live child.cs_next_var dst ==>
  abi_malformed_entry H ctx func cenv cx es child child_sites dstid live
    (Var source) hi pos dst B L xs posN (d+32+j*mem_sz) mem_sz u /\
  abi_malformed_resource_post ctx func cenv cx es sa.cs_next_var sites dstid s u
Proof
  strip_tac >>
  qhdtm_assum `abi_malformed_entry` (strip_assume_tac o REWRITE_RULE [abi_malformed_entry_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es sa.cs_next_var sites dstid s u` by
    (`abi_malformed_resource_post ctx func cenv cx es sa.cs_next_var sites dstid s s` by
       metis_tac[abi_malformed_resource_refl] >>
     irule abi_malformed_resource_register_update >> simp[] >>
     qexists `s with vs_inst_idx := LENGTH child.cs_current_insts` >>
     gvs[abi_malformed_resource_post_inst_idx, lookup_var_def]) >>
  simp[] >> irule abi_malformed_child_entry >> simp[] >>
  conj_tac >-
    (fs[] >> metis_tac[abi_decoder_operand_live_mono]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  qexistsl [`d`,`Var root`,`outsz`,`p`,`s`,`sites`,`src`,`sa`] >> simp[]
QED

(* sa is the post-read cursor; sg is the end of the optional pointer check.
   The operands are those returned by abi_decode_array_element_setup. *)
Theorem malformed_indexed_pass_joint:
  abi_malformed_entry H ctx func cenv cx es sa sites dstid live
    (Var source) hi src (Var root) B L xs p d outsz s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn root s outsz /\
  FST ops = idx /\ FST (SND ops) = pos /\
  abi_decode_indexed_address (Var root) idx mem_sz sg = (SND (SND ops),child) /\
  (if dec_info_needs_offset di then
     emit_op ADD [data;off] sa = (pos,sb) /\
     abi_decode_array_pointer_guard pos data hi stride sb = ((),sg) /\
     fn_has_code sa sg func /\
     eval_operand data s = SOME (n2w (p+32)) /\ eval_operand off s = SOME (n2w delta) /\
     abi_decoder_operand_live sa.cs_next_var data /\
     p+32 < dimword (:256) /\ delta < dimword (:256) /\
     ~(w2n (n2w (p+32+delta) : bytes32) < p+32 \/
       L < w2n (n2w (p+32+delta) : bytes32) + stride) /\
     (!op. op IN {data;off;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
     posN = p+32+delta
   else sg = sa /\ posN = p+32+j*stride /\ posN < dimword (:256) /\
     eval_operand pos s = SOME (n2w posN) /\ abi_decoder_operand_live sa.cs_next_var pos /\
     op_prov G pos = NONE /\ op_taint tn pos = {}) /\
  eval_operand idx s = SOME (n2w j) /\ abi_decoder_operand_live sa.cs_next_var idx /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  32 + j*mem_sz + mem_sz <= outsz /\ child_sites SUBSET sites /\
  sa.cs_next_var <= sg.cs_next_var /\ sg.cs_next_var <= ceiling.cs_next_var /\
  child.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sg child func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lower s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gu tu q.
    abi_malformed_entry H ctx func cenv cx es child child_sites dstid live
      (Var source) hi (FST (SND ops)) (SND (SND ops)) B L xs posN (d+32+j*mem_sz) mem_sz u /\
    abi_malformed_resource_post ctx func cenv cx es sa.cs_next_var sites dstid s u /\
    abi_decode_ptr_window Gu tu u source (n2w B) L /\ ptr_covers Gu tu root u outsz /\
    SND (SND ops) = Var q /\ ptr_covers Gu tu q u mem_sz /\
    eval_operand (SND (SND ops)) u = SOME (n2w (d+32+j*mem_sz)) /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    abi_decoder_operand_live child.cs_next_var (FST ops) /\
    op_prov Gu (FST ops) = NONE /\ op_taint tu (FST ops) = {} /\
    eval_operand (FST (SND ops)) u = SOME (n2w posN) /\
    op_prov Gu (FST (SND ops)) = NONE /\ op_taint tu (FST (SND ops)) = {} /\
    fresh_vars_wrt ceiling u /\ ~u.vs_halted /\ allocas_from lower u /\
    u.vs_current_bb = child.cs_current_bb /\ u.vs_inst_idx = LENGTH child.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      FLOOKUP tu.t_var x = FLOOKUP tn.t_var x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
                  (s,G,tn) [] (OK u,Gu,tu))
Proof
  strip_tac >>
  qhdtm_assum `abi_malformed_entry` (strip_assume_tac o REWRITE_RULE [abi_malformed_entry_def]) >>
  `L < dimword (:256) /\ d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256)` by
    (fs[abi_malformed_allocated_window_def] >> decide_tac) >>
  `not_fresh_at sa source /\ not_fresh_at sa root /\
   abi_decoder_operand_live sa.cs_next_var hi` by fs[calldata_operand_live_not_fresh] >>
  `?v Gv tv.
     v = (s with <| vs_vars := v.vs_vars; vs_inst_idx := LENGTH sg.cs_current_insts |>) /\
     v.vs_current_bb = sg.cs_current_bb /\ fresh_vars_wrt ceiling v /\
     posN < dimword (:256) /\ eval_operand pos v = SOME (n2w posN) /\
     abi_decoder_operand_live sg.cs_next_var pos /\ op_prov Gv pos = NONE /\ op_taint tv pos = {} /\
     (!x. not_fresh_at sa x ==>
       lookup_var x v = lookup_var x s /\ FLOOKUP Gv x = FLOOKUP G x /\
       FLOOKUP tv.t_var x = FLOOKUP tn.t_var x /\ op_taint tv (Var x) = op_taint tn (Var x)) /\
     tv.t_mem = tn.t_mem /\ tv.t_stor = tn.t_stor /\ tv.t_trans = tn.t_trans /\ tv.t_imm = tn.t_imm /\
     (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
                    (s,G,tn) [] (OK v,Gv,tv))` by
    (Cases_on `dec_info_needs_offset di` >>
     qpat_x_assum `if _ then _ else _` mp_tac >> pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac
     >- (drule_all indexed_pass_indirect_cut >>
         disch_then (qspec_then `PG` strip_assume_tac) >>
         rename1 `op_prov Gv pos = NONE` >> rename1 `op_taint tv pos = {}` >>
         rename1 `eval_operand pos v = SOME _` >>
         `v.vs_current_bb = sg.cs_current_bb` by
           (qpat_assum `v = s with <|vs_vars := v.vs_vars; vs_inst_idx := _|>`
              (fn th => once_rewrite_tac[th]) >> simp[]) >>
         qexistsl [`v`,`Gv`,`tv`] >> simp[] >> decide_tac)
     >> qexistsl [`s`,`G`,`tn`] >> simp[gas_origin_ptr_path_rules] >>
        qpat_x_assum `s.vs_inst_idx = _` (rewrite_tac o single o SYM) >> simp[]) >>
  `v.vs_labels = s.vs_labels /\ v.vs_inst_idx = LENGTH sg.cs_current_insts /\
   ~v.vs_halted /\ allocas_from lower v` by
    ((qpat_assum `v = s with <|vs_vars := v.vs_vars; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >> simp[allocas_from_def] >> (gvs[allocas_from_def]))) >>
  `lookup_var root v = SOME (n2w d)` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `root` mp_tac) >>
     simp[GSYM eval_operand_def]) >>
  `ptr_covers Gv tv root v outsz` by
    (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `root` mp_tac) >> simp[]) >>
  `eval_operand idx v = SOME (n2w j) /\ op_prov Gv idx = NONE /\ op_taint tv idx = {}` by
    (`!x. not_fresh_at sa x ==>
        lookup_var x v = lookup_var x s /\ FLOOKUP Gv x = FLOOKUP G x /\
        op_taint tv (Var x) = op_taint tn (Var x)` by metis_tac[] >>
     drule indexed_pass_operand_frame >>
     disch_then (qspec_then `idx` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live sg.cs_next_var idx` by metis_tac[abi_decoder_operand_live_mono] >>
  `not_fresh_at sg root` by fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  drule indexed_destination_structure >> strip_tac >>
  `allocas_below_fmp v = allocas_below_fmp s` by
    (qpat_assum `v = s with <|vs_vars := v.vs_vars; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by metis_tac[] >>
  drule_all indexed_pass_destination_cut >>
  disch_then (qspec_then `PG`
    (qx_choose_then `raw` (qx_choose_then `u` (qx_choose_then `Gu`
      (qx_choose_then `tu` (qx_choose_then `q` strip_assume_tac)))))) >>
  `u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH child.cs_current_insts|>` by
    (qpat_assum `u = raw with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `raw = v with vs_vars := raw.vs_vars` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `v = s with <|vs_vars := v.vs_vars; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
     FLOOKUP tu.t_var x = FLOOKUP tn.t_var x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sg x` by fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sg x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `u.vs_labels = v.vs_labels` by
    (qpat_assum `u = raw with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `raw = v with vs_vars := raw.vs_vars` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sg x ==>
        lookup_var x u = lookup_var x v /\ FLOOKUP Gu x = FLOOKUP Gv x /\
        op_taint tu (Var x) = op_taint tv (Var x)` by metis_tac[] >>
  drule indexed_pass_operand_frame >>
  disch_then (fn th => qspec_then `idx` mp_tac th >> qspec_then `pos` mp_tac th) >>
  simp[] >> rpt strip_tac >>
  `abi_decoder_operand_live child.cs_next_var idx /\
   abi_decoder_operand_live child.cs_next_var pos /\ sa.cs_next_var <= child.cs_next_var` by
    metis_tac[abi_decoder_operand_live_mono, LESS_EQ_TRANS] >>
  `abi_malformed_entry H ctx func cenv cx es child child_sites dstid live
       (Var source) hi pos (SND (SND ops)) B L xs posN (d+32+j*mem_sz) mem_sz u /\
   abi_malformed_resource_post ctx func cenv cx es sa.cs_next_var sites dstid s u` by
    (`!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by metis_tac[] >>
     `eval_operand pos u = SOME (n2w posN)` by simp[] >>
     MATCH_MP_TAC indexed_pass_child_entry >> metis_tac[]) >>
  `ptr_covers Gu tu root u outsz` by
    (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (qspec_then `root` mp_tac) >> simp[]) >>
  `abi_decode_ptr_window Gu tu u source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (qspec_then `source` strip_assume_tac) >>
     metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (rpt gen_tac >>
     qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK v,Gv,tv)`
       (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_x_assum `!D explicit. gas_origin_ptr_path _ (v,Gv,tv) [] (OK u,Gu,tu)`
       (qspecl_then [`D`,`explicit`] mp_tac) >>
     rpt disch_tac >>
     pop_assum (fn a => pop_assum (fn b =>
       POP_ASSUM_LIST kall_tac >> mp_tac a >> mp_tac b)) >>
     metis_tac[gas_origin_ptr_path_append,APPEND]) >>
  `s.vs_current_bb = child.cs_current_bb` by
    (`v.vs_current_bb = s.vs_current_bb` by
       (qpat_assum `v = s with <|vs_vars := v.vs_vars; vs_inst_idx := _|>`
          (fn th => once_rewrite_tac[th]) >> simp[]) >>
     fs[same_blocks_def]) >>
  `u.vs_current_bb = child.cs_current_bb /\ u.vs_inst_idx = LENGTH child.cs_current_insts /\
   u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u = s with <|vs_vars := u.vs_vars; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  `allocas_from lower u` by
    (rewrite_tac[allocas_from_def] >>
     qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `allocas_from lower s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qexistsl [`u`,`Gu`,`tu`] >> gvs[]
QED
