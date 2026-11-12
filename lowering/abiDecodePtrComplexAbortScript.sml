Theory abiDecodePtrComplexAbort
Ancestors
  abiDecodePtrComplexHeader abiDecodePtrScalarAbort
  bodyPtrHashBuiltinsShaTail bodyPtrBopScalarSeq
  abiDecodePtrMemberInterface exprLoweringProps
  stmtReasonLitFragMemory emitHelperProps ptrDiscipline words pred_set list

Theorem abi_decode_complex_header_abort:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf j. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf
    (Abort a (u with vs_inst_idx := j))
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x}
    {pos;hi;Lit (n2w static_sz)} (emitted_insts sa sb) B` by
    (irule abi_decode_complex_header_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;hi;Lit (n2w static_sz)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac[IN_INSERT, NOT_IN_EMPTY] >> rpt strip_tac >>
     gvs[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def, emitted_insts_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  drule_all hash_inst_seq_abort_zero_path >> metis_tac[]
QED
