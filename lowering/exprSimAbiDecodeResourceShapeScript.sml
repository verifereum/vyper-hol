Theory exprSimAbiDecodeResourceShape
Ancestors
  exprSimAbiDecodeResourceMutual exprSimAbiDecodeFramed exprSimAbiDecodeResourcePrims
  exprSimAbiDecodeResource exprSimAbiDecodeShape exprSimAbiDecodeTraceSafe
  exprSimAbiDecodeTrace exprSimAbiGasBridge builtinAbi abiEncoder compileEnv
  emitHelper context venomInst pred_set sorting list fragExec

Theorem decode_framed_lower:
  data <> Label ex ==>
  decode_framed ex (lower_abi_decode data di mn mx msz) (\v. v <> Label ex)
Proof
  strip_tac >> rewrite_tac[lower_abi_decode_def] >>
  ntac 2 (match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
    conj_tac >- (irule decode_straight_framed >> simp[decode_straight_emit_op]) >>
    rpt strip_tac >> gvs[]) >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac
  >- (irule decode_straight_framed >> Cases_on `mn = mx` >> simp[] >>
      rpt (match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
        conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[]) >>
      simp[decode_straight_emit_void]) >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\b. b.buf_operand <> Label ex` >>
  conj_tac >- (irule decode_straight_framed >> simp[decode_straight_alloc_buffer]) >>
  rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- (irule decode_framed_return >> simp[]) >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_framed_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- simp[decode_framed_to_buf] >> irule decode_framed_return >> simp[]
QED

Theorem decode_resource_shape:
  decode_resource_run ex P m sa out sb Q ==>
  cs_extends sa sb /\ frag_ops_free sa sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  strip_tac >> drule decode_resource_run_trace >> strip_tac >>
  `PERM (frag_code sa sb) (decode_instructions es)` by
    metis_tac[decode_replay_frag_code_history] >>
  fs[decode_trace_safe_def] >>
  conj_tac >- metis_tac[decode_history_extends, decode_replay_extends] >>
  conj_tac >- metis_tac[frag_ops_free_def, PERM_EVERY] >>
  conj_tac >- metis_tac[PERM_MAP, ALL_DISTINCT_PERM] >>
  metis_tac[decode_replay_final_label_history]
QED

Theorem decode_resource_gas_free:
  decode_resource_run ex P m sa out sb Q /\ sa.cs_blocks = sb.cs_blocks /\
  ex = sa.cs_current_bb ==> frag_gas_free sa sb
Proof
  strip_tac >> drule decode_resource_run_trace >> strip_tac >>
  `PERM (frag_code sa sb) (decode_instructions es)` by
    metis_tac[decode_replay_frag_code_history] >>
  `sa.cs_blocks = (decode_replay es sa).cs_blocks` by
    (qpat_x_assum `sb = _` (mp_tac o AP_TERM ``\s:compile_state. s.cs_blocks``) >>
     simp[decode_history_def] >> metis_tac[]) >>
  `decode_switches es = []` by
    (mp_tac (Q.SPECL [`es`, `sa`] decode_replay_labels_raw) >>
     disch_then (mp_tac o AP_TERM ``LENGTH : string list -> num``) >> simp[] ) >>
  fs[decode_trace_safe_def] >>
  rewrite_tac[frag_gas_free_def] >> conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      `MEM i (decode_instructions es)` by metis_tac[PERM_MEM_EQ] >>
      first_x_assum drule >> simp[] >> metis_tac[]) >>
  simp[emitted_blocks_def]
QED
