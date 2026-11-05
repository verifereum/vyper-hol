(* Concrete primitive encoder instruction checks. *)
Theory bodyPtrAbiEncodeWordChecks
Ancestors
  bodyPtrAbiEncodePrimitive typedCopyPtr ghostPcTransportPtr
  fragGasSeqPtr fragGasPathPtr fragExecPtr venomExecSemantics venomInst venomState
  ptrDiscipline ptrSafeRun finite_map
  abiEncoderReentryLeaves emitHelperProps emitHelper compileEnv abiDecoderReentry
  abiDecoderContract exprLoweringProps

Theorem abi_encode_mstore_inst_idx[local]:
  mstore off w (s with vs_inst_idx := k) =
  (mstore off w s) with vs_inst_idx := k
Proof
  simp[mstore_def]
QED

Theorem abi_encode_word_sequence_checks:
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\ tmp <> dst /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst;Var tmp] []] s Gf tnf /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> FLOOKUP Gf p = FLOOKUP G p /\
                          op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all mload_then_mstore_ok >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `id`, `0`] strip_assume_tac) >>
  `ptr_inst_ok D 0 0 ctx fn
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (mk_inst (id+1) MSTORE [Var dst;Var tmp] [])
    (update_var tmp (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_mstore >> simp[] >> conj_tac
     >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]) >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst;Var tmp] [])
    (update_var tmp (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (mstore (w2n b) (mload (w2n a) s)
      (update_var tmp (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  simp[inst_seq_ptr_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def,
       eval_operand_def, eval_operands_def] >>
  asm_rewrite_tac[GSYM mk_inst_def] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `step_prov PG G1 store stored` >>
  qmatch_goalsub_abbrev_tac `step_taint store loaded stored tn1` >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `loaded`] >>
     irule mload_ghost_clean >> simp[eval_operand_def]) >>
  `lookup_var dst loaded = SOME b /\
   eval_operand (Var tmp) loaded = SOME (mload (w2n a) s)` by
    (simp[Abbr `loaded`, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G1`, `id+1`] mp_tac) >>
  simp[GSYM mstore_def, Abbr `store`, Abbr `stored`] >>
  simp[abi_encode_mstore_inst_idx] >> strip_tac >> simp[op_taint_def] >>
  rpt strip_tac >> simp[Abbr `G1`, Abbr `tn1`, Abbr `loaded`,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    set_var_taint_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    op_taint_def]
QED

Theorem abi_encode_word_emitted_code:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id MLOAD [src]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE
       [dst;Var (STRING #"%" (toString st.cs_next_var))] []]
Proof
  strip_tac >> drule abi_encode_word_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem abi_encode_word_emitted_checks:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord st = (out,st') /\
  not_fresh_at st dst /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s Gf tnf /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at st p ==> FLOOKUP Gf p = FLOOKUP G p /\
                          op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule abi_encode_word_emitted_code >> strip_tac >>
  `STRING #"%" (toString st.cs_next_var) <> dst` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all abi_encode_word_sequence_checks >>
  disch_then (qspecl_then [`st.cs_next_id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[] >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString st.cs_next_var)` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  metis_tac[]
QED

Theorem abi_encode_word_checked_ptr_path:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord st = (out,st') /\
  eval_operand (Var src) s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  (!i. sb <= i /\ i < sb + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
      Gf tnf (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    eval_operand out t = SOME 32w /\
    mem_bytes_at db 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory /\
    fresh_vars_wrt limit_st t /\
    tnf.t_mem = tn.t_mem DIFF {i | db <= i /\ i < db + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at st p ==> FLOOKUP Gf p = FLOOKUP G p /\
                          op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `not_fresh_at st dst` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w db)` by
    fs[eval_operand_def] >>
  `!i. w2n (n2w sb:bytes32) <= i /\ i < w2n (n2w sb:bytes32) + 32 ==>
       i NOTIN tn.t_mem` by simp[wordsTheory.w2n_n2w] >>
  drule_all abi_encode_word_emitted_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all abi_encode_word_reentry_ptr_path >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[wordsTheory.w2n_n2w]
QED
