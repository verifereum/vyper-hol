(* Site-parametric leaf effects reuse the existing concrete sequence execution. *)
Theory abiSiteEncoderLeaves
Ancestors
  abiSiteEncoderContract abiSiteAllocation abiScratchLeafEffect abiScratchFootprint
  abiEncoderSequence abiDecoderFootprint abiDecoderFrame abiDecoderContract
  abiDecoderPrimitiveLoopFrames
  abiDecoderLoop abiDecoderReentry abiEncoderReentryLeaves abiEncoderLeafCode
  abiEncoderAdmissible abiEncoderBytes abiEncoderBytesCode abiEncoderInput
  abiEncoderComplexDynamic abiSiteEncoderComplex abiEncoder venomState compileEnv
  valueEncoding contractABI words list arithmetic

Theorem abi_site_leaf_effect:
  abi_site_budget A b cap s /\ fresh_vars_wrt limit_st t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  abi_decode_frame d sz s t /\ t.vs_halted = s.vs_halted /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  abi_site_encoder_effect A lo hi next limit_st d sz b cap s t
Proof
  strip_tac >>
  `(abi_site_budget A b cap t <=> abi_site_budget A b cap s)` by
    (irule abi_site_budget_fields >> simp[]) >>
  `s.vs_alloca_next <= b+cap` by
    (qpat_assum `abi_site_budget _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_site_budget_def] >> strip_tac >> decide_tac) >>
  `abi_scratch_evolution A b cap s t` by
    (rw[abi_scratch_evolution_def] >> gvs[]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (A INTER abi_decoder_ids lo hi) b cap s) s t` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`d`, `sz`] >> simp[]) >>
  asm_simp_tac bool_ss [abi_site_encoder_effect_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_site_sequence_post_effect:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  abi_site_budget A b cap initial ==>
  abi_site_encoder_effect A st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def] >> strip_tac >>
  irule abi_site_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED

Theorem abi_site_leaf_reach:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  (?raw. run_inst_seq (emitted_insts st st') initial = OK raw /\
    abi_encoder_sequence_post at av out st limit_st d initial raw) /\
  fn_has_code st st' func /\ abi_site_budget A b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_site_encoder_effect A st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_sequence_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_site_encoder_effect A st.cs_next_id st'.cs_next_id st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual` by
    (irule abi_site_sequence_post_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `out` >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> fs[abi_encoder_sequence_post_def, Excl "enc_def"]
QED

Theorem abi_site_encoder_word:
  abi_site_encoder AbiPrimWord
Proof
  simp_tac bool_ss [abi_site_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_site_encoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_encoder_input_def]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_word_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK raw` >>
  `abi_encoder_sequence_post at av out start limit_st d initial raw` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  mp_tac (Q.INST [`ei` |-> `AbiPrimWord`, `st` |-> `start`, `st'` |-> `end_st`]
    abi_encode_static_leaf_shape) >>
  (impl_tac >- simp[abi_encoder_static_leaf_def]) >> strip_tac >>
  irule abi_site_leaf_reach >> simp[] >> qexists_tac `raw` >> simp[]
QED

Theorem abi_site_encoder_copy:
  abi_site_encoder (AbiCopy sz)
Proof
  simp_tac bool_ss [abi_site_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_site_encoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_encoder_input_def]) >>
  `LENGTH (enc at av) = sz` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_copy_iff]) >>
     drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK raw` >>
  `abi_encoder_sequence_post at av out start limit_st d initial raw` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  mp_tac (Q.INST [`ei` |-> `AbiCopy sz`, `st` |-> `start`, `st'` |-> `end_st`]
    abi_encode_static_leaf_shape) >>
  (impl_tac >- simp[abi_encoder_static_leaf_def]) >> strip_tac >>
  irule abi_site_leaf_reach >> simp[] >> qexists_tac `raw` >> simp[]
QED

Theorem abi_site_encoder_bytes:
  abi_site_encoder (AbiBytestring maxlen)
Proof
  simp_tac bool_ss [abi_site_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_site_encoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_encoder_input_def]) >>
  `sb < dimword (:256)` by decide_tac >>
  drule_at (Pos (el 2)) abi_encoder_bytes_sequence >> disch_then drule >>
  disch_then (qspecl_then [`limit_st`, `d`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac []) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK raw` >>
  `abi_encoder_sequence_post at av out start limit_st d initial raw` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  drule abi_encode_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start end_st)` by fs[EVERY_CONJ] >>
  irule abi_site_leaf_reach >> simp[] >> qexists_tac `raw` >> simp[]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if not (null (Thm.hyp th)) orelse not (null axs) orelse
       List.exists (fn s => s <> "DISK_THM") ors
    then raise Fail ("Finite-site leaf dependency: " ^ name) else ()
  end) (DB.thms "abiSiteEncoderLeaves");
