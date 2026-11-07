(* Concrete suffix-retaining STOP observers for recursive decoder prefixes. *)
Theory entryConcreteDecoderPrefix
Ancestors
  entryDecoderCfgInventory entryDecoderCfgRules entryDecoderCfgProducer
  entryStopObserverConstruction entryStopRegionAgreement entryStopStepTransport
  entryValidDecoderObserver abiEncoderObserver abiDecoderValidContract
  abiDecoderContract fragExec compileEnv venomExecSemantics venomInst

Theorem entry_concrete_stop_regions:
  entry_cfg_preserves c /\ compile_state_ok start /\ compile_state_ok end_st /\
  ~block_is_terminated start /\ c start = (v,end_st) /\
  fn_has_code start end_st func /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions <= LENGTH end_st.cs_current_insts /\
  LENGTH end_st.cs_current_insts <= LENGTH bb.bb_instructions /\
  obs = entry_stop_function end_st.cs_current_bb (LENGTH end_st.cs_current_insts) iid func ==>
  fn_has_code start end_st obs /\
  lookup_block end_st.cs_current_bb obs.fn_blocks =
    SOME (entry_stop_block (LENGTH end_st.cs_current_insts) iid bb) /\
  get_instruction (entry_stop_block (LENGTH end_st.cs_current_insts) iid bb)
    (LENGTH end_st.cs_current_insts) = SOME (mk_inst iid STOP [] []) /\
  observer_region_closed ctx obs
    (end_st.cs_current_bb,LENGTH end_st.cs_current_insts)
    (entry_emitted_positions start end_st) /\
  observer_region_safe obs
    (end_st.cs_current_bb,LENGTH end_st.cs_current_insts)
    (entry_emitted_positions start end_st) /\
  (start.cs_current_bb,LENGTH start.cs_current_insts) IN entry_emitted_positions start end_st /\
  region_code_agrees obs func
    (end_st.cs_current_bb,LENGTH end_st.cs_current_insts)
    (entry_emitted_positions start end_st)
Proof
  strip_tac >>
  `fn_has_code start end_st obs` by metis_tac[entry_stop_has_code_ok] >>
  drule_all entry_stop_function_cut >> disch_then (qspec_then `iid` strip_assume_tac) >>
  `!b. lookup_block end_st.cs_current_bb obs.fn_blocks = SOME b ==>
    ?id. get_instruction b (LENGTH end_st.cs_current_insts) = SOME (mk_inst id STOP [] [])` by
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all entry_cfg_preserves_observer_regions >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `region_code_agrees obs func
    (end_st.cs_current_bb,LENGTH end_st.cs_current_insts)
    (entry_emitted_positions start end_st)` by
    (gvs[] >> irule entry_stop_region_code_agrees >>
     conj_tac >- simp[] >> qexists_tac `bb` >> simp[]) >>
  gvs[]
QED

Theorem entry_concrete_decoder_prefix:
  compile_abi_decode_to_buf dst src CALLDATALOAD hi
    (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  compile_state_ok start /\ compile_state_ok end_st /\ ~block_is_terminated start /\
  fn_has_code start end_st func /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions <= LENGTH end_st.cs_current_insts /\
  LENGTH end_st.cs_current_insts <= LENGTH bb.bb_instructions /\
  (start.cs_blocks = end_st.cs_blocks \/ phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf ty tv bs v start src dst CALLDATALOAD hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?u. local_prefix ctx func
    (end_st.cs_current_bb,LENGTH end_st.cs_current_insts) initial u /\
    val_in_memory tv v d u.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `obs = entry_stop_function end_st.cs_current_bb
    (LENGTH end_st.cs_current_insts) start.cs_next_id func` >>
  `entry_cfg_preserves (compile_abi_decode_to_buf dst src CALLDATALOAD hi
    (type_to_abi_dec_info sf ce ty))` by simp[entry_cfg_preserves_decode_to_buf] >>
  `obs = entry_stop_function end_st.cs_current_bb
     (LENGTH end_st.cs_current_insts) start.cs_next_id func` by simp[Abbr `obs`] >>
  drule_all entry_concrete_stop_regions >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `start.cs_blocks = end_st.cs_blocks \/
   !b. lookup_block end_st.cs_current_bb obs.fn_blocks = SOME b ==>
     phi_prefix_length b.bb_instructions = 0` by
    (Cases_on `start.cs_blocks = end_st.cs_blocks` >> simp[] >>
     rpt strip_tac >> gvs[] >>
     qspecl_then [`bb.bb_instructions`, `LENGTH end_st.cs_current_insts`,
       `start.cs_next_id`] mp_tac entry_stop_phi_prefix >>
     simp[entry_stop_block_def]) >>
  irule entry_valid_decoder_observer_prefix >>
  simp[] >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `abi_decoder_budget _ _ _ _ _` (irule_at Any) >>
  qpat_assum `region_code_agrees _ _ _ _` (irule_at Any) >>
  qpat_assum `fresh_vars_wrt _ _` (irule_at Any) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `get_instruction _ _ = _` (irule_at Any) >> simp[]
QED
