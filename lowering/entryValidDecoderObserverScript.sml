(* Arbitrary-source typed decoding transported from a regional STOP observer. *)
Theory entryValidDecoderObserver
Ancestors
  abiDecoderValidRecursive abiDecoderValidContract abiEncoderObserver
  abiDecoderContract exprLoweringProps fragExec compileEnv
  venomState venomInst venomExecSemantics

Theorem entry_valid_decoder_observer_prefix:
  compile_abi_decode_to_buf dst src CALLDATALOAD hi
    (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  fn_has_code start end_st obs /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb obs.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf ty tv bs v start src dst CALLDATALOAD hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  cut = (end_st.cs_current_bb,LENGTH end_st.cs_current_insts) /\
  lookup_block (FST cut) obs.fn_blocks = SOME stop_bb /\
  get_instruction stop_bb (SND cut) = SOME (mk_inst stop_id STOP [] []) /\
  observer_region_safe obs cut R /\ observer_region_closed ctx obs cut R /\
  (initial.vs_current_bb,initial.vs_inst_idx) IN R /\
  region_code_agrees obs func cut R ==>
  ?u. local_prefix ctx func cut initial u /\ val_in_memory tv v d u.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_decode >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lookup_block actual.vs_current_bb obs.fn_blocks = SOME stop_bb /\
   get_instruction stop_bb actual.vs_inst_idx = SOME (mk_inst stop_id STOP [] [])` by gvs[] >>
  drule_all abi_decode_sim_stop_run >> strip_tac >>
  drule_all observer_region_run_prefix_transfer >> strip_tac >>
  drule stop_view_fields >> strip_tac >>
  qexists_tac `u` >> gvs[]
QED
