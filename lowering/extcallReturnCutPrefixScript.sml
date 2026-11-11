(* Concrete STOP cuts expose execution before caller resources are restored. *)
Theory extcallReturnCutPrefix
Ancestors
  extcallReturnObserverResources extcallReturnCountedTransport extcallReturnCountedCheck
  abiValidAllocatedObservations abiDecoderVarSequence abiEncoderObserver
  exprSimAbiGasBridge exprSimHash abiMalformedRecursiveInterface venomExecProofs venomExecSemantics venomInstProps
  venomInst venomState compileEnv exprLoweringProps list pred_set

Theorem return_decoder_step_fmp:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = OK t ==> t.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  `run_inst_seq [inst] s = OK t` by simp[run_inst_seq_def] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) [inst]` by simp[] >>
  drule_all abi_valid_allocated_sequence_static >> simp[]
QED

Theorem return_observer_step_fmp:
  abi_observer_step ctx fn cut s t /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==>
    abi_decoder_reentry_opcode inst.inst_opcode) ==>
  t.vs_fmp = s.vs_fmp
Proof
  rw[abi_observer_step_def] >>
  `middle.vs_fmp = s.vs_fmp` by
    (irule return_decoder_step_fmp >>
     qexists_tac `inst` >> metis_tac[step_inst_non_invoke]) >> simp[] >>
  drule eval_phis_only_updates_vs_vars >> strip_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem return_decoder_prefix_fmp:
  local_prefix ctx fn cut s t ==>
  !R. (s.vs_current_bb,s.vs_inst_idx) IN R /\
    observer_region_closed ctx fn cut R /\
    (!lbl idx bb inst. (lbl,idx) IN R /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
      abi_decoder_reentry_opcode inst.inst_opcode) ==>
    t.vs_fmp = s.vs_fmp
Proof
  Induct_on `local_prefix` >> rpt strip_tac >- simp[] >>
  rename1 `abi_observer_step ctx fn cut s middle` >>
  `middle.vs_fmp = s.vs_fmp` by
    (irule return_observer_step_fmp >>
     qexistsl_tac [`ctx`, `cut`, `fn`] >> simp[] >>
     fs[abi_observer_step_def] >> metis_tac[]) >>
  ` (middle.vs_current_bb,middle.vs_inst_idx) IN R` by
    metis_tac[observer_region_closed_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem return_frag_prefix_fmp:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code sa sb) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule return_decoder_prefix_fmp >>
  disch_then (qspec_then `frag_observer_region sa sb` irule) >> simp[] >>
  reverse conj_tac >- metis_tac[frag_observer_region_closed] >>
  rpt strip_tac >>
  `MEM inst (frag_code sa sb)` by metis_tac[frag_observer_code_provenance] >>
  fs[EVERY_MEM]
QED

(* fn is the concrete completed observer. Simulation is first restricted
   to its bare STOP observer; resource restoration happens only afterwards. *)
Theorem return_cut_prefix_resources:
  cs_extends sa sb /\ fn_has_code sa sb obs /\ frag_gas_free sa sb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code sa sb) /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
    !bb. lookup_block sb.cs_current_bb obs.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  abi_decode_sim ctx' (frag_observer sa sb obs id) s t /\
  abi_malformed_resource_post (return_observer_context ctx obs) obs
    ce cx es next sites dstid s t /\
  stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) ==>
  ?u. local_prefix ctx' obs (frag_observer_cut sb) s u /\
    stop_view u = stop_view t /\ u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func ce cx es next sites dstid s u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?fuel. run_from fuel ctx' (frag_observer sa sb obs id) s = Halt (stop_view t)` by
    (irule abi_decode_sim_stop_run >> simp[] >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `?u. local_prefix ctx' (frag_observer sa sb obs id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     conj_tac >- metis_tac[] >> simp[stop_view_def, halt_state_def]) >>
  `u.vs_fmp = s.vs_fmp` by (irule return_frag_prefix_fmp >> metis_tac[]) >>
  `local_prefix ctx' obs (frag_observer_cut sb) s u` by
    (irule frag_observer_prefix_transfer >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `abi_malformed_resource_post (return_observer_context ctx obs) obs
     ce cx es next sites dstid s u` by
    (drule stop_view_fields >> strip_tac >>
     fs[abi_malformed_resource_post_def] >>
     conj_tac >-
       (drule_all stop_view_recover >> disch_then SUBST1_TAC >>
        simp[hash_returndata_state_rel]) >>
     metis_tac[stop_view_operand]) >>
  qexists_tac `u` >>
  fs[frag_observer_cut_def] >>
  irule return_observer_output_resources >> metis_tac[]
QED
