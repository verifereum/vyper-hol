Theory gasFocusOldBodyObservation
Ancestors
  dftGasFromListTraceDefs[qualified,ignore_grammar]
  dftFinitePacketReachability dftGasInvForwardActive dftIndexedExec dftRunRel
  o1SafeUpto stepWriteFootprintBase contextCodegenRel venomWfProps
  simplifyCfgDefs venomExecProofs venomInst venomState list

(* Identify the source fetch from the retained visit's actual body offset. *)
Theorem focus_old_body_observation:
  !R. R = root_entry with vs_gas_readings := gs ++ tail ==>
  !x. x = EL (LENGTH z)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) ==>
  C7.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  fn_entry_label root_sf = SOME lbl /\
  root_entry.vs_prev_bb = NONE /\ root_entry.vs_current_bb = lbl /\
  root_entry.vs_inst_idx = 0 /\
  o1_ctx_shape C7 /\ MEM sf C7.ctx_functions /\
  tf = dft_fn sf /\ dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  bt.bb_label = bb.bb_label /\ ~in_revert_forward tf s /\
  bb.bb_instructions = ps ++ xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  q < LENGTH xs /\ EL q xs = inst /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  MEM ((p,d,x.inst_id),sf,x,u)
    (dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf R) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  u.vs_gas_readings = tail ==>
  raw_reachable R C7 sf inst u /\ u.vs_current_bb = s.vs_current_bb /\
  ~in_revert_forward sf u /\ (!n. gas_cut n R u <=> LENGTH Mcut < n)
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  simp[] >> strip_tac >>
  qpat_x_assum `tf = dft_fn sf` SUBST_ALL_TAC >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length ps` by
    (simp[] >> irule dft_phi_prefix_append >>
     fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length ps <= LENGTH ps` by simp[phi_prefix_length_le] >>
  `EL (LENGTH z)
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst` by
    (simp[DROP_APPEND1, EL_APPEND_EQN, LENGTH_DROP, LENGTH_TAKE,
          arithmeticTheory.MIN_DEF]) >>
  conj_asm1_tac
  >- (irule dft_packet_trace_raw_reachable >> simp[] >> metis_tac[]) >>
  drule_then assume_tac raw_reachable_active >>
  `MEM bb sf.fn_blocks` by
    (qpat_assum `lookup_block _ sf.fn_blocks = SOME bb`
       (mp_tac o MATCH_MP lookup_block_member_label) >> simp[]) >>
  `MEM inst bb.bb_instructions` by (simp[MEM_APPEND] >> metis_tac[EL_MEM]) >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  `u.vs_current_bb = bb.bb_label` by
    (qpat_x_assum `active_inst sf inst u` mp_tac >> simp[active_inst_def] >>
     disch_then (qx_choose_then `src` strip_assume_tac) >>
     `MEM inst src.bb_instructions` by metis_tac[EL_MEM] >>
     `src = bb` by metis_tac[wf_function_instruction_block] >> metis_tac[]) >>
  `active_inst (dft_fn sf) inst s /\ bt.bb_label = s.vs_current_bb` by
    (qpat_assum `lookup_block s.vs_current_bb _ = SOME bt`
       (strip_assume_tac o MATCH_MP lookup_block_member_label) >>
     fs[get_instruction_def, AllCaseEqs()] >> simp[active_inst_def] >>
     qexists `bt` >> fs[]) >>
  conj_asm1_tac >- metis_tac[] >>
  conj_tac >- (strip_tac >> drule_all inv_forward_active >> simp[]) >>
  drule LIST_REL_LENGTH >> simp[gas_cut_def]
QED
