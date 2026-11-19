Theory dftPacketPreterminalOracle
Ancestors
  dftPacketSuccessfulSchedule dftGasInvLookupBlock dftGasInvFixedTrace
  dftGasInvExtraction dftRunRel dftScheduleOrder dftStructural dftCorrectness
  venomWf venomInst venomState list sorting

Theorem dft_packet_preterminal_oracle_reflect:
  LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions /\
  dft_fn_rel sf tf /\
  lookup_block name sf.fn_blocks = SOME bb /\
  lookup_block name tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ ordered ++ [term] /\
  bt.bb_instructions = ps ++ executed ++ [term] /\
  ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  ~is_pseudo term.inst_opcode /\
  EVERY (from_block bb.bb_instructions) executed /\
  inv_ev_trace orc p d fuel D executed s t ==>
  inv_ev_trace orc p d fuel C ordered s t
Proof
  strip_tac >>
  `inv_ev_trace orc p d fuel D ordered s t` by
    (irule inv_lookup_body_replay >> metis_tac[]) >>
  irule dft_packet_successful_schedule_reflect >>
  goal_assum (drule_at Any) >>
  simp[dft_head_bubbles_refl]
QED
