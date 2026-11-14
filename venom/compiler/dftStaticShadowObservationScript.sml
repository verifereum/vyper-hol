(* Project an actual scheduled static prefix into its source shadow. *)
Theory dftStaticShadowObservation
Ancestors
  staticShadowEvent staticShadowDefs dftGasInvExtraction dftGasInvFlexibleTrace
  dftGasOracleDefs dftRunRel venomWfProps venomState venomExecSemantics
  list

Theorem static_shadow_remaining_inv:
  static_shadow_rel s sh ==>
  (dft_remaining_inv fn bb todo sh <=> dft_remaining_inv fn bb todo s)
Proof
  simp[static_shadow_rel_def, static_shadow_def,
       venom_state_component_equality, dft_remaining_inv_def,
       strict_dom_vars_defined_def]
QED

Theorem inv_lookup_scheduled_observation_shadow:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  bb'.bb_instructions = pseudos ++ (scheduled ++ targetobs::targetpost) /\
  targetobs.inst_id = obs.inst_id /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  s0.vs_inst_idx = LENGTH pseudos /\ s0.vs_call_ctx.cc_static /\ static_shadow_rel s0 sh0 /\
  inv_ev_ftrace orc p d ctx scheduled s0 sT /\
  inv_memory_observation obs.inst_opcode ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) sh0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    sS.vs_initial_fmp = sT.vs_initial_fmp
Proof
  strip_tac >>
  drule_all static_shadow_ev_ftrace >> strip_tac >>
  `~sh0.vs_call_ctx.cc_static /\
   sh0.vs_inst_idx = s0.vs_inst_idx /\
   th.vs_initial_fmp = sT.vs_initial_fmp` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  `dft_remaining_inv fn bb (srcpre ++ obs::srcpost) sh0` by
    metis_tac[static_shadow_remaining_inv] >>
  `?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) sh0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op th) /\
    sS.vs_initial_fmp = th.vs_initial_fmp` by
    (irule inv_lookup_scheduled_observation >>
     goal_assum (drule_at Any) >> gvs[] >> metis_tac[]) >>
  qexists_tac `sS` >> simp[] >>
  metis_tac[static_shadow_rel_eval_operand]
QED
