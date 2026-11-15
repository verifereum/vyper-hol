(* Request-emitting partners cannot cross a nonstatic, non-root abort.
 * This is the opcode boundary used by directional request swaps.
 *)
Theory dftGasRequestPartner
Ancestors
  dftGasSimLocalBoundary dftGasOracleDefs dftRunRel
  venomExecSemantics venomState venomInst venomWf venomEffects opcodeClass list
Libs
  stepInstBaseLib

Theorem ev_abort_partner_request_free:
  dft_gas_swap_pair x y /\ inst_wf x /\
  ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  x.inst_opcode <> INVOKE /\
  ev_step orc p d fuel C x s = Abort a t ==>
  ~MEM y.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
Proof
  strip_tac >>
  Cases_on `x.inst_opcode = GAS`
  >- gvs[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  gvs[ev_step_ordinary, step_inst_non_invoke] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[dft_gas_swap_pair_def, is_terminator_def, inst_wf_def,
      read_effects_def, write_effects_def] >>
  with_opcode_clause gvs >>
  gvs[AllCaseEqs(), exec_create_abort_iff] >>
  simp[] >> rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `effects_independent _ _` mp_tac >>
  EVAL_TAC
QED
