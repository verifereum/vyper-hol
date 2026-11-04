(* Allocation evolution for actual successful instruction sequences.
   TOP-LEVEL: abi_scratch_sequence_evolution derives allocation metadata from
   run_inst_seq and a final numeric bound, for use after executing a prefix. *)
Theory abiScratchSequence
Ancestors
  abiScratchFootprint abiDecoderFootprint abiDecoderFrame
  exprLoweringProps venomExecProps venomMemProofs venomExecSemantics
  venomState venomInst finite_map list arithmetic words

Theorem abi_scratch_step_alloca:
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK t ==>
  ?asz:bytes32. exec_alloca inst s asz = OK t
Proof
  strip_tac >> gvs[Once step_inst_base_def, AllCaseEqs()] >>
  rename1 `exec_alloca inst s alloc_size = OK t` >>
  qexists_tac `alloc_size` >> simp[]
QED

Theorem abi_scratch_step_non_alloca:
  step_inst_base inst s = OK t /\ inst.inst_opcode <> ALLOCA /\
  t.vs_alloca_next <= b + cap ==>
  abi_scratch_evolution ids b cap s t
Proof
  strip_tac >> drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s`, `t`] step_inst_base_preserves_alloca_fields) >>
  impl_tac >- simp[] >> strip_tac >>
  simp[abi_scratch_evolution_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_scratch_step_evolution:
  step_inst_base inst s = OK t /\ t.vs_alloca_next <= b + cap ==>
  abi_scratch_evolution ids b cap s t
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >> strip_tac
  >- (drule_all abi_scratch_step_alloca >> strip_tac >>
      drule_all (Q.INST [`ids` |-> `ids`] abi_scratch_evolution_alloca) >> simp[]) >>
  drule_all abi_scratch_step_non_alloca >> simp[]
QED

Theorem abi_scratch_sequence_cons:
  step_inst_base inst s = OK middle /\ abi_scratch_evolution ids b cap middle t ==>
  abi_scratch_evolution ids b cap s t
Proof
  strip_tac >>
  `middle.vs_alloca_next <= b + cap` by
    (fs[abi_scratch_evolution_def] >> decide_tac) >>
  `abi_scratch_evolution ids b cap s middle` by
    (drule_all (Q.INST [`ids` |-> `ids`] abi_scratch_step_evolution) >> simp[]) >>
  drule_all abi_scratch_evolution_trans >> simp[]
QED

Theorem abi_scratch_sequence_evolution:
  !insts s t ids b cap.
  run_inst_seq insts s = OK t /\ t.vs_alloca_next <= b + cap ==>
  abi_scratch_evolution ids b cap s t
Proof
  Induct_on `insts` >- simp[run_inst_seq_def, abi_scratch_evolution_refl] >>
  rpt gen_tac >> rename1 `run_inst_seq (inst::rest) initial = OK final` >>
  simp_tac bool_ss [Once run_inst_seq_def] >>
  Cases_on `step_inst_base inst initial` >> simp[] >> strip_tac >>
  rename1 `step_inst_base inst initial = OK middle` >>
  `abi_scratch_evolution ids b cap middle final` by
    (first_x_assum (qspecl_then [`middle`, `final`, `ids`, `b`, `cap`] mp_tac) >> simp[]) >>
  drule_all abi_scratch_sequence_cons >> simp[]
QED
