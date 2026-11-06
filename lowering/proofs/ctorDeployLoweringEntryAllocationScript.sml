(* Actual-site credit with the initial immutable offset retained. *)
Theory ctorDeployLoweringEntryAllocation
Ancestors
  ctorDeployLoweringEntryRegistration ctorDeployMemoryFrontier
  actualAllocCredit actualAllocExec allocaBudgetProps allocaFrontierBound
  ctorAbiActualAlloc ctorAbiActualFrame ctorAbiActualMemory
  abiEncoderRegisteredEffect abiEncoderPrimitiveEffect compileEnv
  abiDecoderVarSequence abiDecoderIndexInit abiDecoderReentry exprLoweringProps
  abiEncoderProps venomMemProps
  pred_set venomMemDefs
  vyperCompiler venomState venomInst venomExecSemantics finite_map list arithmetic words

Theorem deploy_ctor_alloca_frontier_credit:
  !k ctx fn site s inst.
    alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    s.vs_alloca_next + alloca_size inst <= k + unit_alloca_budget ctx
Proof
  rpt strip_tac >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
  drule_all remaining_alloca_budget_member >>
  gvs[alloca_frontier_inv_from_def] >> decide_tac
QED

Theorem deploy_ctor_alloca_frontier_preserved:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  step_inst_base inst s = OK t /\ alloca_frontier_inv_from k ctx fn site s ==>
  alloca_frontier_inv_from k ctx fn site' t
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all step_inst_base_alloca_budget >>
  simp[alloca_frontier_inv_from_def] >> strip_tac >>
  fs[alloca_frontier_inv_from_def] >> decide_tac
QED

Theorem deploy_ctor_alloca_frontier_fields:
  alloca_frontier_inv_from k ctx fn site s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  alloca_frontier_inv_from k ctx fn site' t
Proof
  strip_tac >>
  `remaining_alloca_budget (fn_insts fn) t =
   remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[alloca_frontier_inv_from_def]
QED

Theorem deploy_ctor_literal_alloca_fresh_run:
  alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  n < dimword (:256) /\ k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (n2w n:bytes32) = OK t /\
    t = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,n));
        vs_alloca_next := s.vs_alloca_next + n|>) /\
    s.vs_alloca_next + n < dimword (:256) /\
    t.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,n)) /\
    t.vs_alloca_next = s.vs_alloca_next + n /\
    (!j. j <> inst.inst_id ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j) /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code /\
    t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `alloca_size inst = n` by simp[alloca_size_def] >>
  drule_all deploy_ctor_alloca_frontier_credit >> strip_tac >>
  `s.vs_alloca_next + n < dimword (:256)` by decide_tac >>
  simp[step_inst_base_def, exec_alloca_def] >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

Theorem deploy_ctor_literal_alloca_owned_step:
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ inst.inst_outputs = [out] /\
  n < dimword (:256) /\ k + unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas inst.inst_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) ==>
  ?t p. step_inst_base inst s = OK t /\
    exec_alloca inst s (n2w n:bytes32) = OK t /\
    lookup_var out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    (!op. op <> Var out ==> eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> inst.inst_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code /\
    t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all deploy_ctor_literal_alloca_fresh_run >> strip_tac >>
      `alloca_inv t` by metis_tac[actual_alloca_slots_preserved] >>
      `alloca_frontier_inv_from k ctx fn site t` by
        metis_tac[deploy_ctor_alloca_frontier_preserved] >>
      drule_all actual_literal_alloca_frame >> strip_tac >>
      qexistsl [`t`, `s.vs_alloca_next`] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  gvs[] >>
  `n < dimword (:256)` by decide_tac >>
  drule_all actual_literal_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `alloca_inv t` by metis_tac[actual_alloca_slots_preserved] >>
  `alloca_frontier_inv_from k ctx fn site t` by
    metis_tac[deploy_ctor_alloca_frontier_preserved] >>
  drule_all actual_literal_alloca_frame >> strip_tac >>
  qexistsl [`t`, `p`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem deploy_ctor_word_alloca_fresh_run:
  alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    t = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,32));
        vs_alloca_next := s.vs_alloca_next + 32|>) /\
    s.vs_alloca_next + 32 < dimword (:256)
Proof
  strip_tac >>
  `alloca_size inst = 32` by
    simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule_all deploy_ctor_alloca_frontier_credit >> strip_tac >>
  `s.vs_alloca_next + 32 < dimword (:256)` by decide_tac >>
  simp[step_inst_base_def, exec_alloca_def] >>
  simp[update_var_def, FLOOKUP_UPDATE,
    dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem deploy_ctor_word_alloca_labels_narrow:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t p.
    step_inst_base inst s = OK t /\
    eval_operand (Var out) t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    regions_disjoint (d,n) (p,32) /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
    abi_encoder_registered_effect {inst.inst_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_labels = s.vs_labels /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_code = s.vs_code
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all deploy_ctor_word_alloca_fresh_run >> strip_tac >>
      `alloca_inv t` by metis_tac[actual_alloca_slots_preserved] >>
      `alloca_frontier_inv_from k ctx fn site t` by
        metis_tac[deploy_ctor_alloca_frontier_preserved] >>
      qexistsl [`t`, `s.vs_alloca_next`] >>
      simp[FLOOKUP_UPDATE] >>
      conj_tac
      >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      conj_tac >- simp[regions_disjoint_def] >>
      conj_tac >- (irule ctor_actual_scratch_fresh >> simp[]) >>
      simp[abi_encoder_registered_effect_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `i = inst.inst_id` >> gvs[]) >>
  PairCases_on `x` >>
  `x1 = 32 /\ regions_disjoint (d,n) (x0,x1)` by
    (gvs[ctor_actual_scratch_def] >> metis_tac[]) >>
  gvs[] >> drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `alloca_inv t` by metis_tac[actual_alloca_slots_preserved] >>
  `alloca_frontier_inv_from k ctx fn site t` by
    metis_tac[deploy_ctor_alloca_frontier_preserved] >>
  `t.vs_labels = s.vs_labels /\ t.vs_gas_readings = s.vs_gas_readings /\
   t.vs_code = s.vs_code` by simp[update_var_def] >>
  qexistsl [`t`, `x0`] >> simp[] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule abi_encoder_registered_update_var
QED

Theorem deploy_ctor_index_slot_bound:
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas id = SOME (p,32) ==>
  p < dimword (:256)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[alloca_frontier_inv_from_def] >> decide_tac) >>
  `p+32 <= s.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >> decide_tac
QED

Theorem deploy_ctor_index_labels_narrow:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_labels = s.vs_labels /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_code = s.vs_code
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id IN ids` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all deploy_ctor_word_alloca_labels_narrow >> strip_tac >>
  rename1 `step_inst_base inst s = OK allocated` >>
  `p < dimword (:256)` by
    (irule deploy_ctor_index_slot_bound >> metis_tac[mk_inst_def]) >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated)` by
    (qpat_x_assum `step_inst_base inst s = OK allocated` mp_tac >>
     simp_tac bool_ss [Abbr `inst`] >> strip_tac >>
     asm_simp_tac bool_ss [run_inst_seq_def] >>
     simp[step_inst_base_def, exec_write2_def, mk_inst_def,
       eval_operand_def, w2n_n2w]) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] allocated (mstore p 0w allocated)` by
    (irule abi_encoder_registered_slot_store >>
     qexists `st.cs_next_id` >> gvs[Abbr `inst`, mk_inst_def]) >>
  `alloca_frontier_inv_from k ctx fn site (mstore p 0w allocated)` by
    (irule deploy_ctor_alloca_frontier_fields >>
     qexistsl [`allocated`, `site`] >> simp[]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    simp[mk_inst_def, abi_decoder_reentry_opcode_def] >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  qexistsl [`mstore p 0w allocated`, `p`] >>
  simp[abi_decoder_operand_mstore, mload_mstore_same,
       abi_encoder_primitive_alloca_inv] >>
  conj_tac >- gvs[Abbr `inst`, mk_inst_def] >>
  irule abi_encoder_registered_effect_trans >> goal_assum (drule_at Any) >>
  gvs[Abbr `inst`, mk_inst_def]
QED
