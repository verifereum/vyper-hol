Theory exprSimAbiDecodeAllocaErasePrefix
Ancestors
  exprSimAbiDecodeAllocaEraseExec abiEncoderObserver
  exprSimAbiDecodeAllocaErase venomState venomExecSemantics
  venomExecProofs venomInst unitShapeDefs

Theorem abi_decode_clean_stop_view:
  stop_view (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (stop_view s)
Proof
  simp[stop_view_def, halt_state_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_prefix_fields[simp]:
  (abi_decode_clean_allocas func s).vs_prev_bb = s.vs_prev_bb /\
  (abi_decode_clean_allocas func s).vs_halted = s.vs_halted /\
  (abi_decode_clean_allocas func s).vs_inst_idx = s.vs_inst_idx /\
  (abi_decode_clean_allocas func s).vs_current_bb = s.vs_current_bb
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_idx_update[simp]:
  (abi_decode_clean_allocas func s) with vs_inst_idx := idx =
  abi_decode_clean_allocas func (s with vs_inst_idx := idx)
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_one_phi[simp]:
  eval_one_phi (abi_decode_clean_allocas func s) inst = eval_one_phi s inst
Proof
  simp[eval_one_phi_def]
QED

Theorem abi_decode_clean_phis_OK:
  !xs s u. eval_phis (abi_decode_clean_allocas func s) xs = OK u <=>
  ?t. eval_phis s xs = OK t /\ u = abi_decode_clean_allocas func t
Proof
  Induct >> simp[eval_phis_def] >- metis_tac[] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >- (
    Cases_on `eval_one_phi s h` >> simp[] >> PairCases_on `x` >>
    simp[AllCaseEqs()] >> metis_tac[abi_decode_clean_update_var]) >> metis_tac[]
QED

Theorem abi_decode_observer_inst_member[local]:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==> MEM inst (fn_insts fn)
Proof
  strip_tac >> drule lookup_block_MEM >> strip_tac >>
  gvs[get_instruction_def] >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  qexists_tac `bb` >> simp[] >> metis_tac[listTheory.EL_MEM]
QED

Theorem abi_decode_clean_observer_step:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func) /\
  abi_observer_step ctx fn cut s t ==>
  abi_observer_step ctx fn cut (abi_decode_clean_allocas func s)
                              (abi_decode_clean_allocas func t)
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  `inst.inst_opcode = ALLOCA ==> inst.inst_id IN abi_decode_alloca_ids func`
    by (drule_all abi_decode_observer_inst_member >> metis_tac[]) >>
  gvs[step_inst_non_invoke] >>
  drule_all abi_decode_clean_step_base >> strip_tac >>
  qexists_tac `abi_decode_clean_allocas func middle` >> simp[]
  >> qexists_tac `abi_decode_clean_allocas func entered` >>
  simp[abi_decode_clean_phis_OK] >> metis_tac[]
QED

Theorem abi_decode_clean_observer_step_reflect:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func) /\
  abi_observer_step ctx fn cut (abi_decode_clean_allocas func s) u ==>
  ?t. abi_observer_step ctx fn cut s t /\ u = abi_decode_clean_allocas func t
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  `inst.inst_opcode = ALLOCA ==> inst.inst_id IN abi_decode_alloca_ids func`
    by (drule_all abi_decode_observer_inst_member >> metis_tac[]) >>
  gvs[step_inst_non_invoke] >>
  drule_all abi_decode_clean_step_base_reflect >> strip_tac >> gvs[] >>
  fs[abi_decode_clean_phis_OK] >> gvs[] >>
  rename1 `eval_phis t target.bb_instructions = OK original` >>
  qexists_tac `original with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  simp[] >> metis_tac[]
QED

Theorem abi_decode_clean_local_prefix:
  !ctx fn cut s t.
  local_prefix ctx fn cut s t ==>
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func) ==>
  local_prefix ctx fn cut (abi_decode_clean_allocas func s)
                          (abi_decode_clean_allocas func t)
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  drule_all abi_decode_clean_observer_step >> strip_tac >>
  irule (cj 2 local_prefix_rules) >> metis_tac[]
QED

Theorem abi_decode_clean_local_prefix_reflect_general[local]:
  !ctx fn cut a u.
  local_prefix ctx fn cut a u ==>
  !s. a = abi_decode_clean_allocas func s ==>
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func) ==>
  ?t. local_prefix ctx fn cut s t /\ u = abi_decode_clean_allocas func t
Proof
  Induct_on `local_prefix` >> rpt strip_tac >> gvs[]
  >- (qexists_tac `s` >> simp[] >> irule (cj 1 local_prefix_rules) >> simp[]) >>
  drule_all abi_decode_clean_observer_step_reflect >> strip_tac >>
  metis_tac[cj 2 local_prefix_rules]
QED

Theorem abi_decode_clean_local_prefix_reflect:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func) /\
  local_prefix ctx fn cut (abi_decode_clean_allocas func s) u ==>
  ?t. local_prefix ctx fn cut s t /\ u = abi_decode_clean_allocas func t
Proof
  metis_tac[abi_decode_clean_local_prefix_reflect_general]
QED
