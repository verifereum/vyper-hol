Theory loadElimConfiguredGeneration
Ancestors
  loadElimGenerationSound loadElimKeyShapeInvariant loadElimTransferProvenance
  loadElimOperandValidity dfgCorrectnessProof loadElimDefs venomExecSemantics venomState list

Theorem le_configured_load_opcode:
  le_configured_context ctx /\ inst.inst_opcode = ctx.lctx_config.lc_load ==>
  MEM (inst.inst_opcode,ctx.lctx_addr_space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata);
     (DLOAD,AddrSp_Data)]
Proof
  simp[le_configured_context_def] >> strip_tac >>
  gvs[memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def]
QED

Theorem le_configured_store_opcode:
  le_configured_context ctx /\
  ctx.lctx_config.lc_store = SOME inst.inst_opcode ==>
  MEM (inst.inst_opcode,ctx.lctx_addr_space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)]
Proof
  simp[le_configured_context_def] >> strip_tac >>
  gvs[memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def]
QED

Theorem le_generating_load_address_exists:
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata);
     (DLOAD,AddrSp_Data)] /\
  inst.inst_operands = [addr] /\ step_inst fuel C inst s = OK t ==>
  ?w. eval_operand addr s = SOME w
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem le_generating_store_address_exists:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] /\ step_inst fuel C inst s = OK t ==>
  ?w. eval_operand addr s = SOME w
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem le_configured_generation_read_local:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  le_inst_operands_valid ctx.lctx_dfg inst s /\
  le_transfer_generates ctx inst key op /\
  step_inst fuel C inst s = OK t /\
  (!a. key = LK_Op (Var a) ==> ~MEM a inst.inst_outputs) ==>
  le_key_read ctx.lctx_addr_space key t = eval_operand op t
Proof
  strip_tac >> fs[le_transfer_generates_def]
  >- (drule_all le_configured_load_opcode >> strip_tac >>
      drule_all le_generating_load_address_exists >> strip_tac >>
      `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s = SOME w` by
        metis_tac[le_inst_operands_valid_eval, MEM] >>
      simp[eval_operand_def] >> irule le_generating_load_key >> simp[] >>
      conj_tac >- (gvs[] >> metis_tac[]) >> metis_tac[]) >>
  drule_all le_configured_store_opcode >> strip_tac >>
  drule_all le_generating_store_address_exists >> strip_tac >>
  `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s = SOME w` by
    metis_tac[le_inst_operands_valid_eval, MEM] >>
  irule le_generating_store_key >> simp[] >> metis_tac[]
QED

Theorem le_configured_generation_read:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  dfg_assigns_sound ctx.lctx_dfg s /\
  le_transfer_generates ctx inst key op /\
  step_inst fuel C inst s = OK t /\
  (!a. key = LK_Op (Var a) ==> ~MEM a inst.inst_outputs) ==>
  le_key_read ctx.lctx_addr_space key t = eval_operand op t
Proof
  metis_tac[le_configured_generation_read_local,
            le_dfg_sound_inst_operands_valid]
QED
