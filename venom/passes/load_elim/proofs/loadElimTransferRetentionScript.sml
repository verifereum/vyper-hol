Theory loadElimTransferRetention
Ancestors
  loadElimTransferProvenance loadElimDefs venomEffects finite_map list pred_set

Theorem le_retained_store_lookup:
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  (!op. ops = [op] ==> ~le_transfer_generates ctx inst key op) /\
  inst.inst_opcode <> ctx.lctx_config.lc_load /\
  ctx.lctx_config.lc_store = SOME st /\ inst.inst_opcode = st /\
  inst.inst_operands = [addr;value] ==>
  key <> load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
    (normalize_operand ctx.lctx_dfg []) inst /\
  FLOOKUP (load_invalidate ctx.lctx_aliases ctx.lctx_bp ctx.lctx_addr_space
    (unwrap_load_lattice initial)
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) inst)) key = SOME ops
Proof
  strip_tac >>
  qpat_x_assum `FLOOKUP _ _ = _` mp_tac >>
  simp[load_transfer_def, unwrap_load_lattice_def] >>
  Cases_on `key = load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
    (normalize_operand ctx.lctx_dfg []) inst` >>
  gvs[FLOOKUP_UPDATE, le_transfer_generates_def]
QED

Theorem le_retained_store_invalidation_member:
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  (!op. ops = [op] ==> ~le_transfer_generates ctx inst key op) /\
  inst.inst_opcode <> ctx.lctx_config.lc_load /\
  ctx.lctx_config.lc_store = SOME st /\ inst.inst_opcode = st /\
  inst.inst_operands = [addr;value] ==>
  key IN FDOM (load_invalidate ctx.lctx_aliases ctx.lctx_bp ctx.lctx_addr_space
    (unwrap_load_lattice initial)
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) inst))
Proof
  strip_tac >> drule_all le_retained_store_lookup >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem le_retained_nonstore_no_write_effect:
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  inst.inst_opcode <> ctx.lctx_config.lc_load /\
  ctx.lctx_config.lc_store = SOME st /\ inst.inst_opcode <> st ==>
  (case ctx.lctx_addr_space of
     AddrSp_Memory => Eff_MEMORY
   | AddrSp_Storage => Eff_STORAGE
   | AddrSp_Transient => Eff_TRANSIENT
   | _ => Eff_MEMORY) NOTIN write_effects inst.inst_opcode
Proof
  strip_tac >> qpat_x_assum `FLOOKUP _ _ = _` mp_tac >>
  simp[load_transfer_def, unwrap_load_lattice_def] >>
  IF_CASES_TAC >> simp[]
QED
