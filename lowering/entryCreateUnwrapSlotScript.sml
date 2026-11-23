(* Storage and transient aggregate forcing, restricted to its own suffix. *)
Theory entryCreateUnwrapSlot
Ancestors
  entryCreateFocusSpec entryCreatePathScope createSizeLocationCode
  createSizeCutRegion exprPtrUnwrapEnsureShape exprPtrUnwrapAllocation
  exprPtrUnwrapStorageLayout exprSimStorageCopy copyExecution exprLoweringProps
  abiEncoderProps exprSimAbiDecodeSiteCoverage fragExec compileEnv emitHelper
  context loweringHalt loweringPosts venomInst venomState venomRunBounded dftGasFromListTracePrefix
  bodyFullIfExpReach entryCreateBodyCut exprSimAbiGasBridge gasContext
  list rich_list arithmetic relation pair

Theorem unwrap_slot_copy_opcodes[local]:
  (opc = SLOAD \/ opc = TLOAD) /\
  MEM i (frag_code a (slot_copy_final a src dst n opc)) ==>
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
  i.inst_opcode <> GAS
Proof
  Cases_on `opc = SLOAD` >>
  gvs[frag_code_def, slot_copy_emitted_blocks, slot_copy_blocks_def,
      slot_copy_final_def, slot_copy_init_insts_def, slot_copy_cond_insts_def,
      slot_copy_body_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem unwrap_slot_ensure_opcodes:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm a = (op,b) /\
  MEM i (frag_code a b) ==>
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
  i.inst_opcode <> GAS
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ensure_slot_memory_split >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `a.cs_blocks = sm.cs_blocks` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `!j. MEM j (frag_code a sm) ==> j.inst_opcode = ALLOCA` by
    simp[frag_code_def, emitted_blocks_def, mk_inst_def] >>
  Cases_on `n = 1`
  >- (gvs[] >> drule storage_copy_word_layout >> strip_tac >>
      `cs_extends sm b` by metis_tac[same_blocks_def,cs_extends_same_block] >>
      drule_all abi_decode_frag_code_compose >> strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `loc = LocStorage` >>
      gvs[frag_code_def, emitted_blocks_def, same_blocks_def, mk_inst_def]) >>
  `?lab. compile_slot_to_memory src buf.buf_operand n loc sm = (lab,b)` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  drule_all abi_decode_frag_code_compose >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `loc = LocStorage` >> gvs[] >> metis_tac[unwrap_slot_copy_opcodes]
QED

Theorem create_unwrap_slot_copy_cut:
  unwrap_value cenv (LocatedValue t p) a = (op,b) /\
  p.ptr_location = slot_loc tr /\ ~is_word_type t /\
  fn_has_code a b fn /\ body_inv tops ctx cenv cx /\ MEM fn ctx.ctx_functions ==>
  create_operand_cut a b explicit ctx fn tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all unwrap_slot_ensure_layout >> strip_tac >>
  `create_cut_code {} a b` by metis_tac[create_unwrap_cut_code,SND] >>
  `!i. MEM i (frag_code a b) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2` by
    (rpt strip_tac >> Cases_on `tr` >> gvs[slot_loc_def] >>
     metis_tac[unwrap_slot_ensure_opcodes]) >>
  drule_all create_cut_region_rules >> strip_tac >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  `create_cut_region a b s` by fs[create_interior_visit_def,create_operand_at_def] >>
  drule create_interior_visit_cases >> strip_tac >>
  fs[create_operand_fetch_def,create_operand_at_def] >>
  `create_cut_region a b u` by metis_tac[create_expr_prefix_cut_region] >>
  `MEM inst (frag_code a b)` by metis_tac[] >>
  gvs[create_body_cut_def,inst_create_size_ok_def]
QED
