Theory exprSimAbiDecodeImmutableFrame
Ancestors
  exprSimAbiDecodeResources exprSimAbiDecodeSuccessPrefix exprSimAbiDecodeAllocaErasePrefix
  exprSimAbiDecodeProtection exprSimAbiDecodeAllocaErase
  abiEncoderPrefixSafety exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeEndpointFrame
  exprSimAbiDecodeSetupExec exprSimAbiGasBridge fragExec venomExecProofs
  exprLoweringProps exprSimAbiDecodeCoverageBoundary localPtrsProps venomState venomInst list rich_list

Theorem abi_decode_closed_region_frame[local]:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  q + n <= s.vs_alloca_next /\
  (!id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint b sz q n) /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >> drule abi_decode_output_site_interval >> strip_tac >>
  qpat_x_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `abi_decode_success_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_post_def] >> strip_tac >>
  fs[abi_decode_allocation_floor_def] >>
  `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas u` by
    simp[abi_decode_allocation_floor_def] >>
  qpat_x_assum `decode_site_effect _ _ _ _ _ _` mp_tac >>
  rewrite_tac[GSYM abi_decode_write_set_def] >> strip_tac >>
  irule (SRULE [] abi_decode_write_set_memory_frame) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  conj_tac >- decide_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac []
QED

Theorem abi_decode_prefix_region_frame:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  evaluate_abi_decode env ty bs = INL v /\
  local_prefix ctx fn (frag_observer_cut final) s t /\
  q + n <= s.vs_alloca_next /\
  (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint b sz q n) ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >>
  `!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func` by
    (simp[abi_decode_alloca_ids_def] >> rpt strip_tac >>
     qexists_tac `i` >> simp[] >> first_x_assum irule >> simp[]) >>
  `abi_builtin_decode_output_site start (abi_static_size ce.ce_struct_fields ty)
      (abi_size_bound ce.ce_struct_fields ty) IN abi_decode_alloca_ids func` by
    (`!i. MEM i (frag_code start final) ==> MEM i (fn_insts fn)` by
       metis_tac[abi_decode_resources_code_member] >>
     drule abi_decode_lower_output_allocation >> strip_tac >>
     metis_tac[]) >>
  drule_all abi_decode_clean_builtin_resources >> strip_tac >>
  `?u. abi_decode_success_closed ce env ty tv bs out d start final ctx func
       (abi_decode_clean_allocas func s) u /\
       local_prefix ctx fn (frag_observer_cut final)
         (abi_decode_clean_allocas func s) u` by
    (mp_tac (Q.INST [`s` |-> `abi_decode_clean_allocas func s`, `n` |-> `k`]
       abi_decode_original_entry_success_prefix) >>
     (impl_tac >- simp[abi_decode_clean_allocas_def, eval_operand_def]) >>
     metis_tac[]) >>
  `local_prefix ctx fn (frag_observer_cut final)
      (abi_decode_clean_allocas func s) (abi_decode_clean_allocas func t)` by
    metis_tac[abi_decode_clean_local_prefix] >>
  `u = abi_decode_clean_allocas func t` by metis_tac[local_prefix_endpoint_unique] >>
  drule_at (Pat `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_decode_closed_region_frame >>
  disch_then (qspecl_then [`q`, `n`, `data`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    irule abi_decode_clean_protected_rows >> goal_assum (drule_at Any) >> metis_tac[])) >>
  simp[]
QED

Theorem abi_decode_prefix_immutable_frame:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  evaluate_abi_decode env ty bs = INL v /\
  local_prefix ctx fn (frag_observer_cut final) s t /\
  immutable_alloca_sep func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
  mem_bytes_at off (type_memory_size itv) t.vs_memory =
  mem_bytes_at off (type_memory_size itv) s.vs_memory
Proof
  strip_tac >>
  `off + type_memory_size itv <= s.vs_alloca_next /\
   (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint b sz off (type_memory_size itv))` by
    (qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [immutable_alloca_sep_def] >>
     disch_then (drule_all o CONJUNCT2) >> strip_tac >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  irule abi_decode_prefix_region_frame >> asm_rewrite_tac [] >>
  goal_assum (drule_at (Pat `local_prefix _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_abi_decode _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  asm_rewrite_tac [] >> metis_tac[]
QED
