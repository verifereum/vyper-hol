Theory lowerDloadResidualNonmemory
Ancestors
  lowerDloadNormalExisting lowerDloadGuardProducer lowerDloadReachableDiscipline
  lowerDloadProvenanceSupport lowerDloadReturnBoundary lowerDloadNormalData
  lowerDloadOwnership lowerDloadPairedBoundary ptrDiscipline o1PassContract
  contextCodegenRel venomWf venomInst list finite_map pred_set
  pointerConfinedDefs memLocDefs lowerDloadOpaqueExecution lowerDloadCoverageInvariant
  lowerDloadExplicitBase lowerDloadReadEffects lowerDloadScalarClosure
  lowerDloadVariableTransport venomState venomExecSemantics codegenRel
  lowerDloadGasProducer lowerDloadFrameCertificate lowerDloadAllocation
  lowerDloadParameterEnvelope lowerDloadParamProducer lowerDloadMaskBounds
  lowerDloadEnvironmentRead lowerDloadOperand lowerDloadStorageRead
  lowerDloadSharedState vfmState lowerDloadStorageWrite lowerDloadNormalTransport
  lowerDloadMaskedStorage

Theorem ld_annotated_inst_wf:
  o1_ctx_shape CS /\ (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s ==>
  inst_wf i
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
  `fn_inst_wf fn` by metis_tac[] >>
  fs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem ld_annotated_guard_scalar:
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] ==>
  !op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!v. MEM (Var v) i.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `!v. op = Var v ==> v NOTIN fn_pv P fn` by metis_tac[] >>
  drule_all ld_annotated_scalar_prov >> simp[]
QED

Theorem ld_normal_guard_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  o1_ctx_shape CS /\ ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `inst_wf i` by metis_tac[ld_annotated_inst_wf] >>
  `i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >> simp[inst_wf_def]) >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN U` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  `ld_owned_vars U E AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule ld_owned_operands_clean >>
     goal_assum (drule_at (Pat `ld_owned_vars _ _ _ _ _ _ _ _`)) >>
     rpt gen_tac >> disch_tac >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[ld_annotated_guard_scalar] >>
     irule ld_taint_operand_clean >>
     goal_assum (drule_at (Pat `taint_ok _ _ _ _`)) >> simp[] >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  `t' = t /\ step_inst fuel CS i s = OK s` by
    (drule_all ld_guard_backward >> simp[]) >>
  qpat_x_assum `t' = t` SUBST_ALL_TAC >>
  qexists_tac `s` >> asm_rewrite_tac[] >>
  drule ld_guard_prov >> disch_then (fn th => rewrite_tac[th]) >>
  drule ld_guard_taint >> disch_then (fn th => rewrite_tac[th]) >>
  simp[ld_set_prov_def, set_var_taint_def, DRESTRICT_UNIV] >> metis_tac[]
QED

Theorem ld_normal_initial_fmp_backward:
  i.inst_opcode = INITIAL_FMP /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `ld_owned_vars U E AG BH tn un s t /\ ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_owned_initial_fmp_backward >> simp[]) >>
  qexists_tac `s'` >> simp[] >>
  `?out w. i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t` by
    (drule_all ld_initial_fmp_backward >>
     disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >>
     metis_tac[venomExecSemanticsTheory.exec_result_11]) >>
  irule ld_normal_step_vars_complete >>
  simp[update_var_def] >> suspend "fields"
QED

Resume ld_normal_initial_fmp_backward[fields]:
  `(!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (simp[ld_step_prov_def, ld_out_prov_def] >>
     irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  simp[] >> conj_tac
  >- (simp[lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `v = out` >> simp[] >> metis_tac[lookup_var_def]) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, source_memory_write_ranges_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, EXTENSION] >>
  rpt CASE_TAC >> simp[] >> metis_tac[]
QED

Finalise ld_normal_initial_fmp_backward

Theorem ld_normal_gas_backward:
  i.inst_opcode = GAS /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `ld_frame_data V U E L H AP BP AG BH tn un s t` by
    metis_tac[ld_normal_data_frame] >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (drule ld_normal_data_companions >> simp[]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    s'.vs_gas_readings = t'.vs_gas_readings /\
    ld_frame_data V U E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_gas_frame_data_backward >> simp[]) >>
  `?out w rest. i.inst_outputs = [out] /\
    s' = update_var out w (s with vs_gas_readings := rest) /\
    t' = update_var out w (t with vs_gas_readings := rest)` by
    (drule_all ld_gas_backward >>
     disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >>
     metis_tac[exec_result_11]) >>
  qexists_tac `s'` >> simp[] >> suspend "completion"
QED

Resume ld_normal_gas_backward[completion]:
  `ld_frame_bound t.vs_alloca_next H BP BH` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by
    (drule ld_normal_data_geometry >> strip_tac >> metis_tac[ld_live_step_prov]) >>
  `!st ta. (step_taint i st
      (update_var out w (st with vs_gas_readings := rest)) ta).t_mem = ta.t_mem /\
    (step_taint i st (update_var out w (st with vs_gas_readings := rest)) ta).t_stor = ta.t_stor /\
    (step_taint i st (update_var out w (st with vs_gas_readings := rest)) ta).t_trans = ta.t_trans /\
    (step_taint i st (update_var out w (st with vs_gas_readings := rest)) ta).t_imm = ta.t_imm` by
    (rpt gen_tac >>
     simp[step_taint_def, mem_taint_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, EXTENSION] >>
     rpt CASE_TAC >> simp[] >> metis_tac[]) >>
  `!v owner bs sz. FLOOKUP (ld_step_prov AP AG L i) v = SOME(owner,(bs,sz)) ==>
    owner IN live` by
    (drule ld_normal_data_geometry >> strip_tac >>
     simp[ld_step_prov_def, ld_out_prov_def, ld_set_prov_def, FLOOKUP_DRESTRICT] >>
     metis_tac[]) >>
  `(!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
   (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32)` by
    (drule ld_normal_data_masks >> strip_tac >> simp[ld_step_taint_bound]) >>
  qpat_x_assum `s' = _` SUBST_ALL_TAC >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  simp[ld_normal_data_def] >>
  qpat_x_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_normal_data_def, update_var_def, ld_alloc_account_def,
       allocas_from_def, read_memory_def] >>
  strip_tac >> gvs[update_var_def] >> asm_rewrite_tac[]
QED

Finalise ld_normal_gas_backward

(* Residual readers do not write memory or any persistent taint component.
   Only the allocation-map projection of their state footprint is needed. *)
Theorem ld_residual_read_taint_nonvar:
  MEM i.inst_opcode [BYTE; SIGNEXTEND; BUMP; INITIAL_FMP; GAS;
    CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
    TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
    BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE;
    BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; SLOAD; TLOAD] /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  simp[MEM] >> strip_tac >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
  simp[mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def] >>
  simp[written_taint_def, range_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  namedCases_on `i.inst_operands` ["", "a ops1"] >> simp[] >>
  namedCases_on `ops1` ["", "b ops2"] >> simp[] >>
  namedCases_on `ops2` ["", "c ops3"] >> simp[] >>
  Cases_on `ops3` >> simp[] >> metis_tac[]
QED

Theorem ld_update_var_definedness:
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  !v. v IN V ==>
    (lookup_var v (update_var out x s) = NONE <=>
     lookup_var v (update_var out y t) = NONE)
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = out` >> simp[] >> metis_tac[]
QED

Theorem ld_update_two_vars_definedness:
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  !v. v IN V ==>
    (lookup_var v (update_var next x' (update_var out x s)) = NONE <=>
     lookup_var v (update_var next y' (update_var out y t)) = NONE)
Proof
  strip_tac >>
  `!v. v IN V ==> (lookup_var v (update_var out x s) = NONE <=>
    lookup_var v (update_var out y t) = NONE)` by
    metis_tac[ld_update_var_definedness] >>
  metis_tac[ld_update_var_definedness]
QED

Theorem ld_annotated_residual_read_operands:
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo CS vs0 /\ opaque_use_ok fn /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [BYTE; SIGNEXTEND; BUMP;
    CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
    TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
    BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE;
    BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; SLOAD; TLOAD] ==>
  !op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN V /\ ~retpc_var fn v) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!v. MEM (Var v) i.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     metis_tac[]) >>
  rpt gen_tac >> disch_tac >> conj_tac
  >- (gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
      gvs[] >> irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  conj_tac
  >- (irule ld_annotated_scalar_prov >>
      goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  irule ld_taint_operand_clean >>
  goal_assum (drule_at (Pat `taint_ok _ _ _ _`)) >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> simp[]
QED

Theorem ld_normal_residual_update_complete:
  MEM i.inst_opcode [BYTE; SIGNEXTEND; CALLER; ADDRESS; CALLVALUE; ORIGIN;
    GASPRICE; CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT;
    BASEFEE; BLOBBASEFEE; BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD;
    RETURNDATASIZE; CODESIZE; BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH;
    SLOAD; TLOAD] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  s' = update_var out x s /\ t' = update_var out y t /\
  ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t' ==>
  ld_normal_data CS fn V U lo E L H AP BP
    (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `(!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    metis_tac[ld_update_var_definedness] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     simp[ld_step_prov_def, ld_out_prov_def] >>
     irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `MEM i.inst_opcode [BYTE; SIGNEXTEND; BUMP; INITIAL_FMP; GAS;
    CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
    TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
    BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE;
    BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; SLOAD; TLOAD]` by
    (fs[MEM] >> metis_tac[]) >>
  `s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
   t'.vs_allocas = t.vs_allocas /\ t'.vs_fmp = t.vs_fmp` by simp[update_var_def] >>
  `(!q. (step_taint i s s' q).t_mem = q.t_mem /\
        (step_taint i s s' q).t_stor = q.t_stor /\
        (step_taint i s s' q).t_trans = q.t_trans /\
        (step_taint i s s' q).t_imm = q.t_imm) /\
   (!q. (step_taint i t t' q).t_mem = q.t_mem /\
        (step_taint i t t' q).t_stor = q.t_stor /\
        (step_taint i t t' q).t_trans = q.t_trans /\
        (step_taint i t t' q).t_imm = q.t_imm)` by
    metis_tac[ld_residual_read_taint_nonvar] >>
  irule ld_normal_step_vars_complete >> simp[update_var_def] >> metis_tac[]
QED

Theorem ld_normal_byte_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  o1_ctx_shape CS /\ ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [BYTE; SIGNEXTEND] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `inst_wf i` by metis_tac[ld_annotated_inst_wf] >>
  `?out. i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN U) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}` by
    (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)
       ld_annotated_residual_read_operands >>
     disch_then (qspecl_then [`lo`,`V`,`P`] mp_tac) >>
     strip_tac >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `op` mp_tac) >>
     impl_tac >- (simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
                   simp[MEM] >> strip_tac >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_owned_byte_backward >> simp[] >> metis_tac[MEM]) >>
  qexists_tac `s'` >> simp[] >>
  `?x y. s' = update_var out x s /\ t' = update_var out y t` by
    (qpat_x_assum `step_inst fuel CS i s = OK s'` mp_tac >>
     qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     simp[step_inst_non_invoke] >>
     asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
     simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  irule ld_normal_residual_update_complete >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem ld_normal_environment_read_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
    BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN U) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}` by
    (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)
       ld_annotated_residual_read_operands >>
     disch_then (qspecl_then [`lo`,`V`,`P`] mp_tac) >>
     strip_tac >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `op` mp_tac) >>
     impl_tac >- (simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
                   simp[MEM] >> strip_tac >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t /\ ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  `?s' out w. step_inst fuel CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t` by
    (drule_all ld_environment_read_backward >>
     disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >> metis_tac[]) >>
  `ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (`?s1. step_inst fuel CS i s = OK s1 /\
       ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
         (step_taint i s s1 tn) (step_taint i t t' un) s1 t'` by
       (irule ld_owned_environment_read_backward >> simp[] >> metis_tac[]) >>
     metis_tac[venomExecSemanticsTheory.exec_result_11]) >>
  qexists_tac `s'` >> simp[] >> irule ld_normal_residual_update_complete >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem ld_normal_bump_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\ i.inst_opcode = BUMP /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN U) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}` by
    (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)
       ld_annotated_residual_read_operands >>
     disch_then (qspecl_then [`lo`,`V`,`P`] mp_tac) >>
     strip_tac >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  `?s' ptr next base sz. step_inst fuel CS i s = OK s' /\
    i.inst_outputs = [ptr;next] /\
    s' = update_var next (word_add base sz) (update_var ptr base s) /\
    t' = update_var next (word_add base sz) (update_var ptr base t)` by
    (drule_all ld_bump_backward >>
     disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >> metis_tac[]) >>
  `ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (`?s1. step_inst fuel CS i s = OK s1 /\
       ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
         (step_taint i s s1 tn) (step_taint i t t' un) s1 t'` by
       (irule ld_owned_bump_backward >> simp[] >> metis_tac[]) >>
     metis_tac[venomExecSemanticsTheory.exec_result_11]) >>
  qexists_tac `s'` >> simp[] >> suspend "complete"
QED

Resume ld_normal_bump_backward[complete]:
  `(!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    metis_tac[ld_update_two_vars_definedness] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (simp[ld_step_prov_def, ld_out_prov_def] >>
     irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `MEM i.inst_opcode [BYTE; SIGNEXTEND; BUMP; INITIAL_FMP; GAS;
    CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
    TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
    BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE;
    BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; SLOAD; TLOAD]` by simp[] >>
  `s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
   t'.vs_allocas = t.vs_allocas /\ t'.vs_fmp = t.vs_fmp` by simp[update_var_def] >>
  `(!q. (step_taint i s s' q).t_mem = q.t_mem /\
        (step_taint i s s' q).t_stor = q.t_stor /\
        (step_taint i s s' q).t_trans = q.t_trans /\
        (step_taint i s s' q).t_imm = q.t_imm) /\
   (!q. (step_taint i t t' q).t_mem = q.t_mem /\
        (step_taint i t t' q).t_stor = q.t_stor /\
        (step_taint i t t' q).t_trans = q.t_trans /\
        (step_taint i t t' q).t_imm = q.t_imm)` by
    metis_tac[ld_residual_read_taint_nonvar] >>
  irule ld_normal_step_vars_complete >>
  gvs[update_var_def] >> asm_rewrite_tac[]
QED

Finalise ld_normal_bump_backward

Theorem ld_normal_storage_read_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [SLOAD; TLOAD] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN U) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}` by
    (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)
       ld_annotated_residual_read_operands >>
     disch_then (qspecl_then [`lo`,`V`,`P`] mp_tac) >>
     strip_tac >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `op` mp_tac) >>
     impl_tac >- (simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
                   simp[MEM] >> strip_tac >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t /\ ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  `?s' out x y. step_inst fuel CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out x s /\ t' = update_var out y t` by
    (drule_all ld_storage_read_backward >>
     disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >> metis_tac[]) >>
  `ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (`?s1. step_inst fuel CS i s = OK s1 /\
       ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
         (step_taint i s s1 tn) (step_taint i t t' un) s1 t'` by
       (irule ld_owned_storage_read_backward >> simp[] >> metis_tac[]) >>
     metis_tac[venomExecSemanticsTheory.exec_result_11]) >>
  qexists_tac `s'` >> simp[] >> irule ld_normal_residual_update_complete >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem ld_account_read_backward:
  MEM i.inst_opcode [BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH] /\
  ld_shared_state tn un s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' out w. step_inst fuelS CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t
Proof
  strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  `!a. (lookup_account a s.vs_accounts).balance =
       (lookup_account a t.vs_accounts).balance /\
       (lookup_account a s.vs_accounts).code = (lookup_account a t.vs_accounts).code /\
       account_empty (lookup_account a s.vs_accounts) =
       account_empty (lookup_account a t.vs_accounts)` by
    (drule ld_shared_state_nonstorage >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a` mp_tac) >>
     simp[lookup_account_def] >> disch_tac >>
     qsuff_tac
       `(s.vs_accounts a with storage := (t.vs_accounts a).storage).balance =
          (t.vs_accounts a).balance /\
        (s.vs_accounts a with storage := (t.vs_accounts a).storage).code =
          (t.vs_accounts a).code /\
        account_empty (s.vs_accounts a with storage := (t.vs_accounts a).storage) =
          account_empty (t.vs_accounts a)`
     >- simp[account_empty_def] >>
     rpt conj_tac >> AP_TERM_TAC >> simp[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> strip_tac >>
  FIRST [drule_at (Pat `exec_read0 _ _ _ = _`) ld_exec_read0_backward,
         drule_at (Pat `exec_read1 _ _ _ = _`) ld_exec_read1_backward] >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  qexists_tac `w` >> simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> simp[]
QED

Theorem ld_owned_account_read_backward:
  MEM i.inst_opcode [BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH] /\
  ld_shared_state tn un s t /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE /\ op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  drule_all ld_account_read_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >> gvs[] >>
  `!st ta. out_taint ta i st = {}` by
    (rpt gen_tac >> simp[out_taint_def] >> rpt CASE_TAC >> simp[]) >>
  `ld_owned_value E NONE NONE {} {} w w` by
    simp[ld_owned_value_def, ld_mask_word_def] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
       ld_owned_vars_def, op_taint_def]
QED

Theorem ld_normal_account_read_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN U) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}` by
    (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)
       ld_annotated_residual_read_operands >>
     disch_then (qspecl_then [`lo`,`V`,`P`] mp_tac) >>
     strip_tac >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `op` mp_tac) >>
     impl_tac >- (simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
                   simp[MEM] >> strip_tac >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t /\ ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  `?s' out w. step_inst fuel CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t` by
    (drule_all ld_account_read_backward >>
     disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >> metis_tac[]) >>
  `ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (`?s1. step_inst fuel CS i s = OK s1 /\
       ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
         (step_taint i s s1 tn) (step_taint i t t' un) s1 t'` by
       (irule ld_owned_account_read_backward >> simp[] >> metis_tac[]) >>
     metis_tac[venomExecSemanticsTheory.exec_result_11]) >>
  qexists_tac `s'` >> simp[] >> irule ld_normal_residual_update_complete >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> gvs[] >>
  metis_tac[]
QED


Theorem ld_storage_write_footprint:
  MEM i.inst_opcode [SSTORE; TSTORE] /\
  (i.inst_opcode = SSTORE ==> s' = sstore key x s) /\
  (i.inst_opcode = TSTORE ==> s' = tstore key x s) ==>
  (s' with <|vs_accounts := s.vs_accounts; vs_transient := s.vs_transient|>) = s /\
  (!addr. addr <> s.vs_call_ctx.cc_address ==>
    (s'.vs_accounts addr).storage = (s.vs_accounts addr).storage /\
    s'.vs_transient addr = s.vs_transient addr)
Proof
  strip_tac >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >> gvs[sstore_def, tstore_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem ld_storage_write_annotation:
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_outputs = [] /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  ld_step_prov AP AG L i = AG /\
  (step_taint i s s' tn).t_var = tn.t_var /\
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  gvs[ld_step_prov_def, step_taint_def, mem_taint_def, imm_taint_def,
      new_site_bytes_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, range_bytes_def, set_var_taint_def,
      ld_set_prov_def, DRESTRICT_UNIV, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt CASE_TAC >> simp[]
QED

Theorem ld_storage_write_taint_inclusions:
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [a;v] /\
  eval_operand a s = SOME key /\ eval_operand a t = SOME key /\
  op_taint un v SUBSET op_taint tn v /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm ==>
  (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
  (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
  (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm
Proof
  strip_tac >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  gvs[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  metis_tac[ld_key_update_mono]
QED

Theorem ld_normal_storage_write_complete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [a;v] /\
  i.inst_outputs = [] /\
  eval_operand a s = SOME key /\ eval_operand a t = SOME key /\
  op_taint un v SUBSET op_taint tn v /\
  (i.inst_opcode = SSTORE ==> s' = sstore key x s /\ t' = sstore key y t) /\
  (i.inst_opcode = TSTORE ==> s' = tstore key x s /\ t' = tstore key y t) /\
  ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t' ==>
  ld_normal_data CS fn V U lo E L H AP BP
    (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def, ld_shared_state_def]) >>
  `(s' with <|vs_accounts := s.vs_accounts; vs_transient := s.vs_transient|>) = s /\
   (!addr. addr <> s.vs_call_ctx.cc_address ==>
     (s'.vs_accounts addr).storage = (s.vs_accounts addr).storage /\
     s'.vs_transient addr = s.vs_transient addr)` by
    (irule ld_storage_write_footprint >> metis_tac[]) >>
  `(t' with <|vs_accounts := t.vs_accounts; vs_transient := t.vs_transient|>) = t /\
   (!addr. addr <> t.vs_call_ctx.cc_address ==>
     (t'.vs_accounts addr).storage = (t.vs_accounts addr).storage /\
     t'.vs_transient addr = t.vs_transient addr)` by
    (irule ld_storage_write_footprint >> metis_tac[]) >>
  `s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
   t'.vs_allocas = t.vs_allocas /\ t'.vs_fmp = t.vs_fmp /\
   s'.vs_call_ctx = s.vs_call_ctx` by
    (dxrule ld_storage_restore_normalize >> disch_then SUBST_ALL_TAC >>
     dxrule ld_storage_restore_normalize >> disch_then SUBST_ALL_TAC >> simp[]) >>
  `ld_step_prov AP AG L i = AG /\
   (step_taint i s s' tn).t_var = tn.t_var /\
   (step_taint i s s' tn).t_mem = tn.t_mem` by
    metis_tac[ld_storage_write_annotation] >>
  `ld_step_prov BP BH H i = BH /\
   (step_taint i t t' un).t_var = un.t_var /\
   (step_taint i t t' un).t_mem = un.t_mem` by
    metis_tac[ld_storage_write_annotation] >>
  drule ld_normal_data_companions >> strip_tac >>
  drule ld_normal_data_frame >> strip_tac >>
  `un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
   un.t_imm SUBSET tn.t_imm` by metis_tac[ld_normal_data_masks] >>
  `(step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
   (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
   (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm` by
    (irule ld_storage_write_taint_inclusions >> simp[] >> metis_tac[]) >>
  simp[] >> irule ld_normal_data_storage_transport >> simp[] >>
  qexistsl_tac [`s`,`t`,`tn`,`un`] >> simp[] >>
  dxrule ld_storage_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_storage_restore_normalize >> disch_then SUBST_ALL_TAC >> simp[]
QED

Theorem ld_annotated_storage_operands:
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo CS vs0 /\ opaque_use_ok fn /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [a;v] ==>
  (!op. MEM op i.inst_operands ==>
    (!w. op = Var w ==> w IN V /\ ~retpc_var fn w) /\ ld_op_prov AG op = NONE) /\
  op_taint tn a = {}
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!w. MEM (Var w) i.inst_operands ==> w NOTIN fn_pv P fn` by
    (qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     metis_tac[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >> conj_tac
      >- (gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
          gvs[] >> irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
      irule ld_annotated_scalar_prov >>
      goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  irule ld_taint_store_address_clean >>
  qexistsl_tac [`fn`,`i`,`s`,`v`] >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> metis_tac[]
QED

Theorem ld_normal_storage_write_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [SSTORE; TSTORE] /\ inst_wf i /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `?a v. i.inst_operands = [a;v] /\ i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     simp[inst_wf_def] >> strip_tac >>
     namedCases_on `i.inst_operands` ["", "a ops"] >> gvs[] >>
     namedCases_on `ops` ["", "v rest"] >> gvs[] >> Cases_on `rest` >> gvs[]) >>
  `(!op. MEM op i.inst_operands ==> (!w. op = Var w ==> w IN U) /\
      ld_op_prov AG op = NONE) /\ op_taint tn a = {}` by
    (drule_all ld_annotated_storage_operands >> simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t /\ ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `eval_operand a s = eval_operand a t` by
    (irule ld_owned_operand_clean >>
     qexistsl_tac [`AG`,`BH`,`E`,`U`,`tn`,`un`] >> simp[] >> metis_tac[MEM]) >>
  `?key y. eval_operand a t = SOME key /\ eval_operand v t = SOME y` by
    (qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     simp[Once step_inst_non_invoke, SimpLHS] >>
     asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
     simp[exec_write2_def, eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
  `?x. eval_operand v s = SOME x` by
    (`eval_operand v s = NONE <=> eval_operand v t = NONE` by
       (irule ld_owned_operand_defined >>
        qexistsl_tac [`AG`,`BH`,`E`,`U`,`tn`,`un`] >> simp[] >> metis_tac[MEM]) >>
     Cases_on `eval_operand v s` >> gvs[]) >>
  `ld_owned_value E (ld_op_prov AG v) (ld_op_prov BH v)
    (op_taint tn v) (op_taint un v) x y` by
    (irule ld_owned_operand_value >> qexistsl_tac [`U`,`s`,`t`] >>
     simp[] >> metis_tac[MEM]) >>
  `word_agree_except (op_taint tn v INTER count 32) x y /\
   op_taint un v SUBSET op_taint tn v` by
    (`ld_op_prov AG v = NONE` by metis_tac[MEM] >>
     fs[ld_owned_value_def, ld_mask_word_def, word_agree_except_def] >> metis_tac[]) >>
  suspend "finish"
QED

Resume ld_normal_storage_write_backward[finish]:
  `s.vs_call_ctx = t.vs_call_ctx` by fs[ld_shared_state_def] >>
  drule ld_normal_data_companions >> strip_tac >>
  `?s'. step_inst fuel CS i s = OK s' /\
    (i.inst_opcode = SSTORE ==> s' = sstore key x s /\ t' = sstore key y t) /\
    (i.inst_opcode = TSTORE ==> s' = tstore key x s /\ t' = tstore key y t)` by
    (irule ld_storage_write_backward >> simp[] >> metis_tac[]) >>
  `ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (`?s1. step_inst fuel CS i s = OK s1 /\
      ld_shared_state (step_taint i s s1 tn) (step_taint i t t' un) s1 t'` by
      (irule ld_shared_storage_write_backward >> simp[] >> metis_tac[]) >>
     metis_tac[venomExecSemanticsTheory.exec_result_11]) >>
  qexists_tac `s'` >> simp[] >>
  irule ld_normal_storage_write_complete >> simp[] >> metis_tac[]
QED

Finalise ld_normal_storage_write_backward
