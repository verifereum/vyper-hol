Theory runtimeSymSrcInstructions
Ancestors
  runtimeSymSrcPrimitives runtimeSymSrcExpressions runtimeSymSrcStatements
  runtimeSymSrcRuntimeBoundary runtimeSymSrcDynarrayAppend runtimeSymSrcAbiEncode
  runtimeSymSrcTargetDomains runtimeSymSrcModuleArgPreservation
  runtimeSymSrcGeneratorContracts runtimeSymSrcInterfaces runtimeSymSrcContext
  list supportedStmts supportedExprTraverse supportedExprs vyperTypeContract constSubstCorrect

Theorem runtime_sym_expr_closed:
  !tops ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e
Proof
  metis_tac[runtime_sym_expression_contracts, runtime_sym_generators]
QED


Theorem runtime_sym_assignment_ptr_closed:
  runtime_sym_env tops ce /\ supported_assignment tops bs (BaseTarget bt) e /\
  ~supported_target_exists is_self_code bt /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >>
  mp_tac runtime_sym_generators_target_ptr >>
  simp[runtime_sym_generators, runtime_sym_target_ptr_clause_def] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  simp[runtime_sym_expr_closed] >>
  metis_tac[runtime_sym_assignment_target_domain]
QED

Theorem runtime_sym_target_ptr_closed:
  runtime_sym_env tops ce /\
  (supported_target tops bs bt \/ supported_aug_target tops bs bt) /\
  ~supported_target_exists is_self_code bt /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >>
  mp_tac runtime_sym_generators_target_ptr >>
  simp[runtime_sym_generators, runtime_sym_target_ptr_clause_def] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  simp[runtime_sym_expr_closed] >>
  metis_tac[runtime_sym_supported_target_domain]
QED

Theorem runtime_sym_stmts_closed:
  !tops stmts bs ce lc ty.
    runtime_sym_stmts_contract tops bs compile_stmts ce lc ty stmts
Proof
  gen_tac >> match_mp_tac runtime_sym_stmts >>
  conj_tac >- simp[runtime_sym_expr_closed] >>
  conj_tac >- metis_tac[runtime_sym_assignment_ptr_closed] >>
  conj_tac >- metis_tac[runtime_sym_target_ptr_closed] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      mp_tac runtime_sym_closed_target_ptr >>
      simp[runtime_sym_target_ptr_clause_def] >>
      disch_then irule >> goal_assum (drule_at Any) >>
      simp[runtime_sym_expr_closed] >>
      Cases_on `target` >>
      gvs[supported_append_target_def, supported_target_exists_indices,
          target_indices_def, EVERY_APPEND, EXISTS_APPEND, EVERY_MEM, EXISTS_MEM] >>
      metis_tac[CONJUNCT1 runtime_sym_pure_occurrence_domain]) >>
  conj_tac >- metis_tac[runtime_sym_dynarray_append] >>
  metis_tac[runtime_sym_abi_encode_to_buf]
QED

Theorem runtime_sym_runtime_insts:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
    `mode` |-> `mode`, `layouts` |-> `layouts`, `addr` |-> `addr`,
    `art` |-> `art`, `imms` |-> `imms`, `A` |-> `A`] runtime_sym_runtime_boundary) >>
  simp[runtime_sym_stmts_closed] >>
  impl_tac >-
    (conj_tac >- metis_tac[runtime_sym_alloc_buffer] >>
     conj_tac >- metis_tac[runtime_sym_decode_args] >>
     metis_tac[runtime_sym_fixed_region_with_id]) >>
  simp[]
QED

Theorem runtime_sym_runtime_no_codesize:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
  inst.inst_opcode <> CODESIZE
Proof
  strip_tac >> drule_all runtime_sym_runtime_insts >>
  simp[EVERY_MEM, runtime_sym_inst_def] >> metis_tac[]
QED

Theorem runtime_sym_runtime_codecopy_source:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = CODECOPY ==>
  ?dst sz. inst.inst_operands = [dst; Label "runtime_begin"; sz]
Proof
  strip_tac >> drule_all runtime_sym_runtime_insts >>
  simp[EVERY_MEM, runtime_sym_inst_def] >> metis_tac[]
QED

Theorem runtime_sym_runtime_no_code_end:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
  ~MEM (Label "code_end") inst.inst_operands
Proof
  strip_tac >> drule_all runtime_sym_runtime_insts >>
  simp[EVERY_MEM, runtime_sym_inst_def] >> metis_tac[]
QED
