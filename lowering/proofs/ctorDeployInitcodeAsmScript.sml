(* The deployment bytecode fits the assembler's 2-byte label pushes.
 * TOP-LEVEL: deploy_bc_size_bounded.
 * Helper: deploy_encoding_total_length.
 * codegen_assembly accepts only programs with asm_symbols_ok, which bounds
 * SUM (MAP asm_inst_size prog) below 65536, and on an encoding-wf program
 * (codegen_assembly_asm_encoding_wf, from the output unit's shape) the
 * assembled length is exactly that sum.
 *)
Theory ctorDeployInitcodeAsm
Ancestors
  ctorDeployDefs ctorDeployShape ctorDeployDefsReach o1PipelineCorrect
  codegen codegenEncodingWf asmToBytecodeProofs asmWf symbolResolve list
  rich_list

Theorem deploy_encoding_total_length:
  asm_encoding_wf prog ==>
  LENGTH (assemble prog) = SUM (MAP asm_inst_size prog)
Proof
  strip_tac >> Cases_on `compute_label_offsets prog` >>
  simp[assemble_def, LENGTH_FLAT, MAP_MAP_o] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[MEM_EL] >>
  rpt strip_tac >> irule ewi_length >>
  drule_all asm_encoding_wf_el >> gvs[]
QED

Theorem deploy_bc_size_bounded:
  !policy tops deploy_bc runtime_bc arts am tx.
    deploy_phases policy tops (deploy_bc, runtime_bc) arts /\
    deploy_source_ok tops am tx ==>
    LENGTH deploy_bc < 65536
Proof
  rpt gen_tac >> PairCases_on `arts` >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `unit_shape_ok arts2.po_unit` by
    (irule run_venom_pipeline_output_shape >>
     gvs[deploy_phases_def] >> metis_tac[]) >>
  `codegen_assembly arts0 arts2.po_unit = SOME arts3 /\
   deploy_bc = assemble arts3` by gvs[deploy_phases_def] >>
  `asm_symbols_ok arts3` by
    (qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
     simp[codegen_assembly_def, AllCaseEqs()] >> rw[] >> simp[]) >>
  drule_all codegen_assembly_asm_encoding_wf >> strip_tac >>
  drule deploy_encoding_total_length >> gvs[asm_symbols_ok_def]
QED
