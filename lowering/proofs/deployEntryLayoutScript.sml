(* Generated data labels are available to the actual constructor entry state. *)
Theory deployEntryLayout
Ancestors
  e2eEntry e2eProducers asmDataSuffixProps codegen asmIR symbolResolve
  compileVyper vyperCompiler o1PipelineCorrect venomPipelineData
  finite_map list ctorDeployDefs o1PassContract fnPlanPlaceRevertPostamble
  ctorDeployLoweringDefs

Theorem data_header_fold_present[local]:
  !prog pc labels lbl.
    IS_SOME (FLOOKUP labels lbl) \/ MEM (AsmDataHeader lbl) prog ==>
    IS_SOME (FLOOKUP
      (SND (FOLDL (\(pc : num, labels : (string, num) fmap) inst.
        (pc + asm_inst_size inst,
          case inst of
            AsmLabel key => labels |+ (key, pc)
          | AsmDataHeader key => labels |+ (key, pc)
          | _ => labels)) (pc, labels) prog)) lbl)
Proof
  Induct_on `prog`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `h`
  >> simp[FLOOKUP_UPDATE]
  >> rpt strip_tac
  >> first_x_assum irule
  >> simp[FLOOKUP_UPDATE]
  >> IF_CASES_TAC >> simp[]
QED

Theorem data_header_offset_present[local]:
  !prog lbl. MEM (AsmDataHeader lbl) prog ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) lbl)
Proof
  rpt strip_tac
  >> simp[compute_label_offsets_def]
  >> irule data_header_fold_present
  >> simp[]
QED

Theorem generated_entry_data_label:
  !policy cu prog ds bytes cplan es.
    codegen_assembly policy cu = SOME prog /\
    MEM ds cu.cu_data_segment ==>
    IS_SOME (FLOOKUP
      (entry_venom_state (prog ++ [AsmDataItem bytes]) cplan es).vs_labels
      ds.ds_label)
Proof
  rpt strip_tac
  >> `MEM (AsmDataHeader ds.ds_label) prog` by
    (drule codegen_assembly_success_shape
     >> strip_tac
     >> gvs[data_segment_asm_def, MEM_FLAT, MEM_MAP]
     >> metis_tac[data_section_asm_def, MEM])
  >> drule data_header_offset_present
  >> simp[entry_venom_state_frame_fields, data_suffix_label_offsets]
  >> Cases_on `FLOOKUP (SND (compute_label_offsets prog)) ds.ds_label`
  >> simp[]
QED

Theorem run_deploy_lowering_runtime_section[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  MEM <| ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc] |>
    unit.cu_data_segment
Proof
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem lower_vyper_deploy_unit_runtime_section:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
    MEM <| ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc] |>
      unit.cu_data_segment
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_runtime_section >> simp[]
QED

Theorem deploy_o1_data_bytes_section[local]:
  !rpolicy unit out label bytes.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
      unit.cu_data_segment ==>
    MEM <| ds_label := label; ds_items := [DataBytes bytes] |>
      out.po_unit.cu_data_segment
Proof
  simp[o1PipelineCorrectTheory.o1_pipeline_def] >>
  metis_tac[run_venom_pipeline_data_bytes_section]
QED

Theorem lower_vyper_deploy_unit_entry_runtime_label:
  !tops rpolicy runtime_bc unit out prog args cplan es.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog ==>
    IS_SOME (FLOOKUP
      (entry_venom_state (prog ++ [AsmDataItem args]) cplan es).vs_labels
      "runtime_begin")
Proof
  rpt strip_tac >>
  drule lower_vyper_deploy_unit_runtime_section >> strip_tac >>
  drule_all deploy_o1_data_bytes_section >> strip_tac >>
  drule_all generated_entry_data_label >> simp[]
QED

Theorem deploy_phases_runtime_label:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,unit,out,prog,cplan) ==>
  IS_SOME (FLOOKUP (lo_reloc prog prog) "runtime_begin")
Proof
  simp[deploy_phases_def] >> strip_tac >>
  drule_all lower_vyper_deploy_unit_entry_runtime_label >>
  disch_then (qspecl_then [`[]`, `cplan`, `ARB`] mp_tac) >>
  PURE_REWRITE_TAC [entry_venom_state_frame_fields, data_suffix_label_offsets,
                    lo_reloc_refl, FLOOKUP_o_f, optionTheory.IS_SOME_MAP] >>
  qpat_assum `prog = _` SUBST_ALL_TAC >> simp_tac bool_ss []
QED

Theorem deploy_entry_runtime_label_own:
  gas_variant vs
    (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
  IS_SOME (FLOOKUP (lo_reloc prog prog') "runtime_begin") ==>
  IS_SOME (FLOOKUP vs.vs_labels "runtime_begin")
Proof
  strip_tac >>
  qpat_assum `gas_variant _ _` (mp_tac o PURE_REWRITE_RULE [gas_variant_def]) >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
  simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def] >>
  disch_then (fn th => rewrite_tac [GSYM th]) >>
  Cases_on `FLOOKUP (lo_reloc prog prog') "runtime_begin"` >>
  fs[FLOOKUP_o_f]
QED
