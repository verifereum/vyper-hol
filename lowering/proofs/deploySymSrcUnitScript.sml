(* The deployment unit's source-side static facts, for the asm_opt_finalizer
 * case of e2e_deploy_correctness (used by e2eDeployCorrectness).
 *
 * TOP-LEVEL: lower_vyper_deploy_unit_sym_src_ok.
 *)
Theory deploySymSrcUnit
Ancestors
  deploySymSrcInstructions deploySymSrcData deploySymSrcHistory
  o1LabelFlowSourceBoundary ctorDeployDefs deployEntryLayout
  e2eProducers codegenSymRel compileVyper list context vyperTypeContract constSubstCorrect

(* The deployment unit's source-side static facts: no CODESIZE, CODECOPY
   only from runtime_begin, no code_end label yet, a byte-only data segment,
   and runtime_begin among its headers. *)
Theorem lower_vyper_deploy_unit_sym_src_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan layouts addr art imms A.
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ supported_program_deploy tops /\
  ~program_reads_self_code tops ==>
  label_flow_ok dunit.cu_context /\
  (!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) dunit.cu_data_segment /\
  ((?fn inst. MEM fn dunit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") dunit.cu_data_segment)
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    gvs[deploy_phases_def] >>
  `!fn. MEM fn dunit.cu_context.ctx_functions ==>
        EVERY deploy_sym_inst (fn_insts fn)` by
    metis_tac[deploy_sym_deploy_insts] >>
  fs[EVERY_MEM, deploy_sym_inst_def] >>
  `!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
      ~MEM (Label "code_end") inst.inst_operands` by metis_tac[] >>
  conj_tac
  >- (drule label_flow_ok_seed_free >>
      disch_then (fn th => simp[th]) >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (drule lower_vyper_deploy_unit_data_bytes >> simp[EVERY_MEM]) >>
  drule lower_vyper_deploy_unit_runtime_section >>
  simp[EXISTS_MEM] >> rpt strip_tac >>
  qexists `<| ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc] |>` >>
  simp[]
QED
