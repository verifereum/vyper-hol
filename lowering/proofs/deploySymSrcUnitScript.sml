(* The deployment unit's source-side static facts, for the asm_opt_finalizer
 * case of e2e_deploy_correctness (used by e2eDeployCorrectness).
 *
 * TOP-LEVEL: lower_vyper_deploy_unit_sym_src_ok.
 *)
Theory deploySymSrcUnit
Ancestors
  runtimeSymSrcUnit runtimeSymSrcInstructions runtimeSymSrcData
  o1LabelFlowSourceBoundary ctorDeployDefs deployEntryLayout
  e2eProducers codegenSymRel compileVyper

(* The deployment unit's source-side static facts: no CODESIZE, CODECOPY
   only from runtime_begin, no code_end label yet, a byte-only data segment,
   and runtime_begin among its headers. *)
Theorem lower_vyper_deploy_unit_sym_src_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
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
  cheat
QED
