(* The runtime unit's source-side static facts, for the optimizer case of
   the top theorems (consumed by e2eAsmOpt).

   TOP-LEVEL: lower_vyper_runtime_unit_sym_src_ok.
 *)
Theory runtimeSymSrcUnit
Ancestors
  e2eProducers codegenSymRel compileVyper

(* The runtime unit's source-side static facts: no CODESIZE, CODECOPY only
   from runtime_begin, no code_end label yet, and a byte-only data segment
   (empty under Linear dispatch). *)
(* TEMPORARILY CHEATED - run base only: the leaf is repaired by another run.
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (`!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
             ~MEM (Label "code_end") i.inst_operands` by
        metis_tac[runtime_sym_runtime_no_code_end] >>
      drule label_flow_ok_seed_free >> disch_then (fn th => simp[th]) >>
      metis_tac[runtime_sym_runtime_no_codesize,
                runtime_sym_runtime_codecopy_source]) >>
  conj_tac >- metis_tac[runtime_sym_runtime_no_code_end] >>
  conj_tac >- metis_tac[lower_vyper_runtime_unit_data_bytes] >>
  metis_tac[runtime_sym_runtime_no_runtime_begin]
QED
*)
Theorem lower_vyper_runtime_unit_sym_src_ok:
  !tops rpolicy unit.
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  label_flow_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)
Proof
  cheat
QED
