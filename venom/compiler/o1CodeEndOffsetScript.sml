Theory o1CodeEndOffset
Ancestors
  o1PipelineCorrect codegenSymRel o1PassContract contextRawReachable
  contextPlanLayoutProps unitMemInv ptrDiscipline stepWriteFootprint
  memSafeRun lowerDloadDefs

(* HELD ADMISSION SEQ-4285: the reached CODECOPY bound awaits its O1
   pipeline transport proof. Pure ADDs may execute before a failing call. *)
Theorem o1_pipeline_code_end_offset_ok:
  !D lo rpolicy unit out vs_out.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "code_end") inst.inst_operands) /\
    LENGTH vs_out.vs_data_section < dimword (:256) DIV 2
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vs_in.vs_code /\
                               s.vs_data_section = vs_in.vs_data_section)
         unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out /\
       code_end_offset_ok (raw_reachable vs_out) out.po_unit.cu_context)
Proof
  cheat
QED
