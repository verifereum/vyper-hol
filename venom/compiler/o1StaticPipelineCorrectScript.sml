Theory o1StaticPipelineCorrect
Ancestors
  o1PipelineCorrect o1PassContract o1RequestContract
  unitMemInv ptrDiscipline lowerDloadDefs staticAbortDefs
  venomState venomInst venomExecSemantics list

(* TEMPORARY: awaiting the proved static O1 composition port. *)
Theorem run_venom_pipeline_fuel_static_abort:
  !D lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs_out /\ vs_out.vs_fmp = vs_out.vs_initial_fmp /\
    code_layout_valid vs_out /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "runtime_begin") inst.inst_operands) /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs_out.vs_initial_fmp) ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim_fuel (cfg_norm_fuel out.po_unit.cu_context) D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       (o1_lowered_inv out.po_unit.cu_context vs_out \/
        ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                     lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s) out.po_unit.cu_context vs_out) /\
         !fuel. terminates (run_context fuel unit.cu_context vs_in) ==>
                ?u. run_context fuel unit.cu_context vs_in = Abort ExHalt_abort u)))
Proof
  cheat
QED

(* TEMPORARY: awaiting the proved static O1 composition port. *)
Theorem run_venom_pipeline_correct_static_abort:
  !D lo rpolicy unit out vs_out.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs_out /\ vs_out.vs_fmp = vs_out.vs_initial_fmp /\
    code_layout_valid vs_out /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "runtime_begin") inst.inst_operands) /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs_out.vs_initial_fmp) ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       ctx_abort_rq D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       (o1_lowered_inv out.po_unit.cu_context vs_out \/
        ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                     lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s) out.po_unit.cu_context vs_out) /\
         !fuel. terminates (run_context fuel unit.cu_context vs_in) ==>
                ?u. run_context fuel unit.cu_context vs_in = Abort ExHalt_abort u)))
Proof
  cheat
QED
