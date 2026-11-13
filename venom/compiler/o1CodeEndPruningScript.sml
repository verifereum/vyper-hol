Theory o1CodeEndPruning
Ancestors
  o1PipelineCompose fcgPruning unitMemInv ctorDeployDload

(* Pruning retains exact states and instructions.  The section predicate
   ignores the context, so the generic invariant transport applies directly. *)
Theorem o1_code_end_prune_section:
  fcg = fcg_analyze unit.cu_context /\
  o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
             s.vs_code = v.vs_code /\
             s.vs_data_section = v.vs_data_section) unit.cu_context vs ==>
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
             s.vs_code = v.vs_code /\
             s.vs_data_section = v.vs_data_section)
    (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  mp_tac (Q.INST [`M` |-> `\ctx fn inst s.
    inst_dload_in_section inst s /\ s.vs_code = v.vs_code /\
    s.vs_data_section = v.vs_data_section`] o1_prune_sim) >>
  simp[]
QED

(* No assumptions on the call graph are needed for this syntactic fact. *)
Theorem o1_code_end_prune_no_label:
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\
             MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) ==>
  (!fn inst.
    MEM fn (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions /\
    MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands)
Proof
  simp[MEM_prune_unit_fcg_unreachable_functions] >> metis_tac[]
QED
