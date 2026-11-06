(* Entry after a pre-existing PHI is an absolute-PC continuation. *)
Theory normalizationPhiEntryProbe
Ancestors
  externalReturnNormalizeRun fragExec memContinuation compileEnv
  venomExecSemantics venomInst venomState emitHelper context

Theorem normalization_allocation_after_phi:
  sb.cs_current_insts = [mk_inst pid PHI [] []; mk_inst nid ADD [] []] /\
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sb.cs_next_var)]) s (n2w n : bytes32) = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  phi_prefix_length sc.cs_current_insts = 1 /\
  mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sc.cs_current_insts)
Proof
  strip_tac >> drule_all normalize_alloc_mem_cont >> strip_tac >> simp[] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]
QED
