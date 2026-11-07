(* Package metadata at the source/target internal-call boundary. *)
Theory bodyIntCallPackageBoundary
Ancestors
  compileEnv entryStateRel structFieldsProps vyperAST fragGasFocus fragExec
  venomExecSemantics venomState

Theorem internal_return_buffer_memory_size:
  compute_func_info
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ret
    (type_mem_bytes (get_struct_fields ce.ce_struct_fields) ret) argtys =
      (0,rbs,pvs) /\
  ret <> NoneT /\ struct_args_unique tops /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  evaluate_type (type_env tops) ret = SOME tv ==>
  rbs = type_memory_size tv
Proof
  strip_tac >>
  `type_mem_bytes (get_struct_fields ce.ce_struct_fields) ret =
     type_memory_size tv` by
    (rewrite_tac[type_mem_bytes_type_memory_bytes] >>
     irule make_struct_fields_map_memory_size >> metis_tac[]) >>
  Cases_on `ret` >> gvs[compute_func_info_def]
QED

Theorem gas_invoke_entry_no_phi:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name,ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME argv /\
  setup_callee callee argv s = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  phi_prefix_length first.bb_instructions = 0 /\ ~setup.vs_halted ==>
  gas_invoke_entry (ctx,func) s callee (setup with vs_inst_idx := 0)
Proof
  strip_tac >> simp[gas_invoke_entry_def] >>
  qexists_tac `setup` >>
  simp[eval_phis_no_phi]
QED
