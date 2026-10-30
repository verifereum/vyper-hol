(* TOP-LEVEL: the actual output ALLOCA discharges the no-PHI continuation
   needed by checked recursive Log packing. No encoder-cut state is assumed. *)
Theory abiLogPackingBoundary
Ancestors
  typedCopyStateFrame
  abiBufferAllocationCode typedLogSplitPath typedCopyContract typedLogArgs
  typedSArrayDynInvariant memoryValueDefs valueEncoding
  context stmtLowering compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem
  fragExec fragBlockPath venomExecSemantics venomState venomInst list rich_list words

Theorem compile_alloc_buffer_continuation:
  !capacity cs buf cs' func.
    compile_alloc_buffer capacity cs = (buf,cs') /\ fn_has_code cs cs' func ==>
    cut_continuation_no_phi cs func
Proof
  rpt gen_tac >> strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  simp_tac bool_ss [cut_continuation_no_phi_def] >> DISCH_TAC >>
  fs[fn_has_code_def] >>
  qmatch_assum_rename_tac `lookup_block cs.cs_current_bb func.fn_blocks = SOME bb` >>
  Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem checked_compile_split_log_data_allocation_boundary:
  !tops in_deploy layouts addr art ctx func cenv flags fts args ftvs atvs buf field_offset
    cs ret cs' capacity abi_buf encode_cut.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    compile_log_store_data cenv (SND (split_log_ops args flags))
      (log_non_indexed_types flags fts) buf field_offset cs = (ret,cs') /\
    compile_alloc_buffer capacity cs' = (abi_buf,encode_cut) /\ fn_has_code cs' encode_cut func ==>
    !ss vs buf_addr.
      fn_has_code cs cs' func /\
      ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
      log_args_rel args atvs vs ss /\
      log_args_safe args atvs ss (w2n buf_addr + field_offset)
        (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
      eval_operand buf ss = SOME buf_addr /\
      w2n buf_addr + field_offset + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) /\
      EVERY (\name. buf <> Var name)
        (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) /\
      log_args_avoid args (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
      ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
        out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
        values_have_types (select_log_args F flags ftvs) (select_log_args F flags vs) /\
        memory_tuple_rel (select_log_args F flags ftvs) (select_log_args F flags vs)
          (w2n buf_addr + field_offset) out.vs_memory /\
        log_args_rel args atvs vs out /\
        log_args_safe args atvs out (w2n buf_addr + field_offset)
          (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
        array_copy_frame (TupleTV (select_log_args F flags ftvs)) 1
          (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
        (!arg_op. EVERY (\name. arg_op <> Var name)
          (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
          eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_continuation >> DISCH_TAC >>
  drule_all_then (qspecl_then [`ctx`, `func`] mp_tac)
    checked_compile_split_log_data_store_contract >>
  simp[split_log_data_store_contract_def]
QED
