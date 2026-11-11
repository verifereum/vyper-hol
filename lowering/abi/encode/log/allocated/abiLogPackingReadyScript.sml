(* TOP-LEVEL: checked packing retains the allocator resources, topic values
   and source pointer needed by the actual following allocation and encoder. *)
Theory abiLogPackingReady
Ancestors
  vyperEventArgCompat
  typedCopyStateFrame typedLogStoreCode typedLogSplitComplete abiLogReady abiFieldOperands
  typeLayoutProps typedCopyProducer
  abiAllocatedState abiAllocatorState abiAllocationFrame abiAllocatedWindows
  abiStateFrame memoryValueSnapshot valueEncoding context compileEnv venomState list words

Theorem abi_log_packing_allocator_frame:
  !before after. copy_state_frame before after ==>
    (alloca_inv after <=> alloca_inv before) /\
    (!id count. abi_alloca_request_ok id count after <=> abi_alloca_request_ok id count before) /\
    (!id offset count. abi_allocated_window after id offset count <=>
      abi_allocated_window before id offset count) /\
    after.vs_alloca_next = before.vs_alloca_next /\
    (!id. memory_snapshot_addr id after = memory_snapshot_addr id before)
Proof
  rpt gen_tac >> DISCH_TAC >>
  `abi_allocator_state after = abi_allocator_state before` by
    fs[copy_state_frame_def, abi_allocator_state_eq] >>
  drule abi_alloca_inv_state >> DISCH_TAC >>
  drule abi_allocated_window_state >> DISCH_TAC >>
  drule abi_alloca_request_ok_state >> DISCH_TAC >>
  fs[copy_state_frame_def, memory_snapshot_addr_def]
QED

Theorem abi_log_packing_operand_frame:
  !cenv ops tys buf field_offset cs ret cs' before after src topic_ops topics root_addr.
    compile_log_store_data cenv ops tys buf field_offset cs = (ret,cs') /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
      eval_operand arg_op after = eval_operand arg_op before) /\
    abi_operand_before cs.cs_next_var src /\ EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operand src before = SOME root_addr /\ eval_operands topic_ops before = SOME topics ==>
    cs.cs_next_var <= cs'.cs_next_var /\
    abi_operand_before cs'.cs_next_var src /\ EVERY (abi_operand_before cs'.cs_next_var) topic_ops /\
    eval_operand src after = SOME root_addr /\ eval_operands topic_ops after = SOME topics /\
    (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op after = eval_operand arg_op before)
Proof
  rpt gen_tac >> strip_tac >> drule compile_log_store_data_next_var >> DISCH_TAC >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op after = eval_operand arg_op before` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`,
       `cs'.cs_next_var - cs.cs_next_var`, `before`, `after`] abi_operand_before_frame) >> simp[]) >>
  `abi_operand_before cs'.cs_next_var src` by (drule_all abi_operand_before_mono >> simp[]) >>
  `EVERY (abi_operand_before cs'.cs_next_var) topic_ops` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> fs[EVERY_MEM]) >>
  drule_all eval_operands_before_frame >> DISCH_TAC >> asm_simp_tac bool_ss []
QED

Theorem log_non_indexed_evaluate_types:
  !flags args fts ftvs tenv.
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) fts ftvs ==>
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
      (log_non_indexed_types flags fts) (select_log_args F flags ftvs)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH fts` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  simp_tac bool_ss [log_non_indexed_types_select] >>
  irule select_log_args_list_rel >> simp[]
QED

Theorem checked_log_data_memory_size:
  !tops in_deploy layouts addr art cenv flags args fts ftvs.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs ==>
    type_memory_size (TupleTV (select_log_args F flags ftvs)) =
      SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags fts))
Proof
  rpt gen_tac >> strip_tac >> drule_all log_non_indexed_evaluate_types >> DISCH_TAC >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `EVERY type_memory_layout (log_non_indexed_types flags fts)` by simp[all_type_memory_layouts] >>
  drule_all type_memory_layout_list >> DISCH_TAC >>
  asm_simp_tac bool_ss [type_memory_size_def, type_memory_size_list_sum]
QED
