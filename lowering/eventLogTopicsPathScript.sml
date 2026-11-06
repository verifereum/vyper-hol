(* TOP-LEVEL: saved, checked Log arguments execute the actual topic producer.
   API: compile_saved_log_topics_path. No state after hashing is assumed. *)
Theory eventLogTopicsPath
Ancestors
  vyperEventArgCompat
  eventLogTopicInputs eventTopicsPath typedLogArgs typedLogArgsMemory typedCopyStateFrame abiFieldOperands
  eventTopicValueProps stmtLowering compileEnv fragExec fragBlockPath
  venomState vyperTypeContract list pair words

Theorem compile_saved_log_topics_path:
  !ctx func tenv flags args values field_types atvs cs ops cs' ss dst byte_count.
    LENGTH flags = LENGTH args /\
    LIST_REL event_arg_compatible field_types (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags field_types /\
    LIST_REL (\arg tv. evaluate_type tenv (SND arg) = SOME tv) args atvs /\
    log_args_rel args atvs values ss /\ log_args_safe args atvs ss dst byte_count /\
    compile_log_topic_ops (FST (split_log_ops args flags)) cs = (ops,cs') /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out topics. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operands ops out = SOME topics /\ encode_indexed_event_topics flags field_types values = SOME topics /\
      EVERY (abi_operand_before cs'.cs_next_var) ops /\ cs.cs_next_var <= cs'.cs_next_var /\
      copy_state_frame ss out /\ out.vs_memory = ss.vs_memory /\
      log_args_rel args atvs values out /\ log_args_safe args atvs out dst byte_count /\
      EVERY (\arg. abi_operand_before cs'.cs_next_var (FST arg)) args /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all compatible_log_args_topic_values >> DISCH_TAC >>
  drule_all_then (qspec_then `ctx` (qx_choose_then `out` (qx_choose_then `topics` strip_assume_tac)))
    compile_split_log_topics_path >>
  `EVERY (\arg. eval_operand (FST arg) out = eval_operand (FST arg) ss) args` by
    (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. abi_operand_before _ _ ==> _` irule >> fs[EVERY_MEM]) >>
  drule_all log_args_rel_memory_frame >> DISCH_TAC >> drule_all log_args_safe_operand_frame >> DISCH_TAC >>
  `EVERY (\arg. abi_operand_before cs'.cs_next_var (FST arg)) args` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> fs[EVERY_MEM]) >>
  qexistsl_tac [`out`, `topics`] >> asm_simp_tac bool_ss []
QED
