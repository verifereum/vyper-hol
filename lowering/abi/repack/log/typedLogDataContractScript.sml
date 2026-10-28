(* TOP-LEVEL: complete Log data packing produces the declared tuple
   layout and retains every saved argument and disjoint memory value. *)
Theory typedLogDataContract
Ancestors
  typedCopyStateFrame
  typedLogArgs typedCopyContract typedSArrayDynInvariant
  valueLoadProps memoryValueDefs valueEncoding vyperTyping vyperValue
  context stmtLowering compileEnv abiStaticLoopCode
  fragExec fragBlockPath venomState venomInst list words arithmetic

Definition log_data_store_contract_def:
  log_data_store_contract ctx func ops ftvs atvs buf field_offset start after <=>
    !ss vs buf_addr.
      fn_has_code start after func /\ cut_continuation_no_phi after func /\
      ss.vs_current_bb = start.cs_current_bb /\ ss.vs_inst_idx = LENGTH start.cs_current_insts /\ ~ss.vs_halted /\
      log_args_rel ops atvs vs ss /\
      log_args_safe ops atvs ss (w2n buf_addr + field_offset) (type_memory_size (TupleTV ftvs)) /\
      eval_operand buf ss = SOME buf_addr /\
      w2n buf_addr + field_offset + type_memory_size (TupleTV ftvs) < dimword(:256) /\
      EVERY (\name. buf <> Var name)
        (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) /\
      log_args_avoid ops (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
      ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
        out.vs_current_bb = after.cs_current_bb /\ out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
        values_have_types ftvs vs /\ memory_tuple_rel ftvs vs (w2n buf_addr + field_offset) out.vs_memory /\
        log_args_rel ops atvs vs out /\
        log_args_safe ops atvs out (w2n buf_addr + field_offset) (type_memory_size (TupleTV ftvs)) /\
        array_copy_frame (TupleTV ftvs) 1 (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
        (!arg_op. EVERY (\name. arg_op <> Var name)
          (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
          eval_operand arg_op out = eval_operand arg_op ss)
End

Theorem log_data_store_contract_nil:
  !ctx func cenv buf field_offset cs ret cs'.
    compile_log_store_data cenv [] [] buf field_offset cs = (ret,cs') ==>
    log_data_store_contract ctx func [] [] [] buf field_offset cs cs'
Proof
  rpt gen_tac >> simp[Once compile_log_store_data_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp_tac bool_ss [log_data_store_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `vs`, `buf_addr`] >> strip_tac >>
  Cases_on `vs` >> fs[log_args_rel_def] >> qexists_tac `ss` >>
  simp[log_args_rel_def, log_args_safe_def, memory_value_rel_def, value_has_type_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete Log data packing contract: " ^ name)
  end) (DB.thms "typedLogDataContract")
