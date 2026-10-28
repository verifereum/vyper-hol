(* TOP-LEVEL: the real runtime-array child prefix has fresh instruction
   history, reserves every child input operand, and extends its loop's
   compiler state. The same compiled prefix is reused by every iteration. *)
Theory abiNativeDynamicArrayPrefixCode
Ancestors
  abiDynamicLoopCode abiDynamicLoopStructure abiStaticLoopCode abiFieldOperands
  compileIdFlow compileEnv fragExec venomInst list rich_list words arithmetic

Theorem abi_native_dynamic_array_prefix_history:
  !dst src width stride len_op cs.
    compiler_id_history cs ==>
    compiler_id_history (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
Proof
  rpt gen_tac >> simp[compiler_id_history_def, abi_dynamic_loop_prefix_cut_def,
    abi_dynamic_loop_entry_def, abi_dynamic_loop_header_def, abi_dynamic_loop_body_prefix_def,
    mk_inst_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem abi_native_dynamic_array_child_operands:
  !dst src width stride len_op cs.
    abi_operand_before (abi_dynamic_loop_prefix_cut dst src width stride len_op cs).cs_next_var
      (Var (compiler_var_name cs.cs_next_var 9)) /\
    abi_operand_before (abi_dynamic_loop_prefix_cut dst src width stride len_op cs).cs_next_var
      (Var (compiler_var_name cs.cs_next_var 14)) /\
    cs.cs_next_var <= (abi_dynamic_loop_prefix_cut dst src width stride len_op cs).cs_next_var
Proof
  rpt gen_tac >> simp[abi_dynamic_loop_prefix_cut_def, abi_operand_before_def, compiler_var_name_def] >>
  rpt strip_tac >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual runtime array child compiler prefix: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayPrefixCode")
