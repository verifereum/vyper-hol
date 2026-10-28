(* TOP-LEVEL: exact compiler cuts for recursive dynamic-array repacking.
   The shared length/capacity prefix is followed by the existing generic
   loop scaffold, whose child can itself emit arbitrary additional blocks. *)
Theory typedDynLoopCode
Ancestors
  typedArrayLoopCode dynCopyCode abiBytestringCode abiStaticLoopCode
  context compileEnv emitHelper venomInst list rich_list pair arithmetic

Definition dyn_copy_prefix_state_def:
  dyn_copy_prefix_state cs dst src capacity =
    cs with <| cs_next_var := cs.cs_next_var + 5; cs_next_id := cs.cs_next_id + 7;
      cs_current_insts := cs.cs_current_insts ++
        dyn_copy_prefix_insts cs.cs_next_id (compiler_var_names cs.cs_next_var 5) dst src capacity |>
End

Definition dynarray_copy_start_def:
  dynarray_copy_start cenv dst dst_ty capacity src src_ty cs =
    typed_array_loop_start (dyn_copy_prefix_state cs dst src capacity)
      (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
      (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1))
      (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2))
      (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 4)) (Var (compiler_var_name cs.cs_next_var 3))
      (type_memory_bytes cenv dst_ty) (type_memory_bytes cenv src_ty)
End

Definition dynarray_copy_finish_def:
  dynarray_copy_finish cs after =
    typed_array_loop_finish (compiler_var_name cs.cs_next_var 5)
      (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
      (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) after
End

Theorem dyn_copy_prefix_state_fields[simp]:
  !cs dst src capacity.
    (dyn_copy_prefix_state cs dst src capacity).cs_next_var = cs.cs_next_var + 5 /\
    (dyn_copy_prefix_state cs dst src capacity).cs_next_id = cs.cs_next_id + 7 /\
    (dyn_copy_prefix_state cs dst src capacity).cs_next_label = cs.cs_next_label /\
    (dyn_copy_prefix_state cs dst src capacity).cs_current_bb = cs.cs_current_bb /\
    (dyn_copy_prefix_state cs dst src capacity).cs_blocks = cs.cs_blocks /\
    (dyn_copy_prefix_state cs dst src capacity).cs_current_insts = cs.cs_current_insts ++
      dyn_copy_prefix_insts cs.cs_next_id (compiler_var_names cs.cs_next_var 5) dst src capacity
Proof
  simp[dyn_copy_prefix_state_def]
QED

Theorem compile_copy_dynarray_loop_result:
  !cenv dst dst_ty capacity src src_ty cs.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\ dst_ty = src_ty) ==>
    compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty cs =
      let start = dynarray_copy_start cenv dst dst_ty capacity src src_ty cs in
      let after = SND (compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11))
        dst_ty (Var (compiler_var_name cs.cs_next_var 10)) src_ty start) in
      ((), dynarray_copy_finish cs after)
Proof
  rpt gen_tac >> strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  asm_simp_tac bool_ss [LET_THM] >>
  simp[dynarray_copy_start_def, dynarray_copy_finish_def, dyn_copy_prefix_state_def,
    typed_array_loop_start_def, typed_array_loop_finish_def,
    typed_array_loop_entry_def, typed_array_loop_header_def, typed_array_loop_addresses_def,
    typed_array_loop_counter_def, dyn_copy_prefix_insts_def, compiler_var_names_EL, compiler_var_name_def,
    emit_op_def, emit_inst_def, emit_void_def, fresh_id_def, fresh_var_def, fresh_label_def,
    new_block_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >> simp[pairTheory.UNCURRY, compile_state_component_equality] >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive dynamic-array code theorem: " ^ name)
  end) (DB.thms "typedDynLoopCode")
