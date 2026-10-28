(* TOP-LEVEL: expose the actual dynamic ABI child prefix and suffix around
   an arbitrary recursively compiled child. No child instruction is unfolded. *)
Theory abiChildCode
Ancestors
  abiEncoder abiBytestringCode abiStaticLoopCode compileEnv emitHelper venomInst
  list pair arithmetic
Libs monadsyntax pairLib

Definition compile_abi_child_prefix_def:
  compile_abi_child_prefix dst dyn_ptr head_offset =
    do head_ptr <- emit_op ADD [dst; Lit (n2w head_offset)];
       tail_offset <- emit_op MLOAD [dyn_ptr];
       tail_ptr <- emit_op ADD [dst; tail_offset];
       return (head_ptr,tail_offset,tail_ptr)
    od
End

Definition compile_abi_child_suffix_def:
  compile_abi_child_suffix head_ptr tail_offset dyn_ptr child_len =
    do emit_void MSTORE [head_ptr; tail_offset];
       new_offset <- emit_op ADD [tail_offset; child_len];
       emit_void MSTORE [dyn_ptr; new_offset];
       return child_len
    od
End

Definition abi_child_prefix_insts_def:
  abi_child_prefix_insts dst dyn_ptr head_offset id var_base =
    [mk_inst id ADD [dst; Lit (n2w head_offset)] [compiler_var_name var_base 0];
     mk_inst (id + 1) MLOAD [dyn_ptr] [compiler_var_name var_base 1];
     mk_inst (id + 2) ADD [dst; Var (compiler_var_name var_base 1)] [compiler_var_name var_base 2]]
End

Definition abi_child_prefix_cut_def:
  abi_child_prefix_cut dst dyn_ptr head_offset cs =
    cs with <| cs_current_insts := cs.cs_current_insts ++
      abi_child_prefix_insts dst dyn_ptr head_offset cs.cs_next_id cs.cs_next_var;
      cs_next_id := cs.cs_next_id + 3; cs_next_var := cs.cs_next_var + 3 |>
End

Definition abi_child_suffix_insts_def:
  abi_child_suffix_insts head_ptr tail_offset dyn_ptr child_len id var_base =
    [mk_inst id MSTORE [head_ptr; tail_offset] [];
     mk_inst (id + 1) ADD [tail_offset; child_len] [compiler_var_name var_base 0];
     mk_inst (id + 2) MSTORE [dyn_ptr; Var (compiler_var_name var_base 0)] []]
End

Definition abi_child_suffix_cut_def:
  abi_child_suffix_cut head_ptr tail_offset dyn_ptr child_len cs =
    cs with <| cs_current_insts := cs.cs_current_insts ++
      abi_child_suffix_insts head_ptr tail_offset dyn_ptr child_len cs.cs_next_id cs.cs_next_var;
      cs_next_id := cs.cs_next_id + 3; cs_next_var := cs.cs_next_var + 1 |>
End

Theorem compile_abi_child_prefix_result:
  !dst dyn_ptr head_offset cs.
    compile_abi_child_prefix dst dyn_ptr head_offset cs =
      ((Var (compiler_var_name cs.cs_next_var 0), Var (compiler_var_name cs.cs_next_var 1),
        Var (compiler_var_name cs.cs_next_var 2)), abi_child_prefix_cut dst dyn_ptr head_offset cs)
Proof
  simp[compile_abi_child_prefix_def, abi_child_prefix_cut_def, abi_child_prefix_insts_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, compiler_var_name_def] >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem compile_abi_child_suffix_result:
  !head_ptr tail_offset dyn_ptr child_len cs.
    compile_abi_child_suffix head_ptr tail_offset dyn_ptr child_len cs =
      (child_len, abi_child_suffix_cut head_ptr tail_offset dyn_ptr child_len cs)
Proof
  simp[compile_abi_child_suffix_def, abi_child_suffix_cut_def, abi_child_suffix_insts_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, compiler_var_name_def] >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem compile_abi_child_dynamic_split:
  !dst src info head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_child dst src info T head_offset dyn_ptr cs = (ret,cs') <=>
    ?head_ptr tail_offset tail_ptr prefix child_len mid.
      compile_abi_child_prefix dst dyn_ptr head_offset cs = ((head_ptr,tail_offset,tail_ptr),prefix) /\
      compile_abi_encode_to_buf tail_ptr src info prefix = (child_len,mid) /\
      compile_abi_child_suffix head_ptr tail_offset dyn_ptr child_len mid = (ret,cs')
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_encode_child_def])) >>
  simp_tac bool_ss [compile_abi_child_prefix_def, compile_abi_child_suffix_def,
    comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [dst; Lit (n2w head_offset)] cs` >>
  rename1 `emit_op ADD [dst; Lit (n2w head_offset)] cs = (head_ptr,after_head)` >>
  Cases_on `emit_op MLOAD [dyn_ptr] after_head` >>
  rename1 `emit_op MLOAD [dyn_ptr] after_head = (tail_offset,after_offset)` >>
  Cases_on `emit_op ADD [dst; tail_offset] after_offset` >>
  rename1 `emit_op ADD [dst; tail_offset] after_offset = (tail_ptr,prefix)` >>
  Cases_on `compile_abi_encode_to_buf tail_ptr src info prefix` >>
  simp[comp_return_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI child code: " ^ name)
  end) (DB.thms "abiChildCode")
