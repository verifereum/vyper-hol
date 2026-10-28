(* TOP-LEVEL: exact open code cuts around a recursively compiled array-copy
   element. The child may finish in a different block and allocate further
   labels; the parent resumes there before jumping back to its own header.
   Helpers describe the shared entry, header, address and counter code. *)
Theory typedArrayLoopCode
Ancestors
  abiStaticLoopCode context compileEnv emitHelper venomInst list rich_list pair arithmetic

Definition typed_array_loop_entry_def:
  typed_array_loop_entry id var_base cond_label =
    [mk_inst id ASSIGN [Lit 0w] [compiler_var_name var_base 0];
     mk_inst (id + 1) JMP [Label cond_label] []]
End

Definition typed_array_loop_header_def:
  typed_array_loop_header id var_base body_label exit_label len_op =
    [mk_inst (id + 2) LT [Var (compiler_var_name var_base 0); len_op]
       [compiler_var_name var_base 1];
     mk_inst (id + 3) ISZERO [Var (compiler_var_name var_base 1)]
       [compiler_var_name var_base 2];
     mk_inst (id + 4) JNZ
       [Var (compiler_var_name var_base 2); Label exit_label; Label body_label] []]
End

Definition typed_array_loop_addresses_def:
  typed_array_loop_addresses id var_base dst src dst_size src_size =
    [mk_inst (id + 5) MUL [Var (compiler_var_name var_base 0); Lit (n2w src_size)]
       [compiler_var_name var_base 3];
     mk_inst (id + 6) MUL [Var (compiler_var_name var_base 0); Lit (n2w dst_size)]
       [compiler_var_name var_base 4];
     mk_inst (id + 7) ADD [src; Var (compiler_var_name var_base 3)]
       [compiler_var_name var_base 5];
     mk_inst (id + 8) ADD [dst; Var (compiler_var_name var_base 4)]
       [compiler_var_name var_base 6]]
End

Definition typed_array_loop_counter_def:
  typed_array_loop_counter id var_base counter cond_label =
    [mk_inst id ADD [Var counter; Lit 1w] [compiler_var_name var_base 0];
     mk_inst (id + 1) ASSIGN [Var (compiler_var_name var_base 0)] [counter];
     mk_inst (id + 2) JMP [Label cond_label] []]
End

Definition typed_array_loop_start_def:
  typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size =
    cs with <|
      cs_next_id := cs.cs_next_id + 9;
      cs_next_var := cs.cs_next_var + 7;
      cs_next_label := cs.cs_next_label + 3;
      cs_current_bb := body_label;
      cs_current_insts := typed_array_loop_addresses cs.cs_next_id cs.cs_next_var dst src dst_size src_size;
      cs_blocks :=
        <| bb_label := cond_label;
           bb_instructions := typed_array_loop_header cs.cs_next_id cs.cs_next_var
             body_label exit_label len_op |> ::
        <| bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++
             typed_array_loop_entry cs.cs_next_id cs.cs_next_var cond_label |> :: cs.cs_blocks |>
End

Definition typed_array_loop_finish_def:
  typed_array_loop_finish counter cond_label exit_label after =
    after with <|
      cs_next_id := after.cs_next_id + 3;
      cs_next_var := after.cs_next_var + 1;
      cs_current_bb := exit_label;
      cs_current_insts := [];
      cs_blocks :=
        <| bb_label := after.cs_current_bb;
           bb_instructions := after.cs_current_insts ++
             typed_array_loop_counter after.cs_next_id after.cs_next_var counter cond_label |>
        :: after.cs_blocks |>
End

Theorem compile_copy_sarray_loop_result:
  !cenv dst dst_ty src src_ty copy_count cs.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) ==>
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs =
      let cond_label = fresh_label_output "typed_sa_cond" cs.cs_next_label in
      let body_label = fresh_label_output "typed_sa_body" (cs.cs_next_label + 1) in
      let exit_label = fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2) in
      let start = typed_array_loop_start cs cond_label body_label exit_label (Lit (n2w copy_count))
        dst src (type_memory_bytes cenv dst_ty) (type_memory_bytes cenv src_ty) in
      let after = SND (compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6))
        dst_ty (Var (compiler_var_name cs.cs_next_var 5)) src_ty start) in
      ((), typed_array_loop_finish (compiler_var_name cs.cs_next_var 0) cond_label exit_label after)
Proof
  rpt gen_tac >> strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  asm_simp_tac bool_ss [LET_THM] >>
  simp[typed_array_loop_start_def, typed_array_loop_finish_def,
    typed_array_loop_entry_def, typed_array_loop_header_def, typed_array_loop_addresses_def,
    typed_array_loop_counter_def, compiler_var_name_def,
    emit_op_def, emit_inst_def, emit_void_def, fresh_id_def, fresh_var_def, fresh_label_def,
    new_block_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >> simp[pairTheory.UNCURRY, compile_state_component_equality] >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive array-copy code theorem: " ^ name)
  end) (DB.thms "typedArrayLoopCode")
