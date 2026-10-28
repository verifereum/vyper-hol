(* TOP-LEVEL: exact compiler cuts for the dynamic-child array loop. Children
   may add blocks; the latch therefore closes the child's final block. *)
Theory abiDynamicLoopCode
Ancestors
  abiStaticLoopCode compileEnv venomInst list arithmetic

Definition abi_dynamic_loop_entry_def:
  abi_dynamic_loop_entry id var_base labels abi_sz len_op =
    [mk_inst id ALLOCA [Lit 32w] [compiler_var_name var_base 0];
     mk_inst (id + 1) MSTORE [Var (compiler_var_name var_base 0); Lit 0w] [];
     mk_inst (id + 2) ALLOCA [Lit 32w] [compiler_var_name var_base 1];
     mk_inst (id + 3) MUL [len_op; Lit (n2w abi_sz)] [compiler_var_name var_base 2];
     mk_inst (id + 4) MSTORE [Var (compiler_var_name var_base 1); Var (compiler_var_name var_base 2)] [];
     mk_inst (id + 5) JMP [Label (fresh_label_output "enc_dyn_hdr" labels)] []]
End

Definition abi_dynamic_loop_header_def:
  abi_dynamic_loop_header id var_base labels len_op =
    [mk_inst (id + 6) MLOAD [Var (compiler_var_name var_base 0)] [compiler_var_name var_base 3];
     mk_inst (id + 7) LT [Var (compiler_var_name var_base 3); len_op] [compiler_var_name var_base 4];
     mk_inst (id + 8) ISZERO [Var (compiler_var_name var_base 4)] [compiler_var_name var_base 5];
     mk_inst (id + 9) JNZ [Var (compiler_var_name var_base 5);
       Label (fresh_label_output "enc_dyn_exit" (labels + 2));
       Label (fresh_label_output "enc_dyn_body" (labels + 1))] []]
End

Definition abi_dynamic_loop_body_prefix_def:
  abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz =
    [mk_inst (id + 10) MLOAD [Var (compiler_var_name var_base 0)] [compiler_var_name var_base 6];
     mk_inst (id + 11) ADD [src; Lit 32w] [compiler_var_name var_base 7];
     mk_inst (id + 12) MUL [Var (compiler_var_name var_base 6); Lit (n2w mem_sz)] [compiler_var_name var_base 8];
     mk_inst (id + 13) ADD [Var (compiler_var_name var_base 7); Var (compiler_var_name var_base 8)]
       [compiler_var_name var_base 9];
     mk_inst (id + 14) ADD [dst; Lit 32w] [compiler_var_name var_base 10];
     mk_inst (id + 15) MUL [Var (compiler_var_name var_base 6); Lit (n2w abi_sz)] [compiler_var_name var_base 11];
     mk_inst (id + 16) ADD [Var (compiler_var_name var_base 10); Var (compiler_var_name var_base 11)]
       [compiler_var_name var_base 12];
     mk_inst (id + 17) MLOAD [Var (compiler_var_name var_base 1)] [compiler_var_name var_base 13];
     mk_inst (id + 18) ADD [Var (compiler_var_name var_base 10); Var (compiler_var_name var_base 13)]
       [compiler_var_name var_base 14]]
End

Definition abi_dynamic_loop_prefix_cut_def:
  abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs =
    cs with <| cs_next_id := cs.cs_next_id + 19; cs_next_var := cs.cs_next_var + 15;
      cs_next_label := cs.cs_next_label + 3;
      cs_current_bb := fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1);
      cs_current_insts := abi_dynamic_loop_body_prefix cs.cs_next_id cs.cs_next_var dst src abi_sz mem_sz;
      cs_blocks :=
        <|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
          bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|> ::
        <|bb_label := cs.cs_current_bb;
          bb_instructions := cs.cs_current_insts ++
            abi_dynamic_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label abi_sz len_op|> :: cs.cs_blocks |>
End

Definition abi_dynamic_loop_latch_def:
  abi_dynamic_loop_latch id var_base i_ptr i_op header_label =
    [mk_inst id ADD [i_op; Lit 1w] [compiler_var_name var_base 0];
     mk_inst (id + 1) MSTORE [i_ptr; Var (compiler_var_name var_base 0)] [];
     mk_inst (id + 2) JMP [Label header_label] []]
End

Definition abi_dynamic_loop_latch_cut_def:
  abi_dynamic_loop_latch_cut i_ptr i_op header_label cs =
    cs with <| cs_next_id := cs.cs_next_id + 3; cs_next_var := cs.cs_next_var + 1;
      cs_current_insts := cs.cs_current_insts ++
        abi_dynamic_loop_latch cs.cs_next_id cs.cs_next_var i_ptr i_op header_label |>
End

Definition abi_dynamic_loop_exit_def:
  abi_dynamic_loop_exit id var_base src dyn_ptr =
    [mk_inst id MLOAD [src] [compiler_var_name var_base 0];
     mk_inst (id + 1) MLOAD [dyn_ptr] [compiler_var_name var_base 1];
     mk_inst (id + 2) ADD [Lit 32w; Var (compiler_var_name var_base 1)] [compiler_var_name var_base 2]]
End

Definition abi_dynamic_loop_exit_cut_def:
  abi_dynamic_loop_exit_cut src dyn_ptr exit_label cs =
    cs with <| cs_next_id := cs.cs_next_id + 3; cs_next_var := cs.cs_next_var + 3;
      cs_current_bb := exit_label;
      cs_current_insts := abi_dynamic_loop_exit cs.cs_next_id cs.cs_next_var src dyn_ptr;
      cs_blocks := <|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts|> :: cs.cs_blocks |>
End

Theorem abi_dynamic_loop_lengths[simp]:
  (!id var_base labels abi_sz len_op. LENGTH (abi_dynamic_loop_entry id var_base labels abi_sz len_op) = 6) /\
  (!id var_base labels len_op. LENGTH (abi_dynamic_loop_header id var_base labels len_op) = 4) /\
  (!id var_base dst src abi_sz mem_sz. LENGTH (abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz) = 9) /\
  (!id var_base i_ptr i_op header_label. LENGTH (abi_dynamic_loop_latch id var_base i_ptr i_op header_label) = 3) /\
  (!id var_base src dyn_ptr. LENGTH (abi_dynamic_loop_exit id var_base src dyn_ptr) = 3)
Proof
  simp[abi_dynamic_loop_entry_def, abi_dynamic_loop_header_def, abi_dynamic_loop_body_prefix_def,
    abi_dynamic_loop_latch_def, abi_dynamic_loop_exit_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-child ABI array-loop code: " ^ name)
  end) (DB.thms "abiDynamicLoopCode")
