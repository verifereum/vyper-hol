(* TOP-LEVEL: exact instructions and compile-state effect of the actual ABI loop
   for dynamic arrays with static elements. These lists describe compiler
   output; the compiler itself continues to use its monadic implementation.
   Helpers: static element instruction lists and generated SSA names. *)
Theory abiStaticLoopCode
Ancestors
  abiEncoder context compileEnv emitHelper exprLoweringProps
  venomInst list rich_list arithmetic ASCIInumbers

Definition compiler_var_name_def:
  compiler_var_name (base:num) (index:num) = STRING #"%" (toString (base + index))
End

Theorem compiler_var_name_inj[simp]:
  !base i j. compiler_var_name base i = compiler_var_name base j <=> i = j
Proof
  simp[compiler_var_name_def]
QED

Theorem compiler_var_name_add:
  !base offset index.
    compiler_var_name (base + offset) index = compiler_var_name base (offset + index)
Proof
  PURE_REWRITE_TAC[compiler_var_name_def, ADD_ASSOC] >> simp[]
QED

Definition static_info_var_count_def:
  static_info_var_count AbiPrimWord = 1 /\
  static_info_var_count _ = 0
End

Definition static_info_id_count_def:
  static_info_id_count AbiPrimWord = 2 /\
  static_info_id_count (AbiCopy _) = 1 /\
  static_info_id_count _ = 0
End

Definition static_info_insts_def:
  static_info_insts id base dst src AbiPrimWord =
    [mk_inst id MLOAD [src] [compiler_var_name base 0];
     mk_inst (id + 1) MSTORE [dst; Var (compiler_var_name base 0)] []] /\
  static_info_insts id base dst src (AbiCopy mem_size) =
    [mk_inst id MCOPY [dst; src; Lit (n2w mem_size)] []] /\
  static_info_insts id base dst src _ = []
End

Definition static_info_output_def:
  static_info_output AbiPrimWord = Lit 32w /\
  static_info_output (AbiCopy mem_size) = Lit (n2w mem_size) /\
  static_info_output _ = Lit 0w
End

Theorem static_info_insts_length[simp]:
  !id base dst src info.
    LENGTH (static_info_insts id base dst src info) = static_info_id_count info
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[static_info_insts_def, static_info_id_count_def]
QED

Theorem static_info_insts_straight:
  !id base dst src info.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (static_info_insts id base dst src info)
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[static_info_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem compile_abi_encode_static_info_result:
  !dst src info cs.
    compile_abi_encode_static_info dst src info cs =
      (static_info_output info,
       cs with <|
         cs_next_var := cs.cs_next_var + static_info_var_count info;
         cs_next_id := cs.cs_next_id + static_info_id_count info;
         cs_current_insts := cs.cs_current_insts ++
           static_info_insts cs.cs_next_id cs.cs_next_var dst src info |> )
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, compile_abi_encode_static_def,
    static_info_output_def, static_info_insts_def, static_info_id_count_def,
    static_info_var_count_def, compiler_var_name_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[compile_state_component_equality]
QED

Definition abi_static_loop_entry_def:
  abi_static_loop_entry id base labels =
    [mk_inst id ALLOCA [Lit 32w] [compiler_var_name base 0];
     mk_inst (id + 1) MSTORE [Var (compiler_var_name base 0); Lit 0w] [];
     mk_inst (id + 2) JMP [Label (fresh_label_output "enc_dyn_hdr" labels)] []]
End

Definition abi_static_loop_header_def:
  abi_static_loop_header id base labels len_op =
    [mk_inst (id + 3) MLOAD [Var (compiler_var_name base 0)] [compiler_var_name base 1];
     mk_inst (id + 4) LT [Var (compiler_var_name base 1); len_op] [compiler_var_name base 2];
     mk_inst (id + 5) ISZERO [Var (compiler_var_name base 2)] [compiler_var_name base 3];
     mk_inst (id + 6) JNZ
       [Var (compiler_var_name base 3);
        Label (fresh_label_output "enc_dyn_exit" (labels + 2));
        Label (fresh_label_output "enc_dyn_body" (labels + 1))] []]
End

Definition abi_static_loop_body_prefix_def:
  abi_static_loop_body_prefix id base dst src abi_sz mem_sz =
    [mk_inst (id + 7) MLOAD [Var (compiler_var_name base 0)] [compiler_var_name base 4];
     mk_inst (id + 8) ADD [src; Lit 32w] [compiler_var_name base 5];
     mk_inst (id + 9) MUL [Var (compiler_var_name base 4); Lit (n2w mem_sz)]
       [compiler_var_name base 6];
     mk_inst (id + 10) ADD [Var (compiler_var_name base 5); Var (compiler_var_name base 6)]
       [compiler_var_name base 7];
     mk_inst (id + 11) ADD [dst; Lit 32w] [compiler_var_name base 8];
     mk_inst (id + 12) MUL [Var (compiler_var_name base 4); Lit (n2w abi_sz)]
       [compiler_var_name base 9];
     mk_inst (id + 13) ADD [Var (compiler_var_name base 8); Var (compiler_var_name base 9)]
       [compiler_var_name base 10]]
End

Definition abi_static_loop_body_def:
  abi_static_loop_body id base labels dst src info abi_sz mem_sz =
    abi_static_loop_body_prefix id base dst src abi_sz mem_sz ++
    static_info_insts (id + 14) (base + 11)
      (Var (compiler_var_name base 10)) (Var (compiler_var_name base 7)) info ++
    [mk_inst (id + 14 + static_info_id_count info) ADD
       [Var (compiler_var_name base 4); Lit 1w]
       [compiler_var_name base (11 + static_info_var_count info)];
     mk_inst (id + 15 + static_info_id_count info) MSTORE
       [Var (compiler_var_name base 0);
        Var (compiler_var_name base (11 + static_info_var_count info))] [];
     mk_inst (id + 16 + static_info_id_count info) JMP
       [Label (fresh_label_output "enc_dyn_hdr" labels)] []]
End

Definition abi_static_loop_exit_def:
  abi_static_loop_exit id base src info abi_sz =
    [mk_inst (id + 17 + static_info_id_count info) MLOAD [src]
       [compiler_var_name base (12 + static_info_var_count info)];
     mk_inst (id + 18 + static_info_id_count info) MUL
       [Var (compiler_var_name base (12 + static_info_var_count info)); Lit (n2w abi_sz)]
       [compiler_var_name base (13 + static_info_var_count info)];
     mk_inst (id + 19 + static_info_id_count info) ADD
       [Lit 32w; Var (compiler_var_name base (13 + static_info_var_count info))]
       [compiler_var_name base (14 + static_info_var_count info)]]
End

Theorem compile_abi_encode_dyn_static_loop_result:
  !dst src info abi_sz mem_sz len_op cs.
    compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len_op cs =
      (Var (compiler_var_name cs.cs_next_var (14 + static_info_var_count info)),
       cs with <|
         cs_next_id := cs.cs_next_id + 20 + static_info_id_count info;
         cs_next_var := cs.cs_next_var + 15 + static_info_var_count info;
         cs_next_label := cs.cs_next_label + 3;
         cs_current_bb := fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2);
         cs_current_insts := abi_static_loop_exit cs.cs_next_id cs.cs_next_var src info abi_sz;
         cs_blocks :=
           <| bb_label := fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1);
              bb_instructions := abi_static_loop_body cs.cs_next_id cs.cs_next_var
                cs.cs_next_label dst src info abi_sz mem_sz |> ::
           <| bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
              bb_instructions := abi_static_loop_header cs.cs_next_id cs.cs_next_var
                cs.cs_next_label len_op |> ::
           <| bb_label := cs.cs_current_bb;
              bb_instructions := cs.cs_current_insts ++
                abi_static_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label |> ::
           cs.cs_blocks |> )
Proof
  rpt gen_tac >>
  simp[compile_abi_encode_dyn_static_loop_def, compile_alloc_buffer_def,
    compile_abi_encode_static_info_result, LET_THM,
    emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, fresh_var_def,
    fresh_label_def, new_block_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    abi_static_loop_entry_def, abi_static_loop_header_def,
    abi_static_loop_body_def, abi_static_loop_body_prefix_def, abi_static_loop_exit_def,
    compiler_var_name_def] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[compile_state_component_equality]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop code theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopCode")
