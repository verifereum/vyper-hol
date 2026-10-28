(* TOP-LEVEL: factor the actual dynamic-array encoder into
   its parent-cell setup, generated loop and parent-cell epilogue.
   Helpers describe compiler cuts and the instructions at those cuts. *)
Theory abiDynArrayCode
Ancestors
  abiEncoder abiEncoderStructure abiStaticLoopCode context compileEnv emitHelper exprLoweringProps
  fragExec venomInst list rich_list arithmetic
Libs pairLib

Definition abi_dynarray_entry_insts_def:
  abi_dynarray_entry_insts id var_base dst src =
    [mk_inst id ALLOCA [Lit 32w] [compiler_var_name var_base 0];
     mk_inst (id + 1) MSTORE [Var (compiler_var_name var_base 0); Lit 0w] [];
     mk_inst (id + 2) MLOAD [src] [compiler_var_name var_base 1];
     mk_inst (id + 3) MSTORE [dst; Var (compiler_var_name var_base 1)] []]
End

Definition abi_dynarray_entry_cut_def:
  abi_dynarray_entry_cut dst src cs =
    cs with <| cs_next_id := cs.cs_next_id + 4;
               cs_next_var := cs.cs_next_var + 2;
               cs_current_insts := cs.cs_current_insts ++
                 abi_dynarray_entry_insts cs.cs_next_id cs.cs_next_var dst src |>
End

Definition abi_dynarray_exit_insts_def:
  abi_dynarray_exit_insts id var_base parent_ptr encoded_size =
    [mk_inst id MLOAD [parent_ptr] [compiler_var_name var_base 0];
     mk_inst (id + 1) ADD [Var (compiler_var_name var_base 0); encoded_size]
       [compiler_var_name var_base 1];
     mk_inst (id + 2) MSTORE [parent_ptr; Var (compiler_var_name var_base 1)] [];
     mk_inst (id + 3) MLOAD [parent_ptr] [compiler_var_name var_base 2]]
End

Definition abi_dynarray_exit_cut_def:
  abi_dynarray_exit_cut parent_ptr encoded_size cs =
    cs with <| cs_next_id := cs.cs_next_id + 4;
               cs_next_var := cs.cs_next_var + 3;
               cs_current_insts := cs.cs_current_insts ++
                 abi_dynarray_exit_insts cs.cs_next_id cs.cs_next_var parent_ptr encoded_size |>
End

Theorem compile_abi_dynarray_factor:
  !dst src info abi_sz mem_sz is_dyn cs.
    compile_abi_encode_to_buf dst src (AbiDynArray info abi_sz mem_sz is_dyn) cs =
      let entry = abi_dynarray_entry_cut dst src cs in
      let (encoded_size,loop_cs) =
        (if is_dyn then compile_abi_encode_dyn_loop else compile_abi_encode_dyn_static_loop) dst src info abi_sz mem_sz
        (Var (compiler_var_name cs.cs_next_var 1)) entry in
      (Var (compiler_var_name loop_cs.cs_next_var 2),
       abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_cs)
Proof
  rpt gen_tac >> Cases_on `is_dyn` >>
  simp[Once compile_abi_encode_child_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, LET_THM,
    abi_dynarray_entry_cut_def, abi_dynarray_entry_insts_def, compiler_var_name_def] >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >> simp[] >>
  pairarg_tac >> simp[abi_dynarray_exit_cut_def, abi_dynarray_exit_insts_def,
    compiler_var_name_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  PURE_ASM_REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >>
  simp[compile_state_component_equality]
QED

Theorem abi_dynarray_cuts_extend:
  (!dst src cs. cs_extends cs (abi_dynarray_entry_cut dst src cs)) /\
  (!parent_ptr encoded_size cs. cs_extends cs (abi_dynarray_exit_cut parent_ptr encoded_size cs))
Proof
  rpt conj_tac >> rpt gen_tac >> irule cs_extends_same_block >>
  simp[abi_dynarray_entry_cut_def, abi_dynarray_exit_cut_def, IS_PREFIX_APPEND]
QED

Theorem compile_abi_dyn_static_loop_extends:
  !dst src info abi_sz mem_sz len_op cs op cs'.
    compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len_op cs = (op,cs') ==>
    cs_extends cs cs'
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_abi_encode_dyn_static_loop_result] >>
  simp[cs_extends_def] >>
  qexists_tac
    `[<|bb_label := fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1);
        bb_instructions := abi_static_loop_body cs.cs_next_id cs.cs_next_var
          cs.cs_next_label dst src info abi_sz mem_sz|>;
      <|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
        bb_instructions := abi_static_loop_header cs.cs_next_id cs.cs_next_var
          cs.cs_next_label len_op|>;
      <|bb_label := cs.cs_current_bb;
        bb_instructions := cs.cs_current_insts ++
          abi_static_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label|>]` >>
  simp[IS_PREFIX_APPEND]
QED

Theorem compile_abi_dynarray_contains_parts:
  !is_dyn dst src info abi_sz mem_sz cs encoded_size loop_cs func.
    (if is_dyn then compile_abi_encode_dyn_loop else compile_abi_encode_dyn_static_loop) dst src info abi_sz mem_sz
      (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_cut dst src cs) =
        (encoded_size,loop_cs) /\
    fn_has_code cs
      (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_cs) func ==>
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    fn_has_code (abi_dynarray_entry_cut dst src cs) loop_cs func /\
    fn_has_code loop_cs
      (abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_cs) func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends (abi_dynarray_entry_cut dst src cs) loop_cs` by
    (Cases_on `is_dyn` >> fs[] >>
     FIRST [drule_all (REWRITE_RULE [cs_appends_def] (cj 4 cs_appends_compile_abi_encode)) >> simp[],
       drule_all compile_abi_dyn_static_loop_extends >> simp[]]) >>
  `cs_extends cs loop_cs` by
    (irule cs_extends_trans >> qexists_tac `abi_dynarray_entry_cut dst src cs` >>
     simp[abi_dynarray_cuts_extend]) >>
  mp_tac (Q.SPECL [`cs`, `loop_cs`,
    `abi_dynarray_exit_cut (Var (compiler_var_name cs.cs_next_var 0)) encoded_size loop_cs`, `func`]
    fn_has_code_split) >> impl_tac >- simp[abi_dynarray_cuts_extend] >> strip_tac >>
  mp_tac (Q.SPECL [`cs`, `abi_dynarray_entry_cut dst src cs`, `loop_cs`, `func`]
    fn_has_code_split) >> simp[abi_dynarray_cuts_extend]
QED

Theorem abi_dynarray_insts_straight:
  (!id var_base dst src.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (abi_dynarray_entry_insts id var_base dst src)) /\
  (!id var_base parent_ptr encoded_size.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (abi_dynarray_exit_insts id var_base parent_ptr encoded_size))
Proof
  simp[abi_dynarray_entry_insts_def, abi_dynarray_exit_insts_def, mk_inst_def, is_terminator_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI dynamic-array code theorem: " ^ name)
  end) (DB.thms "abiDynArrayCode")
