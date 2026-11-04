(* Exact compiler states around a generated dynamic-array loop body. *)
Theory abiDecoderLoopEmit
Ancestors
  abiDecoderLoopSetup abiDecoderExecution abiEncoder emitHelper compileEnv
  venomInst list arithmetic

Definition abi_decode_loop_prefix_def:
  abi_decode_loop_prefix ip src opc =
    do hdr <- fresh_label "dec_dyn_hdr";
       body <- fresh_label "dec_dyn_body";
       exit_lbl <- fresh_label "dec_dyn_exit";
       emit_inst JMP [Label hdr] [];
       new_block hdr;
       idx <- emit_op MLOAD [ip];
       count_op <- emit_op opc [src];
       cmp <- emit_op LT [idx; count_op];
       done_op <- emit_op ISZERO [cmp];
       emit_inst JNZ [done_op; Label exit_lbl; Label body] [];
       new_block body;
       return (hdr,body,exit_lbl)
    od
End

Definition abi_decode_loop_prefix_state_def:
  abi_decode_loop_prefix_state ip src opc st =
    let hdr = fresh_label_output "dec_dyn_hdr" st.cs_next_label;
        body = fresh_label_output "dec_dyn_body" (st.cs_next_label + 1);
        exit_lbl = fresh_label_output "dec_dyn_exit" (st.cs_next_label + 2) in
    st with <|cs_next_var := st.cs_next_var + 4;
      cs_next_id := st.cs_next_id + 6; cs_next_label := st.cs_next_label + 3;
      cs_current_bb := body; cs_current_insts := [];
      cs_blocks :=
        <|bb_label := hdr; bb_instructions :=
          abi_decode_header_insts (st.cs_next_id + 1) ip src opc
            (STRING #"%" (toString st.cs_next_var))
            (STRING #"%" (toString (st.cs_next_var + 1)))
            (STRING #"%" (toString (st.cs_next_var + 2)))
            (STRING #"%" (toString (st.cs_next_var + 3))) body exit_lbl|> ::
        <|bb_label := st.cs_current_bb; bb_instructions :=
          st.cs_current_insts ++ [mk_inst st.cs_next_id JMP [Label hdr] []]|> ::
        st.cs_blocks|>
End

Theorem abi_decode_loop_prefix_shape:
  abi_decode_loop_prefix ip src opc st =
    ((fresh_label_output "dec_dyn_hdr" st.cs_next_label,
      fresh_label_output "dec_dyn_body" (st.cs_next_label + 1),
      fresh_label_output "dec_dyn_exit" (st.cs_next_label + 2)),
      abi_decode_loop_prefix_state ip src opc st)
Proof
  simp[abi_decode_loop_prefix_def, abi_decode_loop_prefix_state_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, new_block_def, emit_op_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, abi_decode_header_insts_def]
QED

Definition abi_decode_loop_suffix_def:
  abi_decode_loop_suffix ip idx hdr exit_lbl =
    do new_idx <- emit_op ADD [idx; Lit 1w];
       emit_void MSTORE [ip; new_idx];
       emit_inst JMP [Label hdr] [];
       new_block exit_lbl;
       return ()
    od
End

Definition abi_decode_loop_suffix_state_def:
  abi_decode_loop_suffix_state ip iv hdr exit_lbl st =
    st with <|cs_next_var := st.cs_next_var + 1;
      cs_next_id := st.cs_next_id + 3;
      cs_current_bb := exit_lbl; cs_current_insts := [];
      cs_blocks := <|bb_label := st.cs_current_bb;
        bb_instructions := st.cs_current_insts ++
          abi_decode_backedge_insts st.cs_next_id iv
            (STRING #"%" (toString st.cs_next_var)) ip hdr|> :: st.cs_blocks|>
End

Theorem abi_decode_loop_suffix_shape:
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl st =
    ((),abi_decode_loop_suffix_state ip iv hdr exit_lbl st)
Proof
  simp[abi_decode_loop_suffix_def, abi_decode_loop_suffix_state_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       new_block_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, abi_decode_backedge_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem abi_decode_dyn_loop_phases:
  compile_abi_decode_dyn_loop dst src opc hi di abi_sz mem_sz ip cnt =
    do labels <- abi_decode_loop_prefix ip src opc;
       child_ops <- abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz;
       compile_abi_decode_to_buf (SND (SND child_ops)) (FST (SND child_ops)) opc hi di;
       abi_decode_loop_suffix ip (FST child_ops) (FST labels) (SND (SND labels))
    od
Proof
  simp[abi_decode_dyn_loop_setup, abi_decode_loop_prefix_def, abi_decode_loop_suffix_def,
       FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_dyn_loop_trace:
  compile_abi_decode_dyn_loop dst src opc hi di abi_sz mem_sz ip cnt start = ((),end_st) ==>
  ?labels st0 ops middle st1.
    abi_decode_loop_prefix ip src opc start = (labels,st0) /\
    abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st0 = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),end_st)
Proof
  strip_tac >> Cases_on `abi_decode_loop_prefix ip src opc start` >>
  rename1 `abi_decode_loop_prefix ip src opc start = (labels,st0)` >>
  Cases_on `abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st0` >>
  rename1 `abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st0 = (ops,middle)` >>
  Cases_on `compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle` >>
  rename1 `compile_abi_decode_to_buf _ _ opc hi di middle = (u,st1)` >>
  Cases_on `u` >> qexistsl_tac [`labels`, `st0`, `ops`, `middle`, `st1`] >>
  gvs[abi_decode_dyn_loop_phases, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED
