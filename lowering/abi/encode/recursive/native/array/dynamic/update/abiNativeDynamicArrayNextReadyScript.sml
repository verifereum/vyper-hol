(* TOP-LEVEL: actual prefix/child/update execution preserves the loop's
   operands and both saved pointers. The latch restores the full ready
   assertion at the next index in the generated header. *)
Theory abiNativeDynamicArrayNextReady
Ancestors
  abiNativeDynamicArrayPrefixState abiNativeDynamicArrayUpdateState abiNativeEncodingDefs abiMemoryLeafRun
  abiDynamicLoopRun abiDynamicLoopCode abiDynamicLoopStep abiFieldOperands abiStaticLoopCode
  compileEnv venomState list words arithmetic

Theorem abi_native_dynamic_array_next_operands:
  !ctx func cs dst src width stride len_op mid child_len dst_addr root_addr counter_addr dyn_addr length_word
      ss out encoded_addr payload index tail_offset child_size.
    abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len encoded_addr payload
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr length_word ss) out /\ cs.cs_next_var + 15 <= mid.cs_next_var ==>
    !arg_op. abi_operand_before (cs.cs_next_var + 3) arg_op ==>
      eval_operand arg_op (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size out) =
        eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  rpt gen_tac >> DISCH_TAC >>
  `abi_operand_before mid.cs_next_var arg_op /\
    abi_operand_before (abi_dynamic_loop_prefix_cut dst src width stride len_op cs).cs_next_var arg_op` by
    (conj_tac >> irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var + 3` >>
     asm_simp_tac (srw_ss()) [abi_dynamic_loop_prefix_cut_def] >> decide_tac) >>
  qspecl_then [`cs`, `mid`, `dst_addr`, `width`, `counter_addr`, `dyn_addr`, `index`, `tail_offset`, `child_size`, `out`, `arg_op`]
    mp_tac abi_native_dynamic_array_next_old_operand >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`, `length_word`, `ss`, `arg_op`]
    mp_tac abi_native_dynamic_array_prefix_old_operand >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qpat_assum `!arg_op. abi_operand_before _ _ ==> _` (qspec_then `arg_op` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >> asm_simp_tac bool_ss []
QED

Theorem abi_native_dynamic_array_next_ready:
  !cs mid dst src len_op dst_addr root_addr counter_addr dyn_addr loop_count index ss out width tail_offset child_size.
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr loop_count index ss /\ ~out.vs_halted /\
    (!arg_op. abi_operand_before (cs.cs_next_var + 3) arg_op ==>
      eval_operand arg_op (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size out) =
        eval_operand arg_op ss) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr loop_count (index + 1)
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size out)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_dynamic_loop_ready _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_dynamic_loop_ready_def]) >>
  qspecl_then [`cs`, `mid`, `dst_addr`, `width`, `counter_addr`, `dyn_addr`, `index`, `tail_offset`, `child_size`, `out`]
    strip_assume_tac abi_native_dynamic_array_next_control >>
  `abi_operand_before (cs.cs_next_var + 3) (Var (compiler_var_name cs.cs_next_var 0)) /\
    abi_operand_before (cs.cs_next_var + 3) (Var (compiler_var_name cs.cs_next_var 1))` by
    (simp[abi_operand_before_def, compiler_var_name_def] >> rpt strip_tac >> decide_tac) >>
  asm_simp_tac bool_ss [abi_dynamic_loop_ready_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual next array header operands and loop readiness: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayNextReady")
