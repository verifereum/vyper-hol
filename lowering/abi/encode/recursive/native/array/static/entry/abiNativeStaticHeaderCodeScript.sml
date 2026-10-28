(* TOP-LEVEL: the real static-loop compiler point after counter setup is
   its empty header block. Both compiler extensions and fresh-name history
   are derived from the actual loop action. *)
Theory abiNativeStaticHeaderCode
Ancestors
  abiStaticLoopCode abiStaticLoopComplete abiStaticLoopIteration abiStaticLoopBody abiStaticLoopExit abiStaticLoopExec
  abiDynArrayCode abiIdFlow abiFieldOperands compileIdFlow compileAllocaProvenance compileEnv fragExec
  venomState venomInst list rich_list words arithmetic

Definition abi_native_static_header_cut_def:
  abi_native_static_header_cut cs =
    cs with <| cs_next_id := cs.cs_next_id + 3; cs_next_var := cs.cs_next_var + 1;
      cs_next_label := cs.cs_next_label + 3;
      cs_current_bb := fresh_label_output "enc_dyn_hdr" cs.cs_next_label; cs_current_insts := [];
      cs_blocks := <|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
        abi_static_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label|> :: cs.cs_blocks |>
End

Theorem abi_native_static_header_extends:
  !cs. cs_extends cs (abi_native_static_header_cut cs)
Proof
  gen_tac >> simp_tac bool_ss [cs_extends_def, abi_native_static_header_cut_def] >>
  qexists_tac `[<|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
    abi_static_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label|>]` >> simp[IS_PREFIX_APPEND]
QED

Theorem abi_native_static_header_continuation:
  !dst src info width stride len_op cs ret after.
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) ==>
    cs_extends (abi_native_static_header_cut cs) after
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_abi_encode_dyn_static_loop_result] >> strip_tac >> gvs[] >>
  simp_tac bool_ss [cs_extends_def, abi_native_static_header_cut_def] >>
  qexists_tac
    `[<|bb_label := fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1);
        bb_instructions := abi_static_loop_body cs.cs_next_id cs.cs_next_var cs.cs_next_label dst src info width stride|>;
      <|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
        bb_instructions := abi_static_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|>]` >> simp[]
QED

Theorem abi_native_static_header_history:
  !cs. compiler_id_history cs ==> compiler_id_history (abi_native_static_header_cut cs)
Proof
  gen_tac >> simp[compiler_id_history_def, abi_native_static_header_cut_def,
    abi_static_loop_entry_def, mk_inst_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem abi_native_static_header_after_flow:
  !dst src info width stride len_op cs ret after.
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\ compiler_id_history cs ==>
    compiler_id_history after /\ (abi_native_static_header_cut cs).cs_next_var <= after.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`compile_abi_encode_dyn_static_loop dst src info width stride len_op`, `cs`, `ret`, `after`]
    mp_tac compiler_id_flow_result >> impl_tac >- simp[compiler_id_flow_abi_static_loop] >> strip_tac >>
  `compiler_id_history after` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  drule compile_abi_encode_dyn_static_loop_cut >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_native_static_header_cut_def] >> decide_tac
QED

Theorem abi_native_static_header_operand_names:
  !var_base info arg_op.
    abi_operand_before (var_base + 1) arg_op ==>
    EVERY (\name. arg_op <> Var name) (abi_static_loop_tail_names var_base info)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_operand_before_def] >> DISCH_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [compiler_var_name_def, ADD_0]) >>
  Cases_on `info` >> simp_tac (srw_ss()) [abi_static_loop_tail_names_def, abi_static_loop_iteration_names_def,
    abi_static_loop_body_names_def, abi_static_loop_exit_names_def, compiler_var_name_def] >>
  rpt conj_tac >> first_x_assum irule >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static header compiler context: " ^ name)
  end) (DB.thms "abiNativeStaticHeaderCode")
