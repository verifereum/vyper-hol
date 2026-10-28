(* TOP-LEVEL: containment of the static-element ABI loop supplies
   its entry, header, body and open exit in the containing function.
   Helpers: generated blocks have no PHI prefix; the exit is straight-line. *)
Theory abiStaticLoopCodeProps
Ancestors
  abiStaticLoopCode fragExec compileEnv venomExecSemantics venomInst
  list rich_list arithmetic

Theorem compile_abi_encode_dyn_static_loop_contains:
  !dst src info abi_sz mem_sz len_op cs op cs' func.
    compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    fn_has_code cs cs' func ==>
    lookup_block (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) func.fn_blocks =
      SOME <| bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
              bb_instructions := abi_static_loop_header cs.cs_next_id cs.cs_next_var
                cs.cs_next_label len_op |> /\
    lookup_block (fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1)) func.fn_blocks =
      SOME <| bb_label := fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1);
              bb_instructions := abi_static_loop_body cs.cs_next_id cs.cs_next_var
                cs.cs_next_label dst src info abi_sz mem_sz |> /\
    lookup_block cs.cs_current_bb func.fn_blocks =
      SOME <| bb_label := cs.cs_current_bb;
              bb_instructions := cs.cs_current_insts ++
                abi_static_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label |> /\
    ?exit_bb.
      lookup_block (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
        func.fn_blocks = SOME exit_bb /\
      isPREFIX (abi_static_loop_exit cs.cs_next_id cs.cs_next_var src info abi_sz)
        exit_bb.bb_instructions
Proof
  rpt gen_tac >>
  simp[compile_abi_encode_dyn_static_loop_result] >> strip_tac >> gvs[] >>
  fs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem abi_static_loop_blocks_no_phi:
  (!id var_base labels.
    phi_prefix_length (abi_static_loop_entry id var_base labels) = 0) /\
  (!id var_base labels len_op.
    phi_prefix_length (abi_static_loop_header id var_base labels len_op) = 0) /\
  (!id var_base labels dst src info abi_sz mem_sz.
    phi_prefix_length (abi_static_loop_body id var_base labels dst src info abi_sz mem_sz) = 0)
Proof
  simp[abi_static_loop_entry_def, abi_static_loop_header_def,
    abi_static_loop_body_def, abi_static_loop_body_prefix_def,
    phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_static_loop_exit_no_phi:
  !id var_base src info abi_sz insts.
    isPREFIX (abi_static_loop_exit id var_base src info abi_sz) insts ==>
    phi_prefix_length insts = 0
Proof
  rpt gen_tac >> simp[IS_PREFIX_APPEND] >> strip_tac >>
  gvs[abi_static_loop_exit_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_static_loop_exit_straight:
  !id var_base src info abi_sz.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (abi_static_loop_exit id var_base src info abi_sz)
Proof
  simp[abi_static_loop_exit_def, mk_inst_def, is_terminator_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop containment theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopCodeProps")
