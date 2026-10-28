(* TOP-LEVEL: a reusable raw-pointer contract for actual recursive typed
   memory copies. Source and destination have complete typed layouts and
   disjoint physical footprints; generated names come from compiler cuts. *)
Theory typedCopyContract
Ancestors
  typedCopyStateFrame typedSArrayDynInvariant typedArrayLoopCode typedArrayLoopStructure typedDynLoopCode
  memoryValueDefs valueEncoding abiBytestringCode abiStaticLoopCode compileEnv fragExec fragBlockPath
  venomExecSemantics venomState venomInst list words arithmetic

Definition cut_continuation_no_phi_def:
  cut_continuation_no_phi cs func <=>
    cs.cs_current_insts = [] ==>
      ?bb. lookup_block cs.cs_current_bb func.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0
End

Definition typed_copy_contract_def:
  typed_copy_contract ctx func dst src ftv atv start after <=>
    !ss v dst_addr src_addr.
      fn_has_code start after func /\ cut_continuation_no_phi after func /\
      ss.vs_current_bb = start.cs_current_bb /\ ss.vs_inst_idx = LENGTH start.cs_current_insts /\ ~ss.vs_halted /\
      value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory /\
      eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
      w2n src_addr + type_memory_size atv < dimword(:256) /\
      w2n dst_addr + type_memory_size ftv < dimword(:256) /\
      (w2n src_addr + type_memory_size atv <= w2n dst_addr \/
        w2n dst_addr + type_memory_size ftv <= w2n src_addr) /\
      EVERY (\name. dst <> Var name /\ src <> Var name)
        (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
      ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
        out.vs_current_bb = after.cs_current_bb /\ out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
        memory_value_rel ftv v (w2n dst_addr) out.vs_memory /\
        array_copy_frame ftv 1 (w2n dst_addr) ss.vs_memory out.vs_memory /\
        (!arg_op. EVERY (\name. arg_op <> Var name)
          (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
          eval_operand arg_op out = eval_operand arg_op ss)
End

Theorem dynarray_copy_child_continuation:
  !cs after func.
    fn_has_code after (dynarray_copy_finish cs after) func ==>
    cut_continuation_no_phi after func
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [cut_continuation_no_phi_def] >> DISCH_TAC >>
  qpat_x_assum `fn_has_code _ _ _` (mp_tac o REWRITE_RULE [dynarray_copy_finish_def]) >> DISCH_TAC >>
  drule typed_array_loop_suffix_contains >> DISCH_TAC >>
  qexists_tac `<| bb_label := after.cs_current_bb;
    bb_instructions := after.cs_current_insts ++ typed_array_loop_counter after.cs_next_id after.cs_next_var
      (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label) |>` >>
  simp[typed_array_loop_counter_def, phi_prefix_length_def, mk_inst_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive typed-copy contract: " ^ name)
  end) (DB.thms "typedCopyContract")
