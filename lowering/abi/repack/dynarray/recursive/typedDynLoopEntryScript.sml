(* TOP-LEVEL: initialize a generic copy invariant and execute the actual
   dynamic-array counter initialization and jump. Initial source payloads
   and operands outside the loop's compiler-derived range are preserved. *)
Theory typedDynLoopEntry
Ancestors
  typedCopyStateFrame
  typedDynLoopInvariant typedDynLoopControl typedDynLoopCode typedSArrayDynInvariant typedArrayCopyMemory
  typedArrayLoopNames abiBytestringCode abiStaticLoopCode abiStaticLoopBody
  ssaOperandFrame emitHelperProps memoryValueDefs valueEncoding compileEnv
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem array_copy_entry_fields:
  !counter cond_label initial.
    let entry = jump_to cond_label (update_var counter 0w initial) in
    entry.vs_current_bb = cond_label /\ entry.vs_inst_idx = 0 /\
    entry.vs_halted = initial.vs_halted /\ entry.vs_memory = initial.vs_memory /\
    eval_operand (Var counter) entry = SOME 0w
Proof
  simp[LET_THM, eval_operand_jump_to_eq, eval_operand_update_var, jump_to_def, update_var_def]
QED

Theorem array_copy_loop_inv_initial:
  !counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial.
    ~initial.vs_halted /\ MEM counter modified_names /\
    array_copy_prefix atv at_index copy_count (w2n src_data) initial.vs_memory ==>
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count
      src_data dst_data initial 0 (jump_to cond_label (update_var counter 0w initial))
Proof
  rpt gen_tac >> strip_tac >>
  `array_copy_memory_inv ftv atv at_index copy_count (w2n src_data) (w2n dst_data)
    initial.vs_memory 0 initial.vs_memory` by
    (irule array_copy_memory_inv_initial >> simp[]) >>
  `copy_state_frame initial (jump_to cond_label (update_var counter 0w initial))` by simp[] >>
  asm_simp_tac bool_ss [array_copy_loop_inv_def, SIMP_RULE bool_ss [LET_THM] array_copy_entry_fields] >>
  qx_gen_tac `arg_op` >> DISCH_TAC >>
  `arg_op <> Var counter` by fs[EVERY_MEM] >> simp[eval_operand_jump_to_eq, eval_operand_update_var_avoids]
QED

Theorem dynarray_copy_loop_begin:
  !ctx func cenv dst fty capacity src aty cs child_names ftv atv at_index copy_count src_data dst_data ss.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity) (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH (dyn_copy_prefix_state cs dst src capacity).cs_current_insts /\ ~ss.vs_halted /\
    array_copy_prefix atv at_index copy_count (w2n src_data) ss.vs_memory ==>
    ?start. fragment_path ctx func ss start /\
      array_copy_loop_inv (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
        (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ftv atv at_index copy_count src_data dst_data ss 0 start
Proof
  rpt gen_tac >> strip_tac >> drule_all_then (qspec_then `ctx` ASSUME_TAC) dynarray_copy_loop_entry >>
  `MEM (compiler_var_name cs.cs_next_var 5) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names))` by
    (simp[compiler_var_name_def, compiler_var_names_def, MEM_GENLIST] >> qexists_tac `0` >> simp[]) >>
  qabbrev_tac `start = jump_to (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
    (update_var (compiler_var_name cs.cs_next_var 5) 0w ss)` >>
  `array_copy_loop_inv (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
    (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ftv atv at_index copy_count src_data dst_data ss 0 start` by
    (simp_tac bool_ss [Abbr`start`] >> irule array_copy_loop_inv_initial >> simp[]) >>
  qexists_tac `start` >> simp[Abbr`start`]
QED
