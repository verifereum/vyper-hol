(* TOP-LEVEL: the actual repacking-loop entry initializes its SSA counter
   and enters the generated header. Replaying the entry preserves memory
   and every operand except the counter; undefined output names are not needed. *)
Theory typedArrayLoopEntry
Ancestors
  typedArrayLoopCode typedArrayLoopStructure typedArrayLoopHeader
  abiStaticLoopCode abiStaticLoopBody ssaOperandFrame fragBlockPath fragExec
  compileEnv exprLoweringProps emitHelperProps venomExecSemantics venomState venomInst
  list rich_list words arithmetic

val typed_entry_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in aconv (rhs guard) ``ASSIGN`` end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem typed_array_loop_entry_split:
  !id var_base cond_label.
    typed_array_loop_entry id var_base cond_label =
      TAKE 1 (typed_array_loop_entry id var_base cond_label) ++
      [EL 1 (typed_array_loop_entry id var_base cond_label)]
Proof
  simp[typed_array_loop_entry_def]
QED

Theorem typed_array_loop_entry_execution:
  !id var_base cond_label ss.
    run_inst_seq (TAKE 1 (typed_array_loop_entry id var_base cond_label)) ss =
      OK (update_var (compiler_var_name var_base 0) 0w ss)
Proof
  asm_simp_tac (srw_ss()) (typed_entry_steps @
    [typed_array_loop_entry_def, run_inst_seq_def, mk_inst_def, eval_operand_lit])
QED

Theorem typed_array_loop_entry_terminator:
  !id var_base cond_label ss index.
    step_inst_base (EL 1 (typed_array_loop_entry id var_base cond_label))
      (ss with vs_inst_idx := index) = OK (jump_to cond_label ss)
Proof
  simp[typed_array_loop_entry_def, step_inst_base_jump_index]
QED

Theorem typed_array_loop_entry_frame:
  !var_base cond_label ss.
    (jump_to cond_label (update_var (compiler_var_name var_base 0) 0w ss)).vs_memory = ss.vs_memory /\
    (jump_to cond_label (update_var (compiler_var_name var_base 0) 0w ss)).vs_halted = ss.vs_halted /\
    eval_operand (Var (compiler_var_name var_base 0))
      (jump_to cond_label (update_var (compiler_var_name var_base 0) 0w ss)) = SOME 0w /\
    (!arg_op. arg_op <> Var (compiler_var_name var_base 0) ==>
      eval_operand arg_op (jump_to cond_label (update_var (compiler_var_name var_base 0) 0w ss)) =
        eval_operand arg_op ss)
Proof
  simp[eval_operand_jump_to_eq, eval_operand_update_var, eval_operand_update_var_avoids,
    jump_to_def, update_var_def]
QED

Theorem typed_array_loop_entry_path:
  !ctx func cs cond_label body_label exit_label len_op dst src dst_size src_size ss.
    fn_has_code cs
      (typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    ~ss.vs_halted ==>
    fragment_path ctx func ss
      (jump_to cond_label (update_var (compiler_var_name cs.cs_next_var 0) 0w ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_array_loop_prefix_contains >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `update_var (compiler_var_name cs.cs_next_var 0) 0w ss`,
    `jump_to cond_label (update_var (compiler_var_name cs.cs_next_var 0) 0w ss)`,
    `<| bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
      typed_array_loop_entry cs.cs_next_id cs.cs_next_var cond_label |>`,
    `<| bb_label := cond_label; bb_instructions := typed_array_loop_header cs.cs_next_id
      cs.cs_next_var body_label exit_label len_op |>`,
    `TAKE 1 (typed_array_loop_entry cs.cs_next_id cs.cs_next_var cond_label)`,
    `EL 1 (typed_array_loop_entry cs.cs_next_id cs.cs_next_var cond_label)`]
    fragment_path_block) >> impl_tac
  >- (simp[DROP_LENGTH_APPEND, typed_array_loop_entry_execution,
        typed_array_loop_entry_terminator, typed_array_loop_header_no_phi, jump_to_def, update_var_def] >>
      simp[typed_array_loop_entry_def, mk_inst_def, is_terminator_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed array-copy entry theorem: " ^ name)
  end) (DB.thms "typedArrayLoopEntry")
