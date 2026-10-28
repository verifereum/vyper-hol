(* TOP-LEVEL: aggregate ABI setup allocates or reuses its actual counter
   cell and initializes it to the complete head size. Input SSA names need
   not be undefined, so setup can execute inside an enclosing loop. *)
Theory abiComplexEntry
Ancestors
  abiComplexCode abiStaticLoopEntry abiStaticLoopCode ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath
  venomExecSemantics venomState venomInst venomMemProps finite_map list rich_list words arithmetic
Libs wordsLib

Definition abi_complex_prefix_state_def:
  abi_complex_prefix_state id var_base head_size ss =
    mstore (w2n (abi_static_loop_counter_addr id ss)) (n2w head_size)
      (update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
        (abi_static_loop_alloc_frame id ss))
End

val complex_entry_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``ALLOCA``, ``MSTORE``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_complex_prefix_execution:
  !head_size id var_base ss.
    run_inst_seq (abi_complex_prefix_insts head_size id var_base) ss =
      OK (abi_complex_prefix_state id var_base head_size ss)
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id`
  >- asm_simp_tac (srw_ss()) (complex_entry_steps @
       [abi_complex_prefix_insts_def, abi_complex_prefix_state_def,
        abi_static_loop_counter_addr_def, abi_static_loop_alloc_frame_def,
        run_inst_seq_def, mk_inst_def, exec_alloca_def, exec_write2_def,
        eval_operand_update_var, eval_operand_lit, LET_THM]) >>
  rename1 `FLOOKUP _ _ = SOME recorded_region` >> PairCases_on `recorded_region` >>
  asm_simp_tac (srw_ss()) (complex_entry_steps @
    [abi_complex_prefix_insts_def, abi_complex_prefix_state_def,
     abi_static_loop_counter_addr_def, abi_static_loop_alloc_frame_def,
     run_inst_seq_def, mk_inst_def, exec_alloca_def, exec_write2_def,
     eval_operand_update_var, eval_operand_lit, LET_THM])
QED

Theorem abi_complex_prefix_control[simp]:
  !id var_base head_size ss.
    (abi_complex_prefix_state id var_base head_size ss).vs_current_bb = ss.vs_current_bb /\
    (abi_complex_prefix_state id var_base head_size ss).vs_inst_idx = ss.vs_inst_idx /\
    (abi_complex_prefix_state id var_base head_size ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id` >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM, LET_THM,
     TypeBase.distinct_of ``:(num # num) option``])
    [abi_complex_prefix_state_def, abi_static_loop_alloc_frame_def,
     update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_complex_prefix_operand_frame:
  !id var_base head_size ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) ==>
    eval_operand arg_op (abi_complex_prefix_state id var_base head_size ss) = eval_operand arg_op ss
Proof
  simp[abi_complex_prefix_state_def, eval_operand_mstore_eq,
    eval_operand_update_var_avoids, abi_static_loop_alloc_frame_operand]
QED

Theorem abi_complex_prefix_counter:
  !id var_base head_size ss.
    eval_operand (Var (compiler_var_name var_base 0)) (abi_complex_prefix_state id var_base head_size ss) =
      SOME (abi_static_loop_counter_addr id ss) /\
    mload (w2n (abi_static_loop_counter_addr id ss)) (abi_complex_prefix_state id var_base head_size ss) =
      n2w head_size
Proof
  simp[abi_complex_prefix_state_def, eval_operand_mstore_eq, eval_operand_update_var, mload_mstore_same]
QED

Theorem abi_complex_prefix_path:
  !ctx func head_size cs ss.
    fn_has_code cs (abi_complex_prefix_cut head_size cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss
      ((abi_complex_prefix_state cs.cs_next_id cs.cs_next_var head_size ss) with
        vs_inst_idx := LENGTH (abi_complex_prefix_cut head_size cs).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `abi_complex_prefix_cut head_size cs`, `ss`,
    `abi_complex_prefix_state cs.cs_next_id cs.cs_next_var head_size ss`] fragment_path_emitted) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [abi_complex_prefix_cut_def, emitted_insts_def, same_blocks_def,
        DROP_LENGTH_APPEND, abi_complex_prefix_execution] >>
      simp[abi_complex_prefix_insts_def, mk_inst_def, is_terminator_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed aggregate ABI counter setup: " ^ name)
  end) (DB.thms "abiComplexEntry")
