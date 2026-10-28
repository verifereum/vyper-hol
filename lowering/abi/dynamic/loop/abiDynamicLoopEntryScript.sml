(* TOP-LEVEL: initialize the actual index and tail-offset cells, supporting
   both fresh and replayed allocations, then jump to the loop header. *)
Theory abiDynamicLoopEntry
Ancestors
  abiDynamicLoopCode abiStaticLoopEntry abiStaticLoopCode abiStaticLoopBody memoryValueAbiExec ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath
  venomExecSemantics venomState venomInst venomMemProps finite_map list words arithmetic
Libs wordsLib

Definition abi_dynamic_loop_entry_tail_state_def:
  abi_dynamic_loop_entry_tail_state id var_base abi_sz (len_word:bytes32) ss =
    let dyn_addr = abi_static_loop_counter_addr (id + 2) ss in
    let initial_tail = len_word * n2w abi_sz in
    mstore (w2n dyn_addr) initial_tail
      (update_var (compiler_var_name var_base 2) initial_tail
        (update_var (compiler_var_name var_base 1) dyn_addr (abi_static_loop_alloc_frame (id + 2) ss)))
End

Definition abi_dynamic_loop_entry_state_def:
  abi_dynamic_loop_entry_state id var_base abi_sz len_word ss =
    abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word (abi_static_loop_entry_state id var_base ss)
End

val dynamic_entry_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``ALLOCA``, ``MUL``, ``MSTORE``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_dynamic_loop_entry_split:
  !id var_base labels abi_sz len_op.
    TAKE 5 (abi_dynamic_loop_entry id var_base labels abi_sz len_op) =
    TAKE 2 (abi_dynamic_loop_entry id var_base labels abi_sz len_op) ++
    TAKE 3 (DROP 2 (abi_dynamic_loop_entry id var_base labels abi_sz len_op))
Proof
  simp[abi_dynamic_loop_entry_def]
QED

Theorem abi_dynamic_loop_entry_first_execution:
  !id var_base labels abi_sz len_op ss.
    run_inst_seq (TAKE 2 (abi_dynamic_loop_entry id var_base labels abi_sz len_op)) ss =
      OK (abi_static_loop_entry_state id var_base ss)
Proof
  rpt gen_tac >> mp_tac (Q.SPECL [`id`, `var_base`, `labels`, `ss`] abi_static_loop_entry_execution) >>
  simp[abi_dynamic_loop_entry_def, abi_static_loop_entry_def]
QED

Theorem abi_dynamic_loop_entry_tail_execution:
  !id var_base labels abi_sz len_op ss len_word.
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name var_base 1) ==>
    run_inst_seq (TAKE 3 (DROP 2 (abi_dynamic_loop_entry id var_base labels abi_sz len_op))) ss =
      OK (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand len_op (abi_static_loop_alloc_frame (id + 2) ss) = SOME len_word` by
    simp[abi_static_loop_alloc_frame_operand] >>
  qpat_x_assum `eval_operand len_op (abi_static_loop_alloc_frame _ _) = _` mp_tac >>
  Cases_on `FLOOKUP ss.vs_allocas (id + 2)`
  >- asm_simp_tac (srw_ss()) (dynamic_entry_steps @
       [abi_dynamic_loop_entry_def, abi_dynamic_loop_entry_tail_state_def,
        abi_static_loop_counter_addr_def, abi_static_loop_alloc_frame_def,
        run_inst_seq_def, mk_inst_def, exec_alloca_def, exec_pure2_def, exec_write2_def,
        eval_operand_update_var_avoids, eval_operand_update_var, eval_operand_lit, LET_THM]) >>
  rename1 `FLOOKUP _ _ = SOME recorded_region` >> PairCases_on `recorded_region` >>
  asm_simp_tac (srw_ss()) (dynamic_entry_steps @
    [abi_dynamic_loop_entry_def, abi_dynamic_loop_entry_tail_state_def,
     abi_static_loop_counter_addr_def, abi_static_loop_alloc_frame_def,
     run_inst_seq_def, mk_inst_def, exec_alloca_def, exec_pure2_def, exec_write2_def,
     eval_operand_update_var_avoids, eval_operand_update_var, eval_operand_lit, LET_THM])
QED

Theorem abi_dynamic_loop_entry_execution:
  !id var_base labels abi_sz len_op ss len_word.
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name var_base 0) /\
    len_op <> Var (compiler_var_name var_base 1) ==>
    run_inst_seq (TAKE 5 (abi_dynamic_loop_entry id var_base labels abi_sz len_op)) ss =
      OK (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand len_op (abi_static_loop_entry_state id var_base ss) = SOME len_word` by
    simp[abi_static_loop_entry_operand_frame] >>
  mp_tac (Q.SPECL [`id`, `var_base`, `labels`, `abi_sz`, `len_op`,
    `abi_static_loop_entry_state id var_base ss`, `len_word`] abi_dynamic_loop_entry_tail_execution) >>
  impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`TAKE 2 (abi_dynamic_loop_entry id var_base labels abi_sz len_op)`,
    `TAKE 3 (DROP 2 (abi_dynamic_loop_entry id var_base labels abi_sz len_op))`, `ss`,
    `abi_static_loop_entry_state id var_base ss`] run_inst_seq_append) >>
  impl_tac >- simp[abi_dynamic_loop_entry_first_execution] >>
  asm_simp_tac bool_ss [abi_dynamic_loop_entry_split, abi_dynamic_loop_entry_state_def]
QED

Theorem abi_dynamic_loop_entry_tail_control:
  !id var_base abi_sz len_word ss.
    (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas (id + 2)` >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM, LET_THM, TypeBase.distinct_of ``:(num # num) option``])
    [abi_dynamic_loop_entry_tail_state_def, abi_static_loop_alloc_frame_def,
     update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_dynamic_loop_entry_control:
  !id var_base abi_sz len_word ss.
    (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_control, abi_static_loop_entry_control]
QED

Theorem abi_dynamic_loop_entry_terminator:
  !id var_base labels abi_sz len_op ss inst_idx.
    step_inst_base (EL 5 (abi_dynamic_loop_entry id var_base labels abi_sz len_op))
      (ss with vs_inst_idx := inst_idx) = OK (jump_to (fresh_label_output "enc_dyn_hdr" labels) ss)
Proof
  simp[abi_dynamic_loop_entry_def, step_inst_base_jump_index]
QED

Theorem abi_dynamic_loop_entry_path:
  !ctx func id var_base labels abi_sz len_op ss len_word entry_bb header_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME entry_bb /\
    DROP ss.vs_inst_idx entry_bb.bb_instructions = abi_dynamic_loop_entry id var_base labels abi_sz len_op /\
    ~ss.vs_halted /\ eval_operand len_op ss = SOME len_word /\
    len_op <> Var (compiler_var_name var_base 0) /\ len_op <> Var (compiler_var_name var_base 1) /\
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    phi_prefix_length header_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss (jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `labels`, `abi_sz`, `len_op`, `ss`, `len_word`]
    abi_dynamic_loop_entry_execution) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `abi_dynamic_loop_entry_state id var_base abi_sz len_word ss`,
    `jump_to (fresh_label_output "enc_dyn_hdr" labels) (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss)`,
    `entry_bb`, `header_bb`, `TAKE 5 (abi_dynamic_loop_entry id var_base labels abi_sz len_op)`,
    `EL 5 (abi_dynamic_loop_entry id var_base labels abi_sz len_op)`] fragment_path_block) >>
  impl_tac
  >- (simp[abi_dynamic_loop_entry_terminator, abi_dynamic_loop_entry_control, jump_to_def] >>
      simp[abi_dynamic_loop_entry_def, mk_inst_def, is_terminator_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop counter initialization: " ^ name)
  end) (DB.thms "abiDynamicLoopEntry")
