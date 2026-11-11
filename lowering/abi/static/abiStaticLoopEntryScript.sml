(* TOP-LEVEL: the actual loop entry allocates or reuses its counter cell,
   zeros it, and jumps to the header from the original compiler position.
   Helpers describe the exact ALLOCA effect without assuming SSA freshness. *)
Theory abiStaticLoopEntry
Ancestors
  abiStaticLoopCode abiStaticLoopCodeProps abiStaticLoopBody abiStaticLoopIteration ssaOperandFrame
  fragBlockPath fragExec compileEnv exprLoweringProps emitHelperProps
  venomExecSemantics venomState venomInst venomMemProps
  finite_map list rich_list words arithmetic
Libs wordsLib

Definition abi_static_loop_counter_addr_def:
  abi_static_loop_counter_addr id ss : bytes32 =
    n2w (case FLOOKUP ss.vs_allocas id of
           NONE => ss.vs_alloca_next | SOME (offset,sz) => offset)
End

Definition abi_static_loop_alloc_frame_def:
  abi_static_loop_alloc_frame id ss =
    if FLOOKUP ss.vs_allocas id = NONE then
      ss with <| vs_allocas := ss.vs_allocas |+ (id,(ss.vs_alloca_next,32));
                 vs_alloca_next := ss.vs_alloca_next + 32 |>
    else ss
End

Definition abi_static_loop_entry_state_def:
  abi_static_loop_entry_state id var_base ss =
    mstore (w2n (abi_static_loop_counter_addr id ss)) 0w
      (update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
        (abi_static_loop_alloc_frame id ss))
End

Definition abi_static_loop_start_state_def:
  abi_static_loop_start_state id var_base labels ss =
    jump_to (fresh_label_output "enc_dyn_hdr" labels) (abi_static_loop_entry_state id var_base ss)
End

(* The memory/allocation postcondition image restores the input SSA map. *)
Definition abi_static_loop_initial_memory_def:
  abi_static_loop_initial_memory id labels ss =
    jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (mstore (w2n (abi_static_loop_counter_addr id ss)) 0w (abi_static_loop_alloc_frame id ss))
End

val entry_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``ALLOCA``, ``MSTORE``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

val entry_projection_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [venom_state_accfupds, combinTheory.K_THM, LET_THM,
   TypeBase.distinct_of ``:(num # num) option``];

Theorem abi_static_loop_entry_prefix_straight:
  !id var_base labels.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 2 (abi_static_loop_entry id var_base labels))
Proof
  simp[abi_static_loop_entry_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_static_loop_entry_prefix_length[simp]:
  !id var_base labels. LENGTH (TAKE 2 (abi_static_loop_entry id var_base labels)) = 2
Proof
  simp[abi_static_loop_entry_def]
QED

Theorem abi_static_loop_entry_execution:
  !id var_base labels ss.
    run_inst_seq (TAKE 2 (abi_static_loop_entry id var_base labels)) ss =
      OK (abi_static_loop_entry_state id var_base ss)
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id`
  >- asm_simp_tac (srw_ss()) (entry_steps @
       [abi_static_loop_entry_def, abi_static_loop_entry_state_def,
        abi_static_loop_counter_addr_def, abi_static_loop_alloc_frame_def,
        run_inst_seq_def, mk_inst_def, exec_alloca_def, exec_write2_def,
        eval_operand_update_var, eval_operand_lit, LET_THM]) >>
  rename1 `FLOOKUP _ _ = SOME recorded_region` >> PairCases_on `recorded_region` >>
  asm_simp_tac (srw_ss()) (entry_steps @
    [abi_static_loop_entry_def, abi_static_loop_entry_state_def,
     abi_static_loop_counter_addr_def, abi_static_loop_alloc_frame_def,
     run_inst_seq_def, mk_inst_def, exec_alloca_def, exec_write2_def,
     eval_operand_update_var, eval_operand_lit, LET_THM])
QED

Theorem abi_static_loop_alloc_frame_operand:
  !arg_op id ss.
    eval_operand arg_op (abi_static_loop_alloc_frame id ss) = eval_operand arg_op ss
Proof
  Cases_on `arg_op` >>
  simp[abi_static_loop_alloc_frame_def, eval_operand_def, lookup_var_def] >> rw[]
QED

Theorem abi_static_loop_entry_operand_frame:
  !id var_base ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) ==>
    eval_operand arg_op (abi_static_loop_entry_state id var_base ss) = eval_operand arg_op ss
Proof
  simp[abi_static_loop_entry_state_def, eval_operand_mstore_eq,
    eval_operand_update_var_avoids, abi_static_loop_alloc_frame_operand]
QED

Theorem abi_static_loop_entry_counter:
  !id var_base ss.
    eval_operand (Var (compiler_var_name var_base 0))
      (abi_static_loop_entry_state id var_base ss) = SOME (abi_static_loop_counter_addr id ss) /\
    mload (w2n (abi_static_loop_counter_addr id ss))
      (abi_static_loop_entry_state id var_base ss) = 0w
Proof
  simp[abi_static_loop_entry_state_def, eval_operand_mstore_eq,
    eval_operand_update_var, mload_mstore_same]
QED

Theorem abi_static_loop_entry_control[simp]:
  !id var_base ss.
    (abi_static_loop_entry_state id var_base ss).vs_current_bb = ss.vs_current_bb /\
    (abi_static_loop_entry_state id var_base ss).vs_inst_idx = ss.vs_inst_idx /\
    (abi_static_loop_entry_state id var_base ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id` >>
  asm_simp_tac entry_projection_ss
    [abi_static_loop_entry_state_def, abi_static_loop_alloc_frame_def,
     update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_static_loop_entry_terminator:
  !id var_base labels ss index.
    step_inst_base (EL 2 (abi_static_loop_entry id var_base labels))
      (ss with vs_inst_idx := index) =
    OK (jump_to (fresh_label_output "enc_dyn_hdr" labels) ss)
Proof
  simp[abi_static_loop_entry_def, step_inst_base_jump_index]
QED

Theorem abi_static_loop_start_operand_frame:
  !id var_base labels ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) ==>
    eval_operand arg_op (abi_static_loop_start_state id var_base labels ss) =
      eval_operand arg_op ss
Proof
  simp[abi_static_loop_start_state_def, eval_operand_jump_to_eq,
    abi_static_loop_entry_operand_frame]
QED

Theorem abi_static_loop_start_counter:
  !id var_base labels ss.
    eval_operand (Var (compiler_var_name var_base 0))
      (abi_static_loop_start_state id var_base labels ss) =
      SOME (abi_static_loop_counter_addr id ss) /\
    mload (w2n (abi_static_loop_counter_addr id ss))
      (abi_static_loop_start_state id var_base labels ss) = 0w
Proof
  simp[abi_static_loop_start_state_def, eval_operand_jump_to_eq,
    memory_reads_jump_to, abi_static_loop_entry_counter]
QED

Theorem abi_static_loop_start_control[simp]:
  !id var_base labels ss.
    (abi_static_loop_start_state id var_base labels ss).vs_current_bb =
      fresh_label_output "enc_dyn_hdr" labels /\
    (abi_static_loop_start_state id var_base labels ss).vs_inst_idx = 0 /\
    (abi_static_loop_start_state id var_base labels ss).vs_halted = ss.vs_halted
Proof
  simp[abi_static_loop_start_state_def, jump_to_def]
QED

Theorem abi_static_loop_alloc_frame_reset_vars:
  !id ss. (abi_static_loop_alloc_frame id ss) with vs_vars := ss.vs_vars =
    abi_static_loop_alloc_frame id ss
Proof
  rw[abi_static_loop_alloc_frame_def, venom_state_component_equality]
QED

Theorem abi_static_loop_start_reset_vars:
  !id var_base labels ss.
    (abi_static_loop_start_state id var_base labels ss) with vs_vars := ss.vs_vars =
      abi_static_loop_initial_memory id labels ss
Proof
  simp[abi_static_loop_start_state_def, abi_static_loop_initial_memory_def,
    abi_static_loop_entry_state_def, mstore_update_var, GSYM jump_to_reset_vars_eq,
    update_var_reset_vars, GSYM mstore_reset_vars, abi_static_loop_alloc_frame_reset_vars]
QED

Theorem abi_static_loop_entry_path:
  !ctx func id var_base labels ss entry_bb header_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME entry_bb /\
    DROP ss.vs_inst_idx entry_bb.bb_instructions = abi_static_loop_entry id var_base labels /\
    ~ss.vs_halted /\
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    phi_prefix_length header_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "enc_dyn_hdr" labels)
        (abi_static_loop_entry_state id var_base ss))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `abi_static_loop_entry_state id var_base ss`,
    `jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (abi_static_loop_entry_state id var_base ss)`, `entry_bb`, `header_bb`,
    `TAKE 2 (abi_static_loop_entry id var_base labels)`,
    `EL 2 (abi_static_loop_entry id var_base labels)`] fragment_path_block) >>
  impl_tac
  >- (simp[abi_static_loop_entry_execution, abi_static_loop_entry_prefix_straight,
        abi_static_loop_entry_terminator, jump_to_def] >>
      simp[abi_static_loop_entry_def, step_inst_base_jump_index, mk_inst_def, is_terminator_def]) >>
  simp[]
QED
