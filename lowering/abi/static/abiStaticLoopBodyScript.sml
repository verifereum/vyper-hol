(* TOP-LEVEL: execution of the actual static-element array-loop body, allowing
   its SSA outputs to be overwritten. Memory aliases are retained in the
   exact copy/store effect; allocation separation is a caller obligation. *)
Theory abiStaticLoopBody
Ancestors
  abiStaticLoopCode ssaOperandFrame fragBlockPath fragExec compileEnv
  exprLoweringProps emitHelperProps venomExecSemantics venomState venomInst venomMemProps
  list rich_list words arithmetic
Libs wordsLib

Definition static_info_memory_def:
  static_info_memory AbiPrimWord (dst_addr:bytes32) (src_addr:bytes32) ss =
    mstore (w2n dst_addr) (mload (w2n src_addr) ss) ss /\
  static_info_memory (AbiCopy copy_size) dst_addr src_addr ss =
    mcopy (w2n dst_addr) (w2n src_addr) (w2n (n2w copy_size:bytes32)) ss /\
  static_info_memory _ dst_addr src_addr ss = ss
End

Definition abi_static_loop_body_memory_def:
  abi_static_loop_body_memory info (dst_addr:bytes32) (src_addr:bytes32)
      abi_sz mem_sz (counter_addr:bytes32) ss =
    let counter = mload (w2n counter_addr) ss in
    let child_src = src_addr + 32w + counter * n2w mem_sz in
    let child_dst = dst_addr + 32w + counter * n2w abi_sz in
    mstore (w2n counter_addr) (counter + 1w)
      (static_info_memory info child_dst child_src ss)
End

Definition abi_static_loop_body_work_def:
  abi_static_loop_body_work id var_base labels dst src info abi_sz mem_sz =
    FRONT (abi_static_loop_body id var_base labels dst src info abi_sz mem_sz)
End

Definition abi_static_loop_body_names_def:
  abi_static_loop_body_names var_base info =
    [compiler_var_name var_base 4; compiler_var_name var_base 5;
     compiler_var_name var_base 6; compiler_var_name var_base 7;
     compiler_var_name var_base 8; compiler_var_name var_base 9;
     compiler_var_name var_base 10; compiler_var_name var_base 11] ++
    (case info of AbiPrimWord => [compiler_var_name var_base 12] | _ => [])
End

val body_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``ADD``, ``MUL``, ``MSTORE``, ``MCOPY``, ``JMP``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

val loop_record_projection_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [venom_state_accfupds, combinTheory.K_THM, LET_THM];

Theorem abi_static_loop_body_work_straight:
  !id var_base labels dst src info abi_sz mem_sz.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (abi_static_loop_body_work id var_base labels dst src info abi_sz mem_sz)
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abi_static_loop_body_work_def, abi_static_loop_body_def,
    abi_static_loop_body_prefix_def, static_info_insts_def,
    static_info_id_count_def, FRONT_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem abi_static_loop_body_execution:
  !id var_base labels dst src info abi_sz mem_sz ss dst_addr src_addr counter_addr.
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (abi_static_loop_body_names var_base info) ==>
    ?out.
      run_inst_seq (abi_static_loop_body_work id var_base labels dst src info abi_sz mem_sz)
        ss = OK out /\
      out with vs_vars := ss.vs_vars =
        abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (abi_static_loop_body_names var_base info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `info` >>
  fs[abi_static_loop_body_names_def] >>
  asm_simp_tac (srw_ss()) (body_steps @
    [abi_static_loop_body_work_def, abi_static_loop_body_def,
     abi_static_loop_body_prefix_def, static_info_insts_def,
     static_info_id_count_def, static_info_var_count_def, compiler_var_name_add,
     FRONT_APPEND, run_inst_seq_def, mk_inst_def,
     exec_read1_def, exec_pure2_def, exec_write2_def,
     eval_operand_update_var_avoids, eval_operand_update_var,
     eval_operand_mstore_eq, eval_operand_mcopy_eq, eval_operand_lit,
     mload_update_var, mstore_update_var, mcopy_update_var,
     update_var_reset_vars, GSYM mstore_reset_vars, GSYM mcopy_reset_vars,
     static_info_memory_def, abi_static_loop_body_memory_def, LET_THM]) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  simp[eval_operand_update_var_avoids, eval_operand_mstore_eq, eval_operand_mcopy_eq]
QED

Theorem abi_static_loop_body_memory_counter:
  !info dst_addr src_addr abi_sz mem_sz counter_addr ss.
    mload (w2n counter_addr)
      (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss) =
      mload (w2n counter_addr) ss + 1w
Proof
  simp[abi_static_loop_body_memory_def, LET_THM, mload_mstore_same]
QED

Theorem abi_static_loop_body_memory_control[simp]:
  !info dst_addr src_addr abi_sz mem_sz counter_addr ss.
    (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss).
      vs_current_bb = ss.vs_current_bb /\
    (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss).
      vs_inst_idx = ss.vs_inst_idx /\
    (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss).
      vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp_tac loop_record_projection_ss
    [abi_static_loop_body_memory_def, static_info_memory_def, mstore_def,
    mcopy_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem abi_static_loop_body_split:
  !id var_base labels dst src info abi_sz mem_sz.
    abi_static_loop_body id var_base labels dst src info abi_sz mem_sz =
      abi_static_loop_body_work id var_base labels dst src info abi_sz mem_sz ++
      [mk_inst (id + 16 + static_info_id_count info) JMP
        [Label (fresh_label_output "enc_dyn_hdr" labels)] []]
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abi_static_loop_body_work_def, abi_static_loop_body_def,
    abi_static_loop_body_prefix_def, static_info_insts_def,
    static_info_id_count_def, FRONT_APPEND] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[]
QED

Theorem step_inst_base_jump_index:
  !id label ss index.
    step_inst_base (mk_inst id JMP [Label label] []) (ss with vs_inst_idx := index) =
      OK (jump_to label ss)
Proof
  asm_simp_tac (srw_ss()) (body_steps @
    [mk_inst_def, jump_to_def, venom_state_component_equality])
QED

Theorem eval_operand_jump_to_eq:
  !arg_op label ss. eval_operand arg_op (jump_to label ss) = eval_operand arg_op ss
Proof
  Cases_on `arg_op` >> simp[eval_operand_def, lookup_var_def, jump_to_def]
QED

Theorem mload_reset_vars_eq:
  !offset vars ss. mload offset (ss with vs_vars := vars) = mload offset ss
Proof
  simp_tac loop_record_projection_ss [mload_def]
QED

Theorem memory_reads_jump_to:
  (!offset label ss. mload offset (jump_to label ss) = mload offset ss) /\
  (!offset read_len label ss.
    read_memory offset read_len (jump_to label ss) = read_memory offset read_len ss)
Proof
  simp_tac loop_record_projection_ss [mload_def, read_memory_def, jump_to_def]
QED

Theorem memory_writes_jump_to:
  (!offset bytes label ss.
    write_memory_with_expansion offset bytes (jump_to label ss) =
      jump_to label (write_memory_with_expansion offset bytes ss)) /\
  (!offset value label ss.
    mstore offset value (jump_to label ss) = jump_to label (mstore offset value ss)) /\
  (!dst src read_len label ss.
    mcopy dst src read_len (jump_to label ss) = jump_to label (mcopy dst src read_len ss))
Proof
  simp_tac loop_record_projection_ss
    [write_memory_with_expansion_def, mstore_def, mcopy_def, read_memory_def,
     jump_to_def, venom_state_component_equality]
QED

Theorem abi_static_loop_body_memory_reset_vars:
  !info dst_addr src_addr abi_sz mem_sz counter_addr vars ss.
    abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr
      (ss with vs_vars := vars) =
    (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss)
      with vs_vars := vars
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abi_static_loop_body_memory_def, static_info_memory_def, LET_THM,
    mload_reset_vars_eq, mstore_reset_vars, mcopy_reset_vars]
QED

Theorem abi_static_loop_body_memory_jump_to:
  !info dst_addr src_addr abi_sz mem_sz counter_addr label ss.
    abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr
      (jump_to label ss) =
    jump_to label (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss)
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abi_static_loop_body_memory_def, static_info_memory_def, LET_THM,
    memory_reads_jump_to, memory_writes_jump_to]
QED

Theorem abi_static_loop_body_path:
  !ctx func id var_base labels dst src info abi_sz mem_sz ss dst_addr src_addr
      counter_addr body_bb header_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME body_bb /\
    body_bb.bb_instructions = abi_static_loop_body id var_base labels dst src info abi_sz mem_sz /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (abi_static_loop_body_names var_base info) /\
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    phi_prefix_length header_bb.bb_instructions = 0 ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\ out.vs_inst_idx = 0 /\
      ~out.vs_halted /\
      out with vs_vars := ss.vs_vars =
        jump_to (fresh_label_output "enc_dyn_hdr" labels)
          (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (abi_static_loop_body_names var_base info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `labels`, `dst`, `src`, `info`, `abi_sz`, `mem_sz`,
    `ss`, `dst_addr`, `src_addr`, `counter_addr`] abi_static_loop_body_execution) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq _ ss = OK raw_out` >>
  `~raw_out.vs_halted` by
    (qpat_x_assum `raw_out with vs_vars := _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >> simp[]) >>
  `fragment_path ctx func ss (jump_to (fresh_label_output "enc_dyn_hdr" labels) raw_out)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `raw_out`,
       `jump_to (fresh_label_output "enc_dyn_hdr" labels) raw_out`, `body_bb`, `header_bb`,
       `abi_static_loop_body_work id var_base labels dst src info abi_sz mem_sz`,
       `mk_inst (id + 16 + static_info_id_count info) JMP
         [Label (fresh_label_output "enc_dyn_hdr" labels)] []`] fragment_path_block) >>
     simp[abi_static_loop_body_split, abi_static_loop_body_work_straight,
       step_inst_base_jump_index, mk_inst_def, is_terminator_def, jump_to_def]) >>
  `((jump_to (fresh_label_output "enc_dyn_hdr" labels) raw_out) with vs_vars := ss.vs_vars) =
    jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss)` by
    (qpat_x_assum `raw_out with vs_vars := _ = _`
       (mp_tac o AP_TERM ``\s:venom_state.
         jump_to (fresh_label_output "enc_dyn_hdr" labels) s``) >> simp[jump_to_def]) >>
  qexists_tac `jump_to (fresh_label_output "enc_dyn_hdr" labels) raw_out` >>
  simp[eval_operand_jump_to_eq, jump_to_def]
QED
