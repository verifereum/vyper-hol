(* TOP-LEVEL: actual static-element array-loop compilation executes from
   its original compiler cut through allocation, all iterations and exit.
   The result records the exact memory/allocation image and size word.
   Helpers transport snapshots across counter setup and the final cut. *)
Theory abiStaticLoopExec
Ancestors
  abiStaticLoopCode abiStaticLoopCodeProps abiStaticLoopBody abiStaticLoopEntry
  abiStaticLoopIteration abiStaticLoopRun abiStaticLoopFinish abiStaticLoopComplete
  abiStaticLoopMemory abiStaticLoopFrame abiStaticLoopPayload abiEncoderPathProps memoryReadProps
  fragBlockPath fragExec abiEncoder compileEnv exprLoweringProps
  venomExecSemantics venomState venomInst venomMemProps list rich_list words arithmetic

Definition abi_static_loop_memory_result_def:
  abi_static_loop_memory_result id labels info dst_addr src_addr abi_sz mem_sz n ss =
    (jump_to (fresh_label_output "enc_dyn_exit" (labels + 2))
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz
        (abi_static_loop_counter_addr id ss) labels) n (abi_static_loop_initial_memory id labels ss)))
      with vs_inst_idx := 3
End

Theorem abi_static_loop_memory_result_counter:
  !id labels info dst_addr src_addr abi_sz mem_sz n ss.
    mload (w2n (abi_static_loop_counter_addr id ss))
      (abi_static_loop_memory_result id labels info dst_addr src_addr abi_sz mem_sz n ss) = n2w n
Proof
  simp[abi_static_loop_memory_result_def, mload_inst_idx, memory_reads_jump_to,
    abi_static_loop_effects_counter, abi_static_loop_initial_memory_def,
    mload_mstore_same, WORD_ADD_0]
QED

Theorem abi_static_loop_initial_read_frame:
  !id labels ss offset read_len.
    (offset + read_len <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= offset) ==>
    read_memory offset read_len (abi_static_loop_initial_memory id labels ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory offset read_len (abi_static_loop_alloc_frame id ss) =
    read_memory offset read_len ss` by
    (simp[abi_static_loop_alloc_frame_def, read_memory_def] >> rw[]) >>
  simp_tac bool_ss [abi_static_loop_initial_memory_def, memory_reads_jump_to] >>
  irule EQ_TRANS >> qexists_tac `read_memory offset read_len (abi_static_loop_alloc_frame id ss)` >>
  conj_tac >- (irule read_memory_mstore_disjoint >> fs[]) >> fs[]
QED

Theorem abi_static_loop_memory_result_frame:
  !id labels info copied_count dst_addr src_addr mem_sz n ss offset read_len.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\
    (copied_count = 0 \/ w2n dst_addr + 32 + n * copied_count <= dimword(:256)) /\
    (copied_count = 0 \/ offset + read_len <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * copied_count <= offset) /\
    (offset + read_len <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= offset) ==>
    read_memory offset read_len
      (abi_static_loop_memory_result id labels info dst_addr src_addr copied_count mem_sz n ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`n`, `info`, `copied_count`, `dst_addr`, `src_addr`, `mem_sz`,
    `abi_static_loop_counter_addr id ss`, `labels`, `abi_static_loop_initial_memory id labels ss`,
    `offset`, `read_len`] abi_static_loop_effects_read_frame) >> impl_tac
  >- (simp_tac (srw_ss()) [abi_static_loop_initial_memory_def,
        memory_reads_jump_to, mload_mstore_same] >> gvs[]) >>
  `read_memory offset read_len (abi_static_loop_initial_memory id labels ss) =
    read_memory offset read_len ss` by
    (irule abi_static_loop_initial_read_frame >> fs[]) >>
  simp[abi_static_loop_memory_result_def, read_memory_def, jump_to_def]
QED

Theorem abi_static_loop_memory_result_mload:
  !id labels info copied_count dst_addr src_addr mem_sz n ss offset.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\
    (copied_count = 0 \/ w2n dst_addr + 32 + n * copied_count <= dimword(:256)) /\
    (copied_count = 0 \/ offset + 32 <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * copied_count <= offset) /\
    (offset + 32 <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= offset) ==>
    mload offset
      (abi_static_loop_memory_result id labels info dst_addr src_addr copied_count mem_sz n ss) =
      mload offset ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`id`, `labels`, `info`, `copied_count`, `dst_addr`, `src_addr`,
    `mem_sz`, `n`, `ss`, `offset`, `32`] abi_static_loop_memory_result_frame) >>
  impl_tac >- (gvs[] >> decide_tac) >> simp[mload_read_memory]
QED

Theorem abi_static_loop_memory_result_payload:
  !id labels info elem_size dst_addr src_addr n ss.
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * elem_size <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= w2n dst_addr + 32) ==>
    read_memory (w2n dst_addr + 32) (n * elem_size)
      (abi_static_loop_memory_result id labels info dst_addr src_addr elem_size elem_size n ss) =
      read_memory (w2n src_addr + 32) (n * elem_size) ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `elem_size = 0`
  >- simp[read_memory_def] >>
  mp_tac (Q.SPECL [`n`, `info`, `elem_size`, `dst_addr`, `src_addr`,
    `abi_static_loop_counter_addr id ss`, `labels`, `abi_static_loop_initial_memory id labels ss`]
    abi_static_loop_effects_payload) >> impl_tac
  >- (simp_tac (srw_ss()) [abi_static_loop_initial_memory_def,
        memory_reads_jump_to, mload_mstore_same] >> gvs[]) >>
  `read_memory (w2n src_addr + 32) (n * elem_size) (abi_static_loop_initial_memory id labels ss) =
    read_memory (w2n src_addr + 32) (n * elem_size) ss` by
    (irule abi_static_loop_initial_read_frame >> gvs[] >> decide_tac) >>
  simp[abi_static_loop_memory_result_def, read_memory_def, jump_to_def]
QED

Theorem compile_abi_encode_dyn_static_loop_cut:
  !dst src info abi_sz mem_sz len_op cs op cs'.
    compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len_op cs = (op,cs') ==>
    op = Var (compiler_var_name cs.cs_next_var (14 + static_info_var_count info)) /\
    cs'.cs_current_bb = fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2) /\
    cs'.cs_current_insts = abi_static_loop_exit cs.cs_next_id cs.cs_next_var src info abi_sz /\
    cs'.cs_next_var = cs.cs_next_var + 15 + static_info_var_count info
Proof
  simp[compile_abi_encode_dyn_static_loop_result] >> rpt gen_tac >> strip_tac >> gvs[]
QED

Theorem abi_static_loop_funpow_reset_vars:
  !n info dst_addr src_addr abi_sz mem_sz counter_addr labels vars ss.
    FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels)
      n (ss with vs_vars := vars) =
    (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels) n ss)
      with vs_vars := vars
Proof
  Induct_on `n` >> simp[FUNPOW_SUC, abi_static_loop_effect_reset_vars]
QED

Theorem control_cut_snapshot:
  !out start_vars current_state vars saved_state label cut.
    out with vs_vars := start_vars = (jump_to label current_state) with vs_inst_idx := cut /\
    current_state with vs_vars := vars = saved_state ==>
    out with vs_vars := vars = (jump_to label saved_state) with vs_inst_idx := cut
Proof
  rpt gen_tac >>
  simp[venom_state_component_equality, jump_to_def] >> strip_tac >> fs[]
QED

Theorem abi_static_loop_initialized_snapshot:
  !id var_base labels info dst_addr src_addr abi_sz mem_sz n ss out.
    out with vs_vars := (abi_static_loop_start_state id var_base labels ss).vs_vars =
    (jump_to (fresh_label_output "enc_dyn_exit" (labels + 2))
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz
        (abi_static_loop_counter_addr id ss) labels) n
          (abi_static_loop_start_state id var_base labels ss))) with vs_inst_idx := 3 ==>
    out with vs_vars := ss.vs_vars =
      abi_static_loop_memory_result id labels info dst_addr src_addr abi_sz mem_sz n ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `((FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz
       (abi_static_loop_counter_addr id ss) labels) n
        (abi_static_loop_start_state id var_base labels ss)) with vs_vars := ss.vs_vars) =
    FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz
      (abi_static_loop_counter_addr id ss) labels) n (abi_static_loop_initial_memory id labels ss)` by
    (mp_tac (Q.SPECL [`n`, `info`, `dst_addr`, `src_addr`, `abi_sz`, `mem_sz`,
       `abi_static_loop_counter_addr id ss`, `labels`, `ss.vs_vars`,
       `abi_static_loop_start_state id var_base labels ss`] abi_static_loop_funpow_reset_vars) >>
     simp[abi_static_loop_start_reset_vars]) >>
  simp_tac (srw_ss()) [abi_static_loop_memory_result_def] >>
  irule control_cut_snapshot >> goal_assum drule >> goal_assum drule
QED

Theorem abi_static_loop_initialized_mload:
  !offset id var_base labels info dst_addr src_addr abi_sz mem_sz n ss.
    mload offset
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz
        (abi_static_loop_counter_addr id ss) labels) n
          (abi_static_loop_start_state id var_base labels ss)) =
    mload offset (abi_static_loop_memory_result id labels info dst_addr src_addr abi_sz mem_sz n ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`n`, `info`, `dst_addr`, `src_addr`, `abi_sz`, `mem_sz`,
    `abi_static_loop_counter_addr id ss`, `labels`, `ss.vs_vars`,
    `abi_static_loop_start_state id var_base labels ss`] abi_static_loop_funpow_reset_vars) >>
  disch_then (mp_tac o AP_TERM ``mload offset``) >>
  simp[abi_static_loop_start_reset_vars, abi_static_loop_memory_result_def,
    mload_def, jump_to_def]
QED

Theorem abi_static_loop_compiled_operand_frame:
  !id var_base labels info ss out.
    (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_tail_names var_base info) ==>
      eval_operand arg_op out =
        eval_operand arg_op (abi_static_loop_start_state id var_base labels ss)) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_names var_base info) ==>
      eval_operand arg_op out = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> simp[abi_static_loop_names_def] >> strip_tac >>
  qpat_x_assum `!arg_op. _` (qspec_then `arg_op` mp_tac) >>
  simp[abi_static_loop_start_operand_frame]
QED

Theorem compile_abi_encode_dyn_static_loop_path:
  !ctx func dst src info abi_sz mem_sz len_op cs op cs' ss dst_addr src_addr n.
    compile_abi_encode_dyn_static_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand len_op ss = SOME (n2w n) /\ n < dimword(:256) /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_names cs.cs_next_var info) ==>
    ?out. fragment_path ctx func ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) out = n2w n /\
      eval_operand op out = SOME (32w + mload (w2n src_addr)
        (abi_static_loop_memory_result cs.cs_next_id cs.cs_next_label info dst_addr src_addr abi_sz mem_sz n ss)
          * n2w abi_sz) /\
      out with vs_vars := ss.vs_vars =
        abi_static_loop_memory_result cs.cs_next_id cs.cs_next_label info dst_addr src_addr abi_sz mem_sz n ss /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_names cs.cs_next_var info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_abi_encode_dyn_static_loop_contains >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block cs.cs_current_bb _ = SOME entry_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) _ = SOME header_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1)) _ = SOME body_bb` >>
  rename1 `isPREFIX (abi_static_loop_exit _ _ _ _ _) exit_bb.bb_instructions` >>
  `fragment_path ctx func ss
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`,
       `ss`, `entry_bb`, `header_bb`] abi_static_loop_entry_path) >>
     simp[abi_static_loop_start_state_def, Abbr`entry_bb`, Abbr`header_bb`,
       abiStaticLoopCodePropsTheory.abi_static_loop_blocks_no_phi, DROP_LENGTH_APPEND]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`,
    `dst`, `src`, `info`, `abi_sz`, `mem_sz`, `len_op`,
    `abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss`,
    `dst_addr`, `src_addr`, `abi_static_loop_counter_addr cs.cs_next_id ss`, `n`,
    `header_bb`, `body_bb`, `exit_bb`] abi_static_loop_complete_path) >>
  impl_tac
  >- (fs[abi_static_loop_names_def, EVERY_CONJ] >>
      simp[abi_static_loop_start_counter, abi_static_loop_start_operand_frame,
        Abbr`header_bb`, Abbr`body_bb`]) >> strip_tac >>
  rename1 `fragment_path ctx func
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) out` >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `info`,
    `dst_addr`, `src_addr`, `abi_sz`, `mem_sz`, `n`, `ss`, `out`]
      abi_static_loop_initialized_snapshot) >> impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `info`, `ss`, `out`]
    abi_static_loop_compiled_operand_frame) >> impl_tac >- simp[] >> DISCH_TAC >>
  `mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) out = n2w n` by
    (qpat_x_assum `out with vs_vars := ss.vs_vars = _`
      (mp_tac o AP_TERM ``mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss))``) >>
     simp[mload_reset_vars_eq, abi_static_loop_memory_result_counter]) >>
  drule compile_abi_encode_dyn_static_loop_cut >> strip_tac >> fs[] >>
  qexists_tac `out` >> simp[abiStaticLoopExitTheory.abi_static_loop_exit_length,
    abi_static_loop_initialized_mload] >> irule fragment_path_trans >>
  qexists_tac `abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss` >> simp[]
QED

Theorem compile_abi_encode_dyn_static_loop_size:
  !ctx func dst src info copied_count mem_sz len_op cs op cs' ss dst_addr src_addr n.
    compile_abi_encode_dyn_static_loop dst src info copied_count mem_sz len_op cs = (op,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand len_op ss = SOME (n2w n) /\ n < dimword(:256) /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_names cs.cs_next_var info) /\
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\ mload (w2n src_addr) ss = n2w n /\
    (copied_count = 0 \/ w2n dst_addr + 32 + n * copied_count <= dimword(:256)) /\
    (copied_count = 0 \/ w2n src_addr + 32 <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * copied_count <= w2n src_addr) /\
    (w2n src_addr + 32 <= w2n (abi_static_loop_counter_addr cs.cs_next_id ss) \/
      w2n (abi_static_loop_counter_addr cs.cs_next_id ss) + 32 <= w2n src_addr) ==>
    ?out. fragment_path ctx func ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) out = n2w n /\
      eval_operand op out = SOME (32w + n2w n * n2w copied_count) /\
      out with vs_vars := ss.vs_vars =
        abi_static_loop_memory_result cs.cs_next_id cs.cs_next_label info dst_addr src_addr copied_count mem_sz n ss /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_names cs.cs_next_var info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `copied_count`, `mem_sz`,
    `len_op`, `cs`, `op`, `cs'`, `ss`, `dst_addr`, `src_addr`, `n`]
    compile_abi_encode_dyn_static_loop_path) >> impl_tac >- fs[] >> strip_tac >>
  rename1 `fragment_path ctx func ss out` >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_label`, `info`, `copied_count`,
    `dst_addr`, `src_addr`, `mem_sz`, `n`, `ss`, `w2n (src_addr:bytes32)`]
    abi_static_loop_memory_result_mload) >>
  impl_tac >- (gvs[] >> decide_tac) >> DISCH_TAC >>
  qexists_tac `out` >> fs[]
QED

Theorem compile_abi_encode_dyn_static_loop_payload:
  !ctx func dst src info elem_size len_op cs op cs' ss dst_addr src_addr n.
    compile_abi_encode_dyn_static_loop dst src info elem_size elem_size len_op cs = (op,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand len_op ss = SOME (n2w n) /\ n < dimword(:256) /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_names cs.cs_next_var info) /\
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n src_addr) ss = n2w n /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * elem_size <= w2n src_addr) /\
    (w2n src_addr + 32 + n * elem_size <= w2n (abi_static_loop_counter_addr cs.cs_next_id ss) \/
      w2n (abi_static_loop_counter_addr cs.cs_next_id ss) + 32 <= w2n src_addr) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= w2n (abi_static_loop_counter_addr cs.cs_next_id ss) \/
      w2n (abi_static_loop_counter_addr cs.cs_next_id ss) + 32 <= w2n dst_addr + 32) ==>
    ?out. fragment_path ctx func ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) out = n2w n /\
      eval_operand op out = SOME (32w + n2w n * n2w elem_size) /\
      read_memory (w2n dst_addr + 32) (n * elem_size) out =
        read_memory (w2n src_addr + 32) (n * elem_size) ss /\
      out with vs_vars := ss.vs_vars =
        abi_static_loop_memory_result cs.cs_next_id cs.cs_next_label info dst_addr src_addr elem_size elem_size n ss /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_names cs.cs_next_var info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `elem_size`, `elem_size`,
    `len_op`, `cs`, `op`, `cs'`, `ss`, `dst_addr`, `src_addr`, `n`]
    compile_abi_encode_dyn_static_loop_size) >>
  impl_tac >- (gvs[] >> decide_tac) >> strip_tac >>
  rename1 `fragment_path ctx func ss out` >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_label`, `info`, `elem_size`,
    `dst_addr`, `src_addr`, `n`, `ss`] abi_static_loop_memory_result_payload) >>
  impl_tac >- (gvs[] >> decide_tac) >> DISCH_TAC >>
  `read_memory (w2n dst_addr + 32) (n * elem_size) out =
    read_memory (w2n src_addr + 32) (n * elem_size) ss` by
    (qpat_x_assum `out with vs_vars := ss.vs_vars = _`
      (mp_tac o AP_TERM
        ``\state:venom_state. read_memory (w2n (dst_addr:bytes32) + 32) (n * elem_size) state``) >>
     simp[read_memory_def]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop compiler theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopExec")
