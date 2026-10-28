(* TOP-LEVEL: the actual dynamic-child loop repeats a recursive child
   contract for the requested number of elements. The caller assertion carries payloads,
   source snapshots and scratch resources across each iteration. *)
Theory abiDynamicLoopRun
Ancestors
  abiDynamicLoopIteration abiDynamicLoopStep abiDynamicLoopFinish abiDynamicLoopUpdate
  abiDynamicLoopCode abiDynamicLoopFactor abiChildCode abiStaticLoopCode compileEnv fragExec fragBlockPath
  venomState venomExecSemantics list words arithmetic

Definition abi_dynamic_loop_ready_def:
  abi_dynamic_loop_ready cs dst src len_op dst_addr src_addr counter_addr dyn_addr loop_count index ss <=>
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) ss = SOME dyn_addr /\
    eval_operand len_op ss = SOME (n2w loop_count) /\ mload (w2n counter_addr) ss = n2w index
End

Definition abi_dynamic_loop_child_contract_def:
  abi_dynamic_loop_child_contract ctx func cs dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr
      loop_count child_len mid P <=>
    !index ss. index < loop_count /\ P index ss ==>
      ?child_out child_size.
        fragment_path ctx func
          (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr src_addr abi_sz mem_sz
            counter_addr dyn_addr (n2w loop_count) ss) child_out /\
        abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr abi_sz counter_addr dyn_addr
          (n2w index) (mload (w2n dyn_addr) ss) child_size child_out /\
        P (index + 1)
          (jump_to (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
            (abi_dynamic_loop_update_state mid (dst_addr + 32w + n2w index * n2w abi_sz) dyn_addr counter_addr
              (n2w index) (mload (w2n dyn_addr) ss) child_size child_out))
End

Theorem abi_dynamic_loop_contract_step:
  !ctx func dst src info abi_sz mem_sz len_op cs op cs' child_len mid dst_addr src_addr
      counter_addr dyn_addr loop_count P index ss.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs cs' func /\ loop_count < dimword(:256) /\
    len_op <> Var (compiler_var_name cs.cs_next_var 3) /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12) /\
    (!i st. P i st ==> abi_dynamic_loop_ready cs dst src len_op dst_addr src_addr counter_addr dyn_addr loop_count i st) /\
    abi_dynamic_loop_child_contract ctx func cs dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr
      loop_count child_len mid P /\ index < loop_count /\ P index ss ==>
    ?next. fragment_path ctx func ss next /\ P (index + 1) next
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i st. P i st ==> _` (qspecl_then [`index`, `ss`] mp_tac) >>
  asm_simp_tac bool_ss [abi_dynamic_loop_ready_def] >> strip_tac >>
  qpat_x_assum `abi_dynamic_loop_child_contract _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [abi_dynamic_loop_child_contract_def]) >>
  disch_then (qspecl_then [`index`, `ss`] mp_tac) >> impl_tac >- simp[] >>
  disch_then (qx_choose_then `child_out` (qx_choose_then `child_size` strip_assume_tac)) >>
  qexists_tac `jump_to (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
    (abi_dynamic_loop_update_state mid (dst_addr + 32w + n2w index * n2w abi_sz) dyn_addr counter_addr
      (n2w index) (mload (w2n dyn_addr) ss) child_size child_out)` >>
  reverse conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `abi_sz`, `mem_sz`, `len_op`, `cs`, `op`, `cs'`,
    `child_len`, `mid`, `ss`, `child_out`, `dst_addr`, `src_addr`, `counter_addr`, `dyn_addr`,
    `n2w loop_count:bytes32`, `child_size`] abi_dynamic_loop_iteration_path) >>
  impl_tac >- (simp[] >> `index < dimword(:256)` by decide_tac >> simp[]) >> simp[]
QED

Theorem abi_dynamic_loop_repeat:
  !ctx func dst src info abi_sz mem_sz len_op cs op cs' child_len mid dst_addr src_addr
      counter_addr dyn_addr loop_count P.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs cs' func /\ loop_count < dimword(:256) /\
    len_op <> Var (compiler_var_name cs.cs_next_var 3) /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12) /\
    (!i st. P i st ==> abi_dynamic_loop_ready cs dst src len_op dst_addr src_addr counter_addr dyn_addr loop_count i st) /\
    abi_dynamic_loop_child_contract ctx func cs dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr
      loop_count child_len mid P ==>
    !remaining index ss. index + remaining = loop_count /\ P index ss ==>
      ?boundary. fragment_path ctx func ss boundary /\ P loop_count boundary
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`remaining`, `ctx`, `func`, `\i st. P (index + i) st`, `ss`] fragment_path_loop) >>
  impl_tac
  >- (simp_tac bool_ss [ADD_0] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      MAP_EVERY qx_gen_tac [`i`, `current`] >> strip_tac >>
      `index + i < loop_count` by decide_tac >>
      `index + SUC i = (index + i) + 1` by decide_tac >>
      asm_simp_tac bool_ss [] >>
      mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `abi_sz`, `mem_sz`, `len_op`, `cs`, `op`, `cs'`,
        `child_len`, `mid`, `dst_addr`, `src_addr`, `counter_addr`, `dyn_addr`, `loop_count`, `P`, `index + i`, `current`]
        abi_dynamic_loop_contract_step) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >> simp[]
QED

Theorem compile_abi_dynamic_loop_contract:
  !ctx func dst src info abi_sz mem_sz len_op cs op cs' child_len mid dst_addr src_addr
      counter_addr dyn_addr loop_count P ss.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs cs' func /\ loop_count < dimword(:256) /\
    len_op <> Var (compiler_var_name cs.cs_next_var 3) /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12) /\
    (!i st. P i st ==> abi_dynamic_loop_ready cs dst src len_op dst_addr src_addr counter_addr dyn_addr loop_count i st) /\
    abi_dynamic_loop_child_contract ctx func cs dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr
      loop_count child_len mid P /\ P 0 ss ==>
    ?boundary out.
      fragment_path ctx func ss out /\ P loop_count boundary /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_memory = boundary.vs_memory /\
      eval_operand op out = SOME (32w + mload (w2n dyn_addr) boundary)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `abi_sz`, `mem_sz`, `len_op`, `cs`, `op`, `cs'`,
    `child_len`, `mid`, `dst_addr`, `src_addr`, `counter_addr`, `dyn_addr`, `loop_count`, `P`]
    abi_dynamic_loop_repeat) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`loop_count`, `0`, `ss`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `boundary` strip_assume_tac) >>
  qpat_x_assum `!i st. P i st ==> _` (qspecl_then [`loop_count`, `boundary`] mp_tac) >>
  asm_simp_tac bool_ss [abi_dynamic_loop_ready_def] >> strip_tac >>
  drule_all abi_dynamic_loop_input_names >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `abi_sz`, `mem_sz`, `len_op`, `cs`, `op`, `cs'`,
    `child_len`, `mid`, `boundary`, `src_addr`, `counter_addr`, `dyn_addr`, `n2w loop_count:bytes32`]
    abi_dynamic_loop_finish_path) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  `op = Var (compiler_var_name (mid.cs_next_var + 2) 2) /\
   cs'.cs_current_bb = fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2) /\
   LENGTH cs'.cs_current_insts = 3` by
    gvs[compile_abi_dynamic_loop_factor, LET_THM, abi_dynamic_loop_exit_cut_def,
      abi_dynamic_loop_latch_cut_def, abi_child_suffix_cut_def] >>
  qexists_tac `boundary` >>
  qexists_tac `abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
    src_addr counter_addr dyn_addr (n2w loop_count) boundary` >>
  simp[SIMP_RULE bool_ss [LET_THM] abi_dynamic_loop_finish_values] >>
  irule fragment_path_trans >> qexists_tac `boundary` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic ABI loop repetition: " ^ name)
  end) (DB.thms "abiDynamicLoopRun")
