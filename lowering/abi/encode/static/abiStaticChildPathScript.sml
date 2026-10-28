(* TOP-LEVEL: close both primitive static-child branches of the real ABI
   dispatcher, including the destination ADD and complete memory/SSA frames. *)
Theory abiStaticChildPath
Ancestors
  abiAllocatorState
  abiStateFrame abiStaticChildCode abiStaticBytesPath abiStaticChildCompose abiStaticChildEmpty
  abiComplexCode abiFieldAddress abiStaticLoopCode abiBytestringCode abiMemoryFrame
  compileEnv fragExec fragBlockPath venomState list words arithmetic

Theorem compile_abi_child_copy_path:
  !ctx func dst src payload head_offset dyn_ptr cs op cs' ss dst_addr src_addr.
    compile_abi_encode_child dst src (AbiCopy (LENGTH payload)) F head_offset dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 0) /\
    LENGTH payload < dimword(:256) /\ read_memory (w2n src_addr) (LENGTH payload) ss = payload ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ eval_operand op out = SOME (n2w (LENGTH payload)) /\
      read_memory (w2n (dst_addr + n2w head_offset)) (LENGTH payload) out = payload /\
      abi_memory_frame [(w2n (dst_addr + n2w head_offset),LENGTH payload)] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 1) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_child_static_contains >> strip_tac >>
  `compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 0)) src (AbiCopy (LENGTH payload))
    (abi_complex_field_cut dst head_offset cs) = (op,cs')` by fs[compile_abi_child_static_cuts] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `head_offset`, `cs`, `ss`, `dst_addr`] abi_field_address_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qabbrev_tac `addressed = abi_field_address_state cs head_offset dst_addr ss` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 0)`, `src`, `payload`,
    `abi_complex_field_cut dst head_offset cs`, `op`, `cs'`, `addressed`, `dst_addr + n2w head_offset`, `src_addr`]
    compile_abi_copy_bytes_path) >>
  impl_tac >- fs[Abbr`addressed`, abi_field_address_state_frame, abi_field_address_state_value,
    abi_field_address_state_operand, abi_field_address_memory, abi_complex_field_cut_def] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `head_offset`, `dst_addr`, `ss`, `out`, `0`,
    `[(w2n (dst_addr + n2w head_offset:bytes32),LENGTH (payload:word8 list))]`] abi_static_child_compose) >>
  impl_tac >- fs[Abbr`addressed`] >> strip_tac >>
  qexists_tac `out` >> fs[Abbr`addressed`, abi_field_address_state_frame]
QED

Theorem compile_abi_child_word_path:
  !ctx func dst src payload head_offset dyn_ptr cs op cs' ss dst_addr src_addr.
    compile_abi_encode_child dst src AbiPrimWord F head_offset dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 0) /\
    LENGTH payload = 32 /\ read_memory (w2n src_addr) 32 ss = payload ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ eval_operand op out = SOME (n2w (LENGTH payload)) /\
      read_memory (w2n (dst_addr + n2w head_offset)) (LENGTH payload) out = payload /\
      abi_memory_frame [(w2n (dst_addr + n2w head_offset),LENGTH payload)] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 2) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_child_static_contains >> strip_tac >>
  `compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 0)) src AbiPrimWord
    (abi_complex_field_cut dst head_offset cs) = (op,cs')` by fs[compile_abi_child_static_cuts] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `head_offset`, `cs`, `ss`, `dst_addr`] abi_field_address_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qabbrev_tac `addressed = abi_field_address_state cs head_offset dst_addr ss` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 0)`, `src`, `payload`,
    `abi_complex_field_cut dst head_offset cs`, `op`, `cs'`, `addressed`, `dst_addr + n2w head_offset`, `src_addr`]
    compile_abi_word_bytes_path) >>
  impl_tac >- fs[Abbr`addressed`, abi_field_address_state_frame, abi_field_address_state_value,
    abi_field_address_state_operand, abi_field_address_memory, abi_complex_field_cut_def, compiler_var_name_def] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 1) 1) ==>
    eval_operand arg_op out = eval_operand arg_op addressed` by
    (qx_gen_tac `arg_op` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. arg_op <> Var _ ==> _` (qspec_then `arg_op` mp_tac) >>
     fs[compiler_var_names_def, GENLIST, abi_complex_field_cut_def, compiler_var_name_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `head_offset`, `dst_addr`, `ss`, `out`, `1`,
    `[(w2n (dst_addr + n2w head_offset:bytes32),LENGTH (payload:word8 list))]`] abi_static_child_compose) >>
  impl_tac >- fs[Abbr`addressed`] >> strip_tac >>
  qexists_tac `out` >> fs[Abbr`addressed`, abi_field_address_state_frame]
QED

Theorem compile_abi_child_static_bytes_path:
  !ctx func dst src info payload head_offset dyn_ptr cs op cs' ss dst_addr src_addr.
    ((info = AbiPrimWord /\ LENGTH payload = 32) \/ info = AbiCopy (LENGTH payload) \/
      (info = AbiComplex [] /\ LENGTH payload = 0)) /\
    compile_abi_encode_child dst src info F head_offset dyn_ptr cs = (op,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 0) /\
    LENGTH payload < dimword(:256) /\ read_memory (w2n src_addr) (LENGTH payload) ss = payload ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ eval_operand op out = SOME (n2w (LENGTH payload)) /\
      read_memory (w2n (dst_addr + n2w head_offset)) (LENGTH payload) out = payload /\
      abi_memory_frame [(w2n (dst_addr + n2w head_offset),LENGTH payload)] ss out /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (if info = AbiPrimWord then 2 else 1)) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `info = AbiPrimWord`
  >- (qpat_x_assum `info = AbiPrimWord` SUBST_ALL_TAC >> fs[] >>
      `read_memory (w2n (src_addr:bytes32)) 32 ss = payload` by
        (qpat_x_assum `read_memory _ _ ss = payload` mp_tac >> simp[]) >>
      mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `payload`, `head_offset`, `dyn_ptr`,
        `cs`, `op`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_abi_child_word_path) >>
      impl_tac >- fs[] >> simp[]) >>
  Cases_on `info = AbiComplex []`
  >- (qpat_x_assum `info = AbiComplex []` SUBST_ALL_TAC >> gvs[] >>
      mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `head_offset`, `dyn_ptr`,
        `cs`, `op`, `cs'`, `ss`, `dst_addr`] compile_abi_child_empty_path) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  fs[] >> qpat_x_assum `info = AbiCopy (LENGTH payload)` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `payload`, `head_offset`, `dyn_ptr`,
    `cs`, `op`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_abi_child_copy_path) >>
  impl_tac >- fs[] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual word/copy static ABI child execution: " ^ name)
  end) (DB.thms "abiStaticChildPath")
