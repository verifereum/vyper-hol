(* TOP-LEVEL: compose a verified recursive child path with the real dynamic
   head/tail wrapper. The conclusion retains the child's exact state image
   apart from the wrapper's two word stores and one generated variable. *)
Theory abiChildRun
Ancestors
  abiAllocatorState
  abiStateFrameOps abiStateFrame abiChildCode abiChildPrefix abiChildSuffix abiChildFrames abiChildStructure abiChildMemoryFrame abiMemoryFrame
  abiStaticLoopCode abiEncoderPathProps instIdxIndep fragExec fragBlockPath memoryReadProps memoryValueAbiExec
  compileEnv venomState venomExecSemantics list words arithmetic

Theorem abi_child_dynamic_path:
  !ctx func dst src info dyn_ptr head_offset cs child_len mid ss dst_addr dyn_addr child_out encoded.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src info
      (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (child_len,mid) /\
    fn_has_code cs (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr child_len mid) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name) (compiler_var_names cs.cs_next_var 3) /\
    fragment_path ctx func
      ((abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
        vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts) child_out /\
    child_out.vs_current_bb = mid.cs_current_bb /\ child_out.vs_inst_idx = LENGTH mid.cs_current_insts /\
    ~child_out.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) child_out = SOME (dst_addr + n2w head_offset) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) child_out = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand dyn_ptr child_out = SOME dyn_addr /\
    eval_operand child_len child_out = SOME (n2w (LENGTH encoded)) /\
    dyn_ptr <> Var (compiler_var_name mid.cs_next_var 0) /\
    read_memory (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH encoded) child_out = encoded /\
    regions_disjoint (w2n (dst_addr + n2w head_offset)) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH encoded)
      (w2n (dst_addr + n2w head_offset)) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH encoded) (w2n dyn_addr) 32 ==>
    ?out.
      fragment_path ctx func ss out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts + 3 /\
      ~out.vs_halted /\
      mload (w2n (dst_addr + n2w head_offset)) out = mload (w2n dyn_addr) ss /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH encoded) /\
      read_memory (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH encoded) out = encoded /\
      abi_memory_frame [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)] child_out out /\
      (!arg_op. arg_op <> Var (compiler_var_name mid.cs_next_var 0) ==>
        eval_operand arg_op out = eval_operand arg_op child_out) /\
      out with vs_vars := child_out.vs_vars =
        (mstore (w2n dyn_addr) (mload (w2n dyn_addr) ss + n2w (LENGTH encoded))
          (mstore (w2n (dst_addr + n2w head_offset)) (mload (w2n dyn_addr) ss) child_out))
          with vs_inst_idx := LENGTH mid.cs_current_insts + 3 /\
      (abi_state_frame ss child_out ==> abi_state_frame ss out) /\
      abi_allocator_state out = abi_allocator_state child_out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_child_dynamic_contains >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `dyn_ptr`, `head_offset`, `cs`, `ss`, `dst_addr`, `dyn_addr`]
    abi_child_prefix_path) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 0)`,
    `Var (compiler_var_name cs.cs_next_var 1)`, `dyn_ptr`, `child_len`, `mid`, `child_out`,
    `dst_addr + n2w head_offset`, `dyn_addr`, `mload (w2n (dyn_addr:bytes32)) ss`, `n2w (LENGTH (encoded:word8 list))`]
    abi_child_suffix_path) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qabbrev_tac `final_state = (abi_child_suffix_state mid.cs_next_var (dst_addr + n2w head_offset)
    dyn_addr (mload (w2n dyn_addr) ss) (n2w (LENGTH encoded)) child_out) with
    vs_inst_idx := LENGTH (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr child_len mid).cs_current_insts` >>
  `fragment_path ctx func ss final_state` by
    (irule fragment_path_trans >>
     qexists_tac `(abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
       vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts` >>
     conj_tac
     >- (irule fragment_path_trans >> qexists_tac `child_out` >> asm_simp_tac bool_ss [Abbr`final_state`]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`mid.cs_next_var`, `dst_addr + n2w head_offset`, `dyn_addr`,
    `mload (w2n (dyn_addr:bytes32)) ss`, `n2w (LENGTH (encoded:word8 list))`, `child_out`] abi_child_suffix_words) >>
  impl_tac >- fs[regions_disjoint_def] >> strip_tac >>
  mp_tac (Q.SPECL [`mid.cs_next_var`, `dst_addr + n2w head_offset`, `dyn_addr`,
    `mload (w2n (dyn_addr:bytes32)) ss`, `n2w (LENGTH (encoded:word8 list))`, `child_out`,
    `w2n (dst_addr + mload (w2n (dyn_addr:bytes32)) ss)`, `LENGTH (encoded:word8 list)`] abi_child_suffix_read_frame) >>
  impl_tac >- fs[regions_disjoint_def] >> DISCH_TAC >>
  qexists_tac `final_state` >> asm_simp_tac (srw_ss()) [Abbr`final_state`, abi_child_suffix_control,
    abi_child_suffix_cut_def, abi_child_suffix_insts_def, mload_inst_idx, read_memory_inst_idx,
    abi_child_suffix_memory_image, abi_child_suffix_operand_frame, eval_op_inst_idx,
    abi_memory_frame_inst_idx, abi_child_suffix_written_frame, abi_state_frame_def] >>
  mp_tac (Q.SPECL [`mid.cs_next_var`, `dst_addr + n2w head_offset`, `dyn_addr`,
    `mload (w2n (dyn_addr:bytes32)) ss`, `n2w (LENGTH (encoded:word8 list))`, `child_out`]
    abi_child_suffix_memory_image) >>
  disch_then (mp_tac o AP_TERM ``\st:venom_state. st with vs_inst_idx := LENGTH mid.cs_current_insts + 3``) >>
  simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI child path composition: " ^ name)
  end) (DB.thms "abiChildRun")
