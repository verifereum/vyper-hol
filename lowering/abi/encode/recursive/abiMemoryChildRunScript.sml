(* TOP-LEVEL: compose an arbitrary recursive native encoder with the actual
   dynamic-child wrapper. The complete result retains all child scratch
   writes, the parent's head/counter stores, and earlier SSA operands.
   This is the child-composition step used by recursive execution induction. *)
Theory abiMemoryChildRun
Ancestors
  abiMemoryChildEntry abiMemoryLeafRun abiResultFlow
  abiChildRun abiChildStructure abiChildCode abiChildPrefix abiChildFlatCode abiChildFlatFrames
  abiFieldOperands abiStateFrame abiAllocatorState abiMemoryFrame
  abiEncodeVarFlow abiStaticLoopCode fragBlockPath compileEnv venomState list words arithmetic

Theorem abi_child_memory_operand_frame:
  !ctx func cs dst dyn_ptr head_offset mid ret dst_addr dyn_addr payload scratch ss child_out out.
    abi_encoding_result ctx func (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid ret
      (dst_addr + mload (w2n dyn_addr) ss) payload scratch
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) child_out /\
    cs.cs_next_var <= mid.cs_next_var /\
    (!arg_op. arg_op <> Var (compiler_var_name mid.cs_next_var 0) ==>
      eval_operand arg_op out = eval_operand arg_op child_out) ==>
    !arg_op. abi_operand_before cs.cs_next_var arg_op ==>
      eval_operand arg_op out = eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >> drule abi_child_entry_result_frame >> DISCH_TAC >>
  qspecl_then [`cs.cs_next_var`, `mid.cs_next_var`, `head_offset`, `dst_addr`, `dyn_addr`,
    `ss`, `LENGTH cs.cs_current_insts + 3`, `child_out`, `out`]
    mp_tac abi_child_flat_operand_frame >>
  impl_tac >- fs[abi_child_entry_state_def] >> simp[]
QED

Theorem abi_child_memory_written_frame:
  !cs head_offset dst_addr dyn_addr writes suffix ss child_out out.
    abi_memory_frame writes (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) child_out /\
    abi_memory_frame suffix child_out out ==>
    abi_memory_frame (writes ++ suffix) ss out
Proof
  rpt gen_tac >> strip_tac >>
  `abi_memory_frame writes ss child_out` by
    (qpat_x_assum `abi_memory_frame writes _ child_out` mp_tac >>
     simp[abi_memory_frame_def, read_memory_def, abi_child_entry_frame]) >>
  irule abi_memory_frame_trans >> qexists_tac `child_out` >> simp[]
QED

Theorem abi_memory_dynamic_child_run:
  !ctx func dst src info dyn_ptr head_offset cs ret mid ss dst_addr dyn_addr payload scratch child_out.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src info
      (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (ret,mid) /\
    fn_has_code cs (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr ret mid) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_encoding_result ctx func (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid ret
      (dst_addr + mload (w2n dyn_addr) ss) payload scratch
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) child_out /\
    regions_disjoint (w2n (dst_addr + n2w head_offset)) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload)
      (w2n (dst_addr + n2w head_offset)) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss)) (LENGTH payload) (w2n dyn_addr) 32 ==>
    ?out.
      abi_encoding_result ctx func cs
        (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
          (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr ret mid) ret
        (dst_addr + mload (w2n dyn_addr) ss) payload
        (scratch ++ [(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]) ss out /\
      mload (w2n (dst_addr + n2w head_offset)) out = mload (w2n dyn_addr) ss /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH payload) /\
      abi_allocator_state out = abi_allocator_state child_out
Proof
  rpt gen_tac >> strip_tac >>
  `cs.cs_next_var <= mid.cs_next_var` by
    (drule compile_abi_encode_next_var >> simp[abi_child_prefix_cut_def] >> decide_tac) >>
  `abi_operand_before mid.cs_next_var ret` by (drule compile_abi_encode_result_before >> simp[]) >>
  `ret <> Var (compiler_var_name mid.cs_next_var 0)` by
    (irule abi_operand_before_self >> simp[]) >>
  `dyn_ptr <> Var (compiler_var_name mid.cs_next_var 0)` by
    (irule abi_operand_before_self >> irule abi_operand_before_mono >>
     qexists_tac `cs.cs_next_var` >> simp[]) >>
  `EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name) (compiler_var_names cs.cs_next_var 3)` by
    (simp[EVERY_CONJ] >> conj_tac >> irule abi_operand_before_names >>
     qexists_tac `cs.cs_next_var` >> simp[]) >>
  drule_all abi_child_entry_result_values >> strip_tac >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `~child_out.vs_halted` by
    (drule_all abi_state_frame_observables >> simp[abi_child_entry_frame]) >>
  `abi_state_frame ss child_out` by
    (irule abi_state_frame_trans >>
     qexists_tac `abi_child_entry_state cs head_offset dst_addr dyn_addr ss` >> simp[abi_child_entry_frame]) >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `dyn_ptr`, `head_offset`, `cs`, `ret`, `mid`,
    `ss`, `dst_addr`, `dyn_addr`, `child_out`, `payload`] mp_tac abi_child_dynamic_path >>
  impl_tac >- fs[GSYM abi_child_entry_cut] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `eval_operand ret out = SOME (n2w (LENGTH payload))` by
    (qpat_x_assum `!arg_op. arg_op <> Var _ ==> _` (qspec_then `ret` mp_tac) >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cs`, `dst`, `dyn_ptr`, `head_offset`, `mid`, `ret`,
    `dst_addr`, `dyn_addr`, `payload`, `scratch`, `ss`, `child_out`, `out`]
    mp_tac abi_child_memory_operand_frame >> impl_tac >- simp[] >> DISCH_TAC >>
  qspecl_then [`cs`, `head_offset`, `dst_addr`, `dyn_addr`,
    `(w2n (dst_addr + mload (w2n dyn_addr) ss),LENGTH payload)::scratch`,
    `[(w2n (dst_addr + n2w head_offset),32);(w2n dyn_addr,32)]`, `ss`, `child_out`, `out`]
    mp_tac abi_child_memory_written_frame >> impl_tac >- simp[] >> DISCH_TAC >>
  qexists_tac `out` >> fs[abi_encoding_result_def, abi_child_suffix_cut_def, abi_child_suffix_insts_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive ABI child execution composition: " ^ name)
  end) (DB.thms "abiMemoryChildRun")
