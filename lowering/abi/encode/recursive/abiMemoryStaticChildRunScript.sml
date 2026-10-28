(* TOP-LEVEL: the actual static child ADD composes with arbitrary recursive
   encoder execution. Nested child scratch writes and old operands are kept.
   Helpers pull back the child's memory and operand frames through the ADD. *)
Theory abiMemoryStaticChildRun
Ancestors
  abiMemoryLeafRun abiStaticChildCode abiFieldAddress abiFieldOperands abiChildFlatCode
  abiStateFrameOps abiStateFrame abiMemoryFrame abiComplexCode
  fragBlockPath compileEnv venomState list words arithmetic

Theorem abi_field_address_written_frame:
  !cs head_offset dst_addr ss out writes.
    abi_memory_frame writes (abi_field_address_state cs head_offset dst_addr ss) out ==>
    abi_memory_frame writes ss out
Proof
  simp[abi_memory_frame_def, read_memory_def, abi_field_address_state_frame]
QED

Theorem abi_field_address_operand_frame:
  !cs head_offset dst_addr ss out.
    (!arg_op. abi_operand_before (cs.cs_next_var + 1) arg_op ==>
      eval_operand arg_op out = eval_operand arg_op (abi_field_address_state cs head_offset dst_addr ss)) ==>
    !arg_op. abi_operand_before cs.cs_next_var arg_op ==>
      eval_operand arg_op out = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  `abi_operand_before (cs.cs_next_var + 1) arg_op` by
    (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  `arg_op <> Var (compiler_var_name cs.cs_next_var 0)` by
    (irule abi_operand_before_self >> simp[]) >>
  qpat_x_assum `!arg_op. _` (qspec_then `arg_op` mp_tac) >>
  simp[abi_field_address_state_operand]
QED

Theorem abi_memory_address_run:
  !ctx func base_op offset cs cs' ss base_addr ret dst_addr payload scratch out.
    fn_has_code cs (abi_complex_field_cut base_op offset cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand base_op ss = SOME base_addr /\
    abi_encoding_result ctx func (abi_complex_field_cut base_op offset cs) cs' ret dst_addr payload scratch
      (abi_field_address_state cs offset base_addr ss) out ==>
    abi_encoding_result ctx func cs cs' ret dst_addr payload scratch ss out
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ctx`, `func`, `base_op`, `offset`, `cs`, `ss`, `base_addr`]
    mp_tac abi_field_address_path >> impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `abi_field_address_state cs offset base_addr ss` >> simp[]) >>
  drule abi_field_address_written_frame >> DISCH_TAC >>
  qspecl_then [`cs`, `offset`, `base_addr`, `ss`, `out`]
    mp_tac abi_field_address_operand_frame >>
  impl_tac >- fs[abi_complex_field_cut_def] >> DISCH_TAC >>
  `abi_state_frame ss out` by
    (irule abi_state_frame_trans >> qexists_tac `abi_field_address_state cs offset base_addr ss` >>
     simp[abi_state_frame_def]) >>
  simp[abi_encoding_result_def]
QED

Theorem abi_memory_static_child_run:
  !ctx func dst src info head_offset dyn_ptr cs ret cs' ss dst_addr payload scratch out.
    compile_abi_encode_child dst src info F head_offset dyn_ptr cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\
    abi_encoding_result ctx func (abi_complex_field_cut dst head_offset cs) cs' ret
      (dst_addr + n2w head_offset) payload scratch
      (abi_field_address_state cs head_offset dst_addr ss) out ==>
    abi_encoding_result ctx func cs cs' ret (dst_addr + n2w head_offset) payload scratch ss out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_child_static_contains >> strip_tac >>
  qspecl_then [`ctx`, `func`, `dst`, `head_offset`, `cs`, `cs'`, `ss`, `dst_addr`, `ret`,
    `dst_addr + n2w head_offset`, `payload`, `scratch`, `out`] mp_tac abi_memory_address_run >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive static ABI child execution: " ^ name)
  end) (DB.thms "abiMemoryStaticChildRun")
