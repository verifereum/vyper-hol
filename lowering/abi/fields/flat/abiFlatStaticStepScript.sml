(* TOP-LEVEL: a concrete static field advances an arbitrary traversal while
   preserving all remaining sources in the common output/scratch frame. *)
Theory abiFlatStaticStep
Ancestors
  abiAllocatorState
  abiStateFrame
  abiFlatFieldsDefs abiFlatSourcesFrame abiFlatGeometry abiStaticFieldStep
  abiFieldOperands abiFieldMemory abiFieldLayoutDefs abiMemoryFrame abiMemoryFrameCover
  abiStaticLoopCode compileEnv fragExec fragBlockPath venomState list pair words arithmetic

Theorem compile_abi_flat_static_step:
  !ctx func dst src dyn_ptr info mem_size payload rest source_offset fields tail_offset capacity
      cs ret cs' ss dst_addr dyn_addr root_addr.
    abi_flat_valid (AbiFlatStatic info mem_size payload) /\
    compile_abi_encode_complex_elems dst src (MAP abi_flat_entry (AbiFlatStatic info mem_size payload::rest))
      source_offset (abi_field_head_size fields) dyn_ptr cs = (ret,cs') /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_flat_state fields (AbiFlatStatic info mem_size payload::rest) tail_offset dst_addr dyn_addr
      root_addr source_offset capacity ss ==>
    ?mid out.
      compile_abi_encode_complex_elems dst src (MAP abi_flat_entry rest) (source_offset + mem_size)
        (abi_field_head_size (fields ++ [(F,payload)])) dyn_ptr mid = (ret,cs') /\ fn_has_code mid cs' func /\
      cs.cs_next_var <= mid.cs_next_var /\ fragment_path ctx func ss out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
      eval_operand dst out = SOME dst_addr /\ eval_operand src out = SOME root_addr /\ eval_operand dyn_ptr out = SOME dyn_addr /\
      abi_flat_state (fields ++ [(F,payload)]) rest tail_offset dst_addr dyn_addr root_addr
        (source_offset + mem_size) capacity out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_flat_state _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_flat_state_def, abi_flat_sources_def]) >>
  `abi_static_field_pre fields tail_offset dst_addr dyn_addr (root_addr + n2w source_offset) payload ss` by
    (fs[abi_flat_source_def] >> drule_all abi_flat_static_pre >> simp[]) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`, `src`, `dst`, `dyn_ptr`,
    `(if info = AbiPrimWord then 2 else 1) + 1`] abi_field_operands_names) >> impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `payload`, `dyn_ptr`, `mem_size`,
    `MAP abi_flat_entry rest`, `source_offset`, `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `dyn_addr`, `root_addr`,
    `fields`, `tail_offset`] compile_abi_static_field_step) >>
  impl_tac >- gvs[abi_flat_valid_def, abi_flat_entry_def] >>
  disch_then (qx_choose_then `mid` (qx_choose_then `out` strip_assume_tac)) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`, `(if info = AbiPrimWord then 2 else 1) + 1`, `ss`, `out`]
    abi_operand_before_frame) >> impl_tac >- simp[] >> DISCH_TAC >>
  `abi_writes_cover [(w2n dst_addr,capacity);(w2n dyn_addr,32)]
      [(w2n (dst_addr + n2w (abi_field_head_size fields)),LENGTH payload)]` by
    (drule_all abi_flat_static_cover >> simp[]) >>
  `abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out` by
    (irule abi_memory_frame_cover >>
     qexists_tac `[(w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),LENGTH (payload:word8 list))]` >> simp[]) >>
  `abi_flat_geometry (fields ++ [(F,payload)]) rest tail_offset dst_addr dyn_addr capacity` by
    (drule abi_flat_geometry_advance >> simp[abi_flat_output_def]) >>
  drule_all abi_flat_sources_frame >> DISCH_TAC >>
  `cs.cs_next_var <= mid.cs_next_var` by decide_tac >>
  qexistsl_tac [`mid`, `out`] >>
  gvs[abi_flat_state_def, abi_flat_mem_size_def, abi_flat_output_def, abi_field_head_size_append,
    abi_field_head_size_def, abi_field_tail_size_append, abi_field_tail_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed concrete static field step with remaining source preservation: " ^ name)
  end) (DB.thms "abiFlatStaticStep")
