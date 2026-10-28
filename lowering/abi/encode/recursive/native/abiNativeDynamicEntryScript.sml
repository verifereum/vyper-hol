(* TOP-LEVEL: the actual dynamic-child prefix prepares the recursive
   assertion's operands and allocation resources. Source memory is unchanged;
   budgets include cached scratch identities from previous loop iterations. *)
Theory abiNativeDynamicEntry
Ancestors
  abiNativeEncodingDefs abiNativeResources abiMemoryChildEntry abiChildCode abiChildStructure
  abiFieldOperands abiChildFlatCode abiAllocationTrace abiAllocatorState
  compileAllocaProvenance compileIdFlow compileEnv venomState venomInst list words arithmetic

Theorem abi_child_prefix_id_history:
  !dst dyn_ptr head_offset cs.
    compiler_id_history cs ==> compiler_id_history (abi_child_prefix_cut dst dyn_ptr head_offset cs)
Proof
  rw[compiler_id_history_def, abi_child_prefix_cut_def, abi_child_prefix_insts_def,
    EVERY_APPEND, EVERY_MEM, mk_inst_def] >> res_tac >> simp[] >> decide_tac
QED

Theorem abi_native_dynamic_entry_ready:
  !func cs after source_id target_id src_addr span encoded_addr payload ss mid
      dst dyn_ptr head_offset dst_addr dyn_addr.
    abi_native_memory_ready func cs after source_id target_id src_addr span encoded_addr payload ss /\
    cs_extends mid after ==>
    abi_native_memory_ready func (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid
      source_id target_id src_addr span encoded_addr payload
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  `compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  `compiler_id_history (abi_child_prefix_cut dst dyn_ptr head_offset cs)` by
    (irule abi_child_prefix_id_history >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss
    (abi_child_entry_state cs head_offset dst_addr dyn_addr ss)` by
    (irule abi_allocation_trace_identity >> simp[abi_child_entry_frame]) >>
  qspecl_then [`func`, `cs`, `after`, `source_id`, `target_id`, `src_addr`, `span`,
    `encoded_addr`, `payload`, `ss`, `abi_child_prefix_cut dst dyn_ptr head_offset cs`, `mid`,
    `abi_child_entry_state cs head_offset dst_addr dyn_addr ss`, `src_addr`, `span`,
    `encoded_addr`, `payload`] mp_tac abi_native_child_ready >>
  simp[abi_child_prefix_extends]
QED

Theorem abi_native_dynamic_entry_inputs:
  !cs head_offset dst_addr dyn_addr ss src src_addr.
    abi_operand_before cs.cs_next_var src /\ eval_operand src ss = SOME src_addr ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var 2))
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) =
        SOME (dst_addr + mload (w2n dyn_addr) ss) /\
    eval_operand src (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) = SOME src_addr /\
    abi_operand_before (cs.cs_next_var + 3) (Var (compiler_var_name cs.cs_next_var 2)) /\
    abi_operand_before (cs.cs_next_var + 3) src
Proof
  rpt gen_tac >> strip_tac >>
  simp[abi_child_entry_values, abi_child_entry_operand, abi_operand_before_generated] >>
  irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native dynamic recursive child entry: " ^ name)
  end) (DB.thms "abiNativeDynamicEntry")
