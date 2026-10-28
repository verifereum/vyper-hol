(* TOP-LEVEL: the actual generated loop reaches its runtime array count
   from semantic recursive-child assertions. All source/output data,
   traversal resources and real cursors are retained at the final header. *)
Theory abiNativeDynamicArrayRepeat
Ancestors
  abiNativeDynamicArrayContract abiNativeDynamicArrayInvariant abiNativeDynamicArrayState abiNativeFields
  abiNativeEncodingDefs abiDynamicLoopRun abiDynamicLoopCode abiFieldOperands abiStaticLoopCode abiBytestringCode abiFieldLayoutDefs
  abiAllocatedWindows compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_repeat:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op ret mid child_len counter_addr dyn_addr dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
      info width stride fields source_capacity initial dyn_inst index_inst 0 initial /\
    abi_allocated_window initial target_id (w2n dst_addr) 32 /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    dyn_inst.inst_id <> index_inst.inst_id /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ LENGTH fields < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    ?boundary. fragment_path ctx func initial boundary /\
      abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
        info width stride fields source_capacity initial dyn_inst index_inst (LENGTH fields) boundary
Proof
  rpt gen_tac >> strip_tac >>
  `abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity 0 initial` by
    fs[abi_native_dynamic_array_invariant_def] >>
  drule_all abi_native_dynamic_array_child_contract >> disch_then (qspec_then `ctx` ASSUME_TAC) >>
  `len_op <> Var (compiler_var_name cs.cs_next_var 3)` by
    (qspecl_then [`cs.cs_next_var + 3`, `len_op`, `cs.cs_next_var + 3`, `1`] mp_tac abi_operand_before_names >>
     impl_tac >- simp[] >> simp[compiler_var_names_def, GENLIST, compiler_var_name_def]) >>
  `EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12)` by
    (simp_tac bool_ss [EVERY_CONJ] >> conj_tac >> irule abi_operand_before_names >>
     qexists_tac `cs.cs_next_var + 3` >> simp[]) >>
  `!index ss. abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
    info width stride fields source_capacity initial dyn_inst index_inst index ss ==>
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr (LENGTH fields) index ss` by
    (simp[abi_native_dynamic_array_invariant_def]) >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `child_len`, `mid`,
    `dst_addr`, `root_addr`, `counter_addr`, `dyn_addr`, `LENGTH fields`,
    `abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
      info width stride fields source_capacity initial dyn_inst index_inst`] mp_tac abi_dynamic_loop_repeat >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (qspecl_then [`LENGTH fields`, `0`, `initial`] mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array repetition from recursive semantic assertions: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayRepeat")
