(* TOP-LEVEL: actual array setup reserves its parent pointer and saved
   length before either generated loop. Old source/output operands retain
   their values, and the runtime boundary matches the compiler entry cut. *)
Theory abiNativeArrayEntryOperands
Ancestors
  abiNativeArrayParentState abiDynArrayCode abiDynArrayBoundaryFrames abiFieldOperands abiStaticLoopCode
  compileEnv venomState venomInst list words arithmetic

Definition abi_native_array_counter_inst_def:
  abi_native_array_counter_inst cs = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0]
End

Theorem abi_native_array_counter_inst_id[simp]:
  !cs. (abi_native_array_counter_inst cs).inst_id = cs.cs_next_id
Proof
  simp[abi_native_array_counter_inst_def, mk_inst_def]
QED

Theorem abi_native_array_operands_before:
  !var_base next_var dst src.
    abi_operand_before var_base dst /\ abi_operand_before var_base src /\ var_base + 2 <= next_var ==>
    EVERY (abi_operand_before next_var)
      [dst; src; Var (compiler_var_name var_base 0); Var (compiler_var_name var_base 1)]
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [] >> rpt conj_tac
  >- (irule abi_operand_before_mono >> qexists_tac `var_base` >> simp[] >> decide_tac)
  >- (irule abi_operand_before_mono >> qexists_tac `var_base` >> simp[] >> decide_tac)
  >- (irule abi_operand_before_reserved >> decide_tac) >>
  `Var (compiler_var_name var_base 1) = Var (compiler_var_name (var_base + 1) 0)` by simp[compiler_var_name_def] >>
  pop_assum SUBST1_TAC >> irule abi_operand_before_reserved >> decide_tac
QED

Theorem abi_native_array_parent_control:
  !cs dst src dst_addr root_addr ss.
    ss.vs_current_bb = cs.cs_current_bb /\ ~ss.vs_halted ==>
    (abi_dynarray_entry_boundary cs dst_addr root_addr ss).vs_current_bb =
      (abi_dynarray_entry_cut dst src cs).cs_current_bb /\
    (abi_dynarray_entry_boundary cs dst_addr root_addr ss).vs_inst_idx =
      LENGTH (abi_dynarray_entry_cut dst src cs).cs_current_insts /\
    ~(abi_dynarray_entry_boundary cs dst_addr root_addr ss).vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `ss`] strip_assume_tac abi_dynarray_entry_boundary_frame >>
  asm_simp_tac (srw_ss()) [abi_dynarray_entry_cut_def, abi_dynarray_entry_insts_def]
QED

Theorem abi_native_array_parent_operands:
  !cs dst src dst_addr root_addr ss.
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr ==>
    eval_operand dst (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = SOME dst_addr /\
    eval_operand src (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = SOME root_addr
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_native_array_parent_old_operand]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual array setup operands and control: " ^ name)
  end) (DB.thms "abiNativeArrayEntryOperands")
