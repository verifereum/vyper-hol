(* TOP-LEVEL: actual static index setup retains the output/source pointers,
   parent pointer and saved array length created before its allocation. *)
Theory abiNativeStaticStartOperands
Ancestors
  abiNativeArrayEntryOperands abiNativeStaticStartState abiStaticLoopEntry abiStaticLoopCode abiFieldOperands
  compileEnv venomState list words arithmetic

Theorem abi_native_static_start_operands:
  !var_base cs dst src dst_addr root_addr parent_addr length_word ss.
    var_base + 2 <= cs.cs_next_var /\ abi_operand_before var_base dst /\ abi_operand_before var_base src /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME parent_addr /\
    eval_operand (Var (compiler_var_name var_base 1)) ss = SOME length_word ==>
    eval_operand dst (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) = SOME dst_addr /\
    eval_operand src (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) = SOME root_addr /\
    eval_operand (Var (compiler_var_name var_base 0))
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) = SOME parent_addr /\
    eval_operand (Var (compiler_var_name var_base 1))
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) = SOME length_word /\
    EVERY (abi_operand_before (cs.cs_next_var + 1))
      [dst; src; Var (compiler_var_name var_base 0); Var (compiler_var_name var_base 1)]
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`var_base`, `cs.cs_next_var`, `dst`, `src`] mp_tac abi_native_array_operands_before >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac (srw_ss()) [] >> strip_tac >>
  `EVERY (abi_operand_before (cs.cs_next_var + 1))
    [dst; src; Var (compiler_var_name var_base 0); Var (compiler_var_name var_base 1)]` by
    (irule abi_native_array_operands_before >> simp[] >> decide_tac) >>
  asm_simp_tac (srw_ss()) [abi_native_static_start_old_operand] >> fs[EVERY_DEF]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static index setup operand values: " ^ name)
  end) (DB.thms "abiNativeStaticStartOperands")
