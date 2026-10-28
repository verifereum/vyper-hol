(* TOP-LEVEL: the aggregate child's returned length is an earlier SSA name
   than the following wrapper suffix. Caller names remain outside that suffix. *)
Theory abiChildFlatCode
Ancestors
  abiFlatComplexCode abiFlatFieldsDefs abiFieldOperands abiChildCode abiEncodeVarFlow
  abiStaticLoopCode emitHelperProps compileEnv venomState list words arithmetic

Theorem abi_operand_before_self:
  !var_base arg_op.
    abi_operand_before var_base arg_op ==> arg_op <> Var (compiler_var_name var_base 0)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_operand_before_def] >> DISCH_TAC >>
  first_x_assum (qspec_then `var_base` mp_tac) >> simp[]
QED

Theorem abi_flat_complex_result_before:
  !rows dst src cs op cs'.
    EXISTS (\row. FST (abi_flat_output row)) rows /\
    compile_abi_encode_to_buf dst src (AbiComplex (MAP abi_flat_entry rows)) cs = (op,cs') ==>
    abi_operand_before cs'.cs_next_var op
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`rows`, `dst`, `src`, `cs`, `op`, `cs'`] compile_abi_flat_complex_split) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `ret` (qx_choose_then `mid` strip_assume_tac)) >>
  drule emitted_insts_emit_op >> strip_tac >>
  mp_tac (Q.SPECL [`mid.cs_next_var`, `cs'.cs_next_var`] abi_operand_before_reserved) >>
  impl_tac >- simp[] >> fs[compiler_var_name_def]
QED

Theorem abi_child_flat_suffix_bound:
  !rows dst src dyn_ptr head_offset cs op mid.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src
      (AbiComplex (MAP abi_flat_entry rows)) (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (op,mid) ==>
    cs.cs_next_var <= mid.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >> drule compile_abi_encode_next_var >>
  simp[abi_child_prefix_cut_def] >> decide_tac
QED

Theorem abi_operand_before_generated:
  !var_base index next_var.
    var_base + index < next_var ==> abi_operand_before next_var (Var (compiler_var_name var_base index))
Proof
  simp[abi_operand_before_def, compiler_var_name_def] >> rpt strip_tac >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive aggregate child result and SSA bounds: " ^ name)
  end) (DB.thms "abiChildFlatCode")
