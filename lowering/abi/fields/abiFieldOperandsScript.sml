(* TOP-LEVEL: operands reserved before field compilation remain outside all
   subsequent generated name intervals, including across recursive children. *)
Theory abiFieldOperands
Ancestors
  abiFieldReady typedArrayLoopNames abiStaticLoopCode compileEnv venomState list arithmetic

Definition abi_operand_before_def:
  abi_operand_before var_base arg_op <=>
    !n. var_base <= n ==> arg_op <> Var (compiler_var_name n 0)
End

Theorem abi_operand_before_names:
  !var_base arg_op next_var count.
    abi_operand_before var_base arg_op /\ var_base <= next_var ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names next_var count)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_operand_before_def, compiler_var_names_avoid] >>
  strip_tac >> qx_gen_tac `j` >> DISCH_TAC >>
  qpat_x_assum `!n. _` (qspec_then `next_var + j` mp_tac) >>
  impl_tac >- decide_tac >> simp[compiler_var_name_def]
QED

Theorem abi_operand_before_reserved:
  !var_base next_var.
    var_base < next_var ==> abi_operand_before next_var (Var (compiler_var_name var_base 0))
Proof
  simp[abi_operand_before_def, compiler_var_name_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_operand_before_mono:
  !var_base next_var arg_op.
    abi_operand_before var_base arg_op /\ var_base <= next_var ==>
    abi_operand_before next_var arg_op
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_operand_before_def] >> strip_tac >>
  qx_gen_tac `n` >> DISCH_TAC >>
  qpat_x_assum `!n. _` (qspec_then `n` mp_tac) >> impl_tac >- decide_tac >> simp[]
QED

Theorem abi_field_operands_names:
  !var_base next_var src dst dyn_ptr count.
    abi_operand_before var_base src /\ abi_operand_before var_base dst /\
    abi_operand_before var_base dyn_ptr /\ var_base <= next_var ==>
    EVERY (\name. src <> Var name /\ dst <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names next_var count)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [EVERY_CONJ] >>
  rpt conj_tac >> irule abi_operand_before_names >> qexists_tac `var_base` >> simp[]
QED

Theorem abi_operand_before_frame:
  !var_base next_var count before after.
    var_base <= next_var /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names next_var count) ==>
      eval_operand arg_op after = eval_operand arg_op before) ==>
    !arg_op. abi_operand_before var_base arg_op ==> eval_operand arg_op after = eval_operand arg_op before
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  qpat_x_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `arg_op` mp_tac) >>
  impl_tac >- (irule abi_operand_before_names >> qexists_tac `var_base` >> simp[]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI field operand lifetimes: " ^ name)
  end) (DB.thms "abiFieldOperands")
