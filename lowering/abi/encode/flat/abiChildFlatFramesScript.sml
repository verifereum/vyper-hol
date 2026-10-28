(* TOP-LEVEL: caller operands survive the dynamic prefix, a complete child
   encoder, and the real one-variable suffix, even when child length varies. *)
Theory abiChildFlatFrames
Ancestors
  abiChildFlatCode abiFieldOperands abiChildPrefix abiStaticLoopCode
  instIdxIndep compileEnv venomState list words arithmetic

Theorem abi_child_flat_operand_frame:
  !var_base suffix_var head_offset dst_addr dyn_addr ss index child_out out.
    var_base <= suffix_var /\
    (!arg_op. abi_operand_before (var_base + 3) arg_op ==> eval_operand arg_op child_out =
      eval_operand arg_op ((abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) with vs_inst_idx := index)) /\
    (!arg_op. arg_op <> Var (compiler_var_name suffix_var 0) ==>
      eval_operand arg_op out = eval_operand arg_op child_out) ==>
    !arg_op. abi_operand_before var_base arg_op ==> eval_operand arg_op out = eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  `abi_operand_before (var_base + 3) arg_op` by
    (irule abi_operand_before_mono >> qexists_tac `var_base` >> simp[]) >>
  `abi_operand_before suffix_var arg_op` by
    (irule abi_operand_before_mono >> qexists_tac `var_base` >> simp[]) >>
  `arg_op <> Var (compiler_var_name suffix_var 0)` by
    (irule abi_operand_before_self >> first_assum MATCH_ACCEPT_TAC) >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 3)` by
    (irule abi_operand_before_names >> qexists_tac `var_base` >> simp[]) >>
  asm_simp_tac (srw_ss()) [eval_op_inst_idx, abi_child_prefix_operand_frame]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed caller operand preservation across a recursive ABI child: " ^ name)
  end) (DB.thms "abiChildFlatFrames")
