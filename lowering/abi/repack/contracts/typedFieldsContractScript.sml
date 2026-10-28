(* TOP-LEVEL: complete tuple-field copies use root operands and natural
   byte offsets. The frame covers the entire target tuple footprint. *)
Theory typedFieldsContract
Ancestors
  typedCopyStateFrame
  typedCopyContract typedFieldsCode typedFieldsMemory
  abiStaticLoopCode memoryValueDefs valueEncoding
  context compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Definition typed_fields_copy_contract_def:
  typed_fields_copy_contract ctx func dst src ftvs atvs dst_off src_off start after <=>
    !ss vs dst_addr src_addr.
      fn_has_code start after func /\ cut_continuation_no_phi after func /\
      ss.vs_current_bb = start.cs_current_bb /\ ss.vs_inst_idx = LENGTH start.cs_current_insts /\ ~ss.vs_halted /\
      values_have_types atvs vs /\
      memory_tuple_rel atvs vs (w2n src_addr + src_off) ss.vs_memory /\
      eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
      w2n src_addr + src_off + type_memory_size (TupleTV atvs) < dimword(:256) /\
      w2n dst_addr + dst_off + type_memory_size (TupleTV ftvs) < dimword(:256) /\
      (w2n src_addr + src_off + type_memory_size (TupleTV atvs) <= w2n dst_addr + dst_off \/
        w2n dst_addr + dst_off + type_memory_size (TupleTV ftvs) <= w2n src_addr + src_off) /\
      EVERY (\name. dst <> Var name /\ src <> Var name)
        (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
      ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
        out.vs_current_bb = after.cs_current_bb /\ out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
        memory_tuple_rel ftvs vs (w2n dst_addr + dst_off) out.vs_memory /\
        array_copy_frame (TupleTV ftvs) 1 (w2n dst_addr + dst_off) ss.vs_memory out.vs_memory /\
        (!arg_op. EVERY (\name. arg_op <> Var name)
          (compiler_var_names start.cs_next_var (after.cs_next_var - start.cs_next_var)) ==>
          eval_operand arg_op out = eval_operand arg_op ss)
End

Theorem typed_fields_copy_contract_nil:
  !ctx func cenv dst src dst_off src_off cs ret cs'.
    compile_typed_copy_fields cenv dst src [] [] dst_off src_off cs = (ret,cs') ==>
    typed_fields_copy_contract ctx func dst src [] [] dst_off src_off cs cs'
Proof
  rpt gen_tac >> simp[Once compile_store_memory_typed_def, comp_return_def] >> strip_tac >>
  gvs[] >> simp_tac bool_ss [typed_fields_copy_contract_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `vs` >> fs[vyperTypingTheory.value_has_type_def] >>
  qexists_tac `ss` >> simp[memory_value_rel_def, fragment_path_refl]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete tuple-field copy contract: " ^ name)
  end) (DB.thms "typedFieldsContract")
