(* TOP-LEVEL: actual typed dynamic-array copy with identical element types.
   Capacity widening checks the live length and copies only live elements. *)
Theory dynCopyCode
Ancestors
  abiBytestringCode context compileEnv exprLoweringProps emitHelper
  venomInst list rich_list arithmetic

Definition dyn_copy_prefix_insts_def:
  dyn_copy_prefix_insts id names dst src capacity =
    [mk_inst id MLOAD [src] [EL 0 names];
     mk_inst (id + 1) GT [Var (EL 0 names); Lit (n2w capacity)] [EL 1 names];
     mk_inst (id + 2) ISZERO [Var (EL 1 names)] [EL 2 names];
     mk_inst (id + 3) ASSERT [Var (EL 2 names)] [];
     mk_inst (id + 4) MSTORE [dst; Var (EL 0 names)] [];
     mk_inst (id + 5) ADD [src; Lit 32w] [EL 3 names];
     mk_inst (id + 6) ADD [dst; Lit 32w] [EL 4 names]]
End

Definition dyn_copy_insts_def:
  dyn_copy_insts id names dst src capacity elem_size =
    dyn_copy_prefix_insts id names dst src capacity ++
    [mk_inst (id + 7) MUL [Var (EL 0 names); Lit (n2w elem_size)] [EL 5 names];
     mk_inst (id + 8) MCOPY [Var (EL 4 names); Var (EL 3 names); Var (EL 5 names)] []]
End

Theorem compiler_var_names_six:
  !var_base. compiler_var_names var_base 6 =
    [STRING #"%" (toString var_base); STRING #"%" (toString (var_base + 1));
     STRING #"%" (toString (var_base + 2)); STRING #"%" (toString (var_base + 3));
     STRING #"%" (toString (var_base + 4)); STRING #"%" (toString (var_base + 5))]
Proof
  simp[compiler_var_names_def, GENLIST_CONS]
QED

Theorem compile_copy_dynarray_code:
  !cenv dst elem_ty capacity src cs ret cs'.
    compile_copy_dynarray_typed cenv dst elem_ty capacity src elem_ty cs = (ret,cs') ==>
    ret = () /\
    emitted_insts cs cs' = dyn_copy_insts cs.cs_next_id
      (compiler_var_names cs.cs_next_var 6) dst src capacity (type_memory_bytes cenv elem_ty) /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 6
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Once compile_store_memory_typed_def, compile_copy_memory_dynamic_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emitted_insts_def,
    dyn_copy_insts_def, dyn_copy_prefix_insts_def, compiler_var_names_EL, same_blocks_def,
    DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem dyn_copy_straight:
  !id names dst src capacity elem_size.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (dyn_copy_insts id names dst src capacity elem_size)
Proof
  simp[dyn_copy_insts_def, dyn_copy_prefix_insts_def, mk_inst_def, is_terminator_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-array copy code theorem: " ^ name)
  end) (DB.thms "dynCopyCode")
