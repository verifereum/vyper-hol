(* TOP-LEVEL: field traversal contracts thread an assertion indexed by the
   remaining metadata, source/head offsets and actual compiler cut. This
   retains reserved SSA operands, recursive source bytes and ownership. *)
Theory abiFieldsContract
Ancestors
  abiFieldsStructure abiComplexCode abiComplexStructure abiStaticLoopCode
  abiEncoder compileEnv fragExec fragBlockPath venomState list pair arithmetic

Definition abi_field_contract_def:
  abi_field_contract ctx func dst src dyn_ptr P (info,head_size,mem_size,is_dyn) rest <=>
    !source_offset head_offset cs child_result mid ss.
      compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
        (abi_complex_field_cut src source_offset cs) = (child_result,mid) /\
      fn_has_code cs mid func /\
      ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
      P ((info,head_size,mem_size,is_dyn)::rest) source_offset head_offset cs ss ==>
      ?out. fragment_path ctx func ss out /\
        out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
        P rest (source_offset + mem_size) (head_offset + head_size) mid out
End

Definition abi_field_list_contract_def:
  abi_field_list_contract ctx func dst src dyn_ptr P [] = T /\
  abi_field_list_contract ctx func dst src dyn_ptr P (entry::rest) =
    (abi_field_contract ctx func dst src dyn_ptr P entry rest /\
     abi_field_list_contract ctx func dst src dyn_ptr P rest)
End

Definition abi_fields_contract_def:
  abi_fields_contract ctx func dst src dyn_ptr P fields <=>
    !source_offset head_offset cs ret cs' ss.
      compile_abi_encode_complex_elems dst src fields source_offset head_offset dyn_ptr cs = (ret,cs') /\
      fn_has_code cs cs' func /\
      ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
      P fields source_offset head_offset cs ss ==>
      ?out. fragment_path ctx func ss out /\
        out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
        P [] (source_offset + SUM (MAP (\(_,_,mem_size,_). mem_size) fields))
          (head_offset + SUM (MAP (\(_,head_size,_,_). head_size) fields)) cs' out
End

Theorem abi_fields_contract_nil:
  !ctx func dst src dyn_ptr P. abi_fields_contract ctx func dst src dyn_ptr P []
Proof
  simp_tac bool_ss [abi_fields_contract_def, abi_complex_fields_nil] >>
  rpt gen_tac >> strip_tac >> gvs[] >> qexists_tac `ss` >> simp[fragment_path_refl]
QED
