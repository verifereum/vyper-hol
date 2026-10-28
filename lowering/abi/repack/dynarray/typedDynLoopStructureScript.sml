(* TOP-LEVEL: a containing function includes the dynamic-array header
   prefix, loop scaffold, recursive child and back edge. The child's final
   block and generated labels are retained by the real compiler. *)
Theory typedDynLoopStructure
Ancestors
  typedDynLoopCode typedArrayLoopCode typedArrayLoopStructure
  typedCopyAppend compileAppendProps abiStaticLoopCode context compileEnv fragExec
  exprLoweringProps venomInst list rich_list pair arithmetic

Theorem dyn_copy_prefix_extends:
  !cs dst src capacity. cs_extends cs (dyn_copy_prefix_state cs dst src capacity)
Proof
  rpt gen_tac >> rewrite_tac[cs_extends_def] >> qexists_tac `[]` >>
  simp[dyn_copy_prefix_state_def, IS_PREFIX_APPEND]
QED

Theorem dynarray_copy_start_extends:
  !cenv dst dst_ty capacity src src_ty cs.
    cs_extends (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs)
Proof
  rpt gen_tac >> rewrite_tac[dynarray_copy_start_def] >> irule typed_array_loop_start_extends
QED

Theorem dynarray_copy_finish_extends:
  !cs after. cs_extends after (dynarray_copy_finish cs after)
Proof
  simp[dynarray_copy_finish_def, typed_array_loop_finish_extends]
QED

Theorem compile_copy_dynarray_loop_split:
  !cenv dst dst_ty capacity src src_ty cs ret cs'.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\ dst_ty = src_ty) /\
    compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty cs = (ret,cs') ==>
    ?after. ret = () /\
      compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) dst_ty
        (Var (compiler_var_name cs.cs_next_var 10)) src_ty
        (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) = ((),after) /\
      cs' = dynarray_copy_finish cs after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cenv`, `dst`, `dst_ty`, `capacity`, `src`, `src_ty`, `cs`]
    compile_copy_dynarray_loop_result) >> impl_tac >- first_assum ACCEPT_TAC >> DISCH_TAC >>
  Cases_on `compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) dst_ty
    (Var (compiler_var_name cs.cs_next_var 10)) src_ty
    (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs)` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (unit_result,after)` >>
  Cases_on `unit_result` >> gvs[LET_THM] >> qexists_tac `after` >> simp[]
QED

Theorem compile_copy_dynarray_loop_contains:
  !cenv dst dst_ty capacity src src_ty cs ret cs' func.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\ dst_ty = src_ty) /\
    compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty cs = (ret,cs') /\
    fn_has_code cs cs' func ==>
    ?after. ret = () /\
      compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) dst_ty
        (Var (compiler_var_name cs.cs_next_var 10)) src_ty
        (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) = ((),after) /\
      cs' = dynarray_copy_finish cs after /\
      fn_has_code cs (dyn_copy_prefix_state cs dst src capacity) func /\
      fn_has_code (dyn_copy_prefix_state cs dst src capacity)
        (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func /\
      fn_has_code (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) after func /\
      fn_has_code after cs' func
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_dynarray_loop_split >> strip_tac >>
  qabbrev_tac `prefix_cs = dyn_copy_prefix_state cs dst src capacity` >>
  qabbrev_tac `child_cs = dynarray_copy_start cenv dst dst_ty capacity src src_ty cs` >>
  `cs_extends cs prefix_cs` by simp[Abbr`prefix_cs`, dyn_copy_prefix_extends] >>
  `cs_extends prefix_cs child_cs` by
    simp[Abbr`prefix_cs`, Abbr`child_cs`, dynarray_copy_start_extends] >>
  `cs_appends (compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) dst_ty
    (Var (compiler_var_name cs.cs_next_var 10)) src_ty)` by simp[CONJUNCT1 cs_appends_typed_copy_mutual] >>
  `cs_extends child_cs after` by (drule_all cs_appends_result_extends >> simp[]) >>
  `cs_extends after cs'` by simp[dynarray_copy_finish_extends] >>
  `cs_extends child_cs cs'` by (irule cs_extends_trans >> qexists_tac `after` >> simp[]) >>
  `cs_extends prefix_cs cs'` by (irule cs_extends_trans >> qexists_tac `child_cs` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `prefix_cs`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`prefix_cs`, `child_cs`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`child_cs`, `after`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >> qexists_tac `after` >> asm_simp_tac bool_ss []
QED

Theorem dynarray_copy_start_fields[simp]:
  !cenv dst dst_ty capacity src src_ty cs.
    (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_next_var = cs.cs_next_var + 12 /\
    (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_next_id = cs.cs_next_id + 16 /\
    (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_next_label = cs.cs_next_label + 3 /\
    (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_current_bb =
      fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1)
Proof
  simp[dynarray_copy_start_def, typed_array_loop_start_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive dynamic-array containment theorem: " ^ name)
  end) (DB.thms "typedDynLoopStructure")
