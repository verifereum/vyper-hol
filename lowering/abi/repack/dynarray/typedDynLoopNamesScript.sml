(* TOP-LEVEL: recursive children retain the parent's generated names.
   Their allocation range is derived from the actual compiler, and operand
   frames compose across adjacent generated-name ranges. *)
Theory typedDynLoopNames
Ancestors
  typedCopyVarFlow compileVarFlow typedDynLoopCode typedDynLoopStructure typedArrayLoopCode
  typedArrayLoopNames abiBytestringCode abiStaticLoopCode context compileEnv
  venomState venomInst list arithmetic

Theorem dynarray_copy_child_names:
  !cenv dst dst_ty capacity src src_ty cs ret after.
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) dst_ty
      (Var (compiler_var_name cs.cs_next_var 10)) src_ty
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) = (ret,after) ==>
    ?child_names. after.cs_next_var = cs.cs_next_var + 12 + child_names /\
      (dynarray_copy_finish cs after).cs_next_var = cs.cs_next_var + 13 + child_names
Proof
  rpt gen_tac >> DISCH_TAC >>
  drule_then (ASSUME_TAC o SIMP_RULE (srw_ss()) []) compile_store_memory_typed_next_var >>
  qabbrev_tac `child_names = after.cs_next_var - (cs.cs_next_var + 12)` >>
  `after.cs_next_var = cs.cs_next_var + 12 + child_names` by
    (simp_tac bool_ss [Abbr`child_names`] >> decide_tac) >>
  qexists_tac `child_names` >> simp[dynarray_copy_finish_def, typed_array_loop_finish_def]
QED

Theorem dynarray_copy_parent_names:
  !cenv dst dst_ty capacity src src_ty cs child_names j.
    j < 12 ==>
    EVERY (\name. Var (compiler_var_name cs.cs_next_var j) <> Var name)
      (compiler_var_names (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_next_var child_names)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `12`, `child_names`, `j`] compiler_var_names_before) >> simp[]
QED

Theorem compiler_operands_frame_before:
  !var_base offset num_names initial current j.
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + offset) num_names) ==>
      eval_operand arg_op current = eval_operand arg_op initial) /\ j < offset ==>
    eval_operand (Var (compiler_var_name var_base j)) current =
      eval_operand (Var (compiler_var_name var_base j)) initial
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!arg_op. _` (qspec_then `Var (compiler_var_name var_base j)` mp_tac) >>
  impl_tac >- (irule compiler_var_names_before >> simp[]) >> simp[]
QED

Theorem compiler_operands_frame_ranges:
  !var_base first_count second_count initial mid final.
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_base first_count) ==>
      eval_operand arg_op mid = eval_operand arg_op initial) /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names (var_base + first_count) second_count) ==>
      eval_operand arg_op final = eval_operand arg_op mid) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_base (first_count + second_count)) ==>
      eval_operand arg_op final = eval_operand arg_op initial
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names var_base first_count)` by
    (mp_tac (Q.SPECL [`arg_op`, `var_base`, `first_count + second_count`, `first_count`]
       compiler_var_names_avoid_prefix) >> simp[]) >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + first_count) second_count)` by
    (mp_tac (Q.SPECL [`arg_op`, `var_base`, `first_count + second_count`, `first_count`, `second_count`]
       compiler_var_names_avoid_segment) >> simp[]) >>
  qpat_x_assum `!arg_op. EVERY _ (compiler_var_names var_base first_count) ==> _`
    (qspec_then `arg_op` mp_tac) >>
  qpat_x_assum `!arg_op. EVERY _ (compiler_var_names (var_base + first_count) second_count) ==> _`
    (qspec_then `arg_op` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive dynamic-array name-lifetime theorem: " ^ name)
  end) (DB.thms "typedDynLoopNames")
