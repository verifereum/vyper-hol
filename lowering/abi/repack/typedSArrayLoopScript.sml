(* TOP-LEVEL: the actual fixed-array repacking compiler exposes its exact
   recursive child and all three containing code spans. Helpers name the
   reserved parent labels and the open child state. *)
Theory typedSArrayLoop
Ancestors
  typedCopyStateFrame
  typedCopyLoopStateFrame typedArrayLoopCode typedArrayLoopStructure typedArrayLoopHeader typedArrayLoopAddress typedArrayLoopNames
  typedCopyAppend abiStaticLoopCode instIdxIndep
  context compileEnv fragExec fragBlockPath emitHelperProps venomState venomInst list pair words arithmetic

Definition sarray_copy_start_def:
  sarray_copy_start cenv dst dst_ty src src_ty copy_count cs =
    typed_array_loop_start cs
      (fresh_label_output "typed_sa_cond" cs.cs_next_label)
      (fresh_label_output "typed_sa_body" (cs.cs_next_label + 1))
      (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) (Lit (n2w copy_count))
      dst src (type_memory_bytes cenv dst_ty) (type_memory_bytes cenv src_ty)
End

Definition sarray_copy_finish_def:
  sarray_copy_finish cs after =
    typed_array_loop_finish (compiler_var_name cs.cs_next_var 0)
      (fresh_label_output "typed_sa_cond" cs.cs_next_label)
      (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) after
End

Theorem compile_copy_sarray_loop_split:
  !cenv dst dst_ty src src_ty copy_count cs ret cs'.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) /\
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs = (ret,cs') ==>
    ?after. ret = () /\
      compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) dst_ty
        (Var (compiler_var_name cs.cs_next_var 5)) src_ty
        (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs) = ((),after) /\
      cs' = sarray_copy_finish cs after
Proof
  rpt gen_tac >> strip_tac >>
  `compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs =
    ((), sarray_copy_finish cs
      (SND (compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) dst_ty
        (Var (compiler_var_name cs.cs_next_var 5)) src_ty
        (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs))))` by
    (mp_tac (Q.SPECL [`cenv`, `dst`, `dst_ty`, `src`, `src_ty`, `copy_count`, `cs`]
      compile_copy_sarray_loop_result) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp_tac bool_ss [sarray_copy_start_def, sarray_copy_finish_def, LET_THM]) >>
  Cases_on `compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) dst_ty
    (Var (compiler_var_name cs.cs_next_var 5)) src_ty
    (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs)` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (unit_result,after)` >>
  Cases_on `unit_result` >> gvs[] >> qexists_tac `after` >> simp[]
QED

Theorem compile_copy_sarray_loop_contains:
  !cenv dst dst_ty src src_ty copy_count cs ret cs' func.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) /\
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs = (ret,cs') /\
    fn_has_code cs cs' func ==>
    ?after. ret = () /\
      compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) dst_ty
        (Var (compiler_var_name cs.cs_next_var 5)) src_ty
        (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs) = ((),after) /\
      cs' = sarray_copy_finish cs after /\
      fn_has_code cs (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs) func /\
      fn_has_code (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs) after func /\
      fn_has_code after cs' func
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_sarray_loop_split >> strip_tac >>
  `cs_appends (compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) dst_ty
    (Var (compiler_var_name cs.cs_next_var 5)) src_ty)` by
    simp[CONJUNCT1 cs_appends_typed_copy_mutual] >>
  qexists_tac `after` >> simp[] >> fs[sarray_copy_start_def, sarray_copy_finish_def] >>
  drule_all (SIMP_RULE bool_ss [LET_THM] typed_array_loop_contains) >> simp[]
QED

Theorem compile_copy_sarray_loop_enter_body:
  !ctx func cenv dst dst_ty src src_ty copy_count cs ret cs' ss i.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) /\
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME (n2w i) /\
    i < copy_count /\ copy_count < dimword(:256) ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "typed_sa_body" (cs.cs_next_label + 1))
        (typed_array_loop_header_state cs.cs_next_var (n2w i) (n2w copy_count) ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_sarray_loop_contains >> strip_tac >>
  qpat_x_assum `fn_has_code cs (sarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [sarray_copy_start_def]) >> DISCH_TAC >>
  drule_all typed_array_loop_prefix_contains >> strip_tac >>
  `phi_prefix_length body_bb.bb_instructions = 0` by
    (mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `dst`, `src`,
      `type_memory_bytes cenv dst_ty`, `type_memory_bytes cenv src_ty`, `body_bb.bb_instructions`]
      typed_array_loop_body_no_phi) >> simp[]) >>
  `i < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`,
    `fresh_label_output "typed_sa_body" (cs.cs_next_label + 1)`,
    `fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)`, `Lit (n2w copy_count)`,
    `ss`, `(n2w i:bytes32)`, `(n2w copy_count:bytes32)`,
    `<| bb_label := fresh_label_output "typed_sa_cond" cs.cs_next_label;
        bb_instructions := typed_array_loop_header cs.cs_next_id cs.cs_next_var
          (fresh_label_output "typed_sa_body" (cs.cs_next_label + 1))
          (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) (Lit (n2w copy_count)) |>`,
    `body_bb`] typed_array_loop_header_path) >> impl_tac >- simp[eval_operand_lit] >> simp[]
QED

Theorem compile_copy_sarray_loop_child_entry:
  !ctx func cenv dst dst_ty src src_ty copy_count cs ret cs' ss counter_word dst_addr src_addr.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) /\
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = fresh_label_output "typed_sa_body" (cs.cs_next_label + 1) /\
    ss.vs_inst_idx = 0 /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_word /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 3) /\ src <> Var (compiler_var_name cs.cs_next_var 4) /\
    dst <> Var (compiler_var_name cs.cs_next_var 3) /\ dst <> Var (compiler_var_name cs.cs_next_var 4) /\
    dst <> Var (compiler_var_name cs.cs_next_var 5) ==>
    ?child_ss. fragment_path ctx func ss child_ss /\ copy_state_frame ss child_ss /\
      child_ss.vs_current_bb = (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs).cs_current_bb /\
      child_ss.vs_inst_idx = LENGTH (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs).cs_current_insts /\
      child_ss.vs_halted = ss.vs_halted /\ child_ss.vs_memory = ss.vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 5)) child_ss =
        SOME (src_addr + counter_word * n2w (type_memory_bytes cenv src_ty)) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 6)) child_ss =
        SOME (dst_addr + counter_word * n2w (type_memory_bytes cenv dst_ty)) /\
      (!arg_op. EVERY (\j. arg_op <> Var (compiler_var_name cs.cs_next_var j)) [3;4;5;6] ==>
        eval_operand arg_op child_ss = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_sarray_loop_contains >> strip_tac >>
  qpat_x_assum `fn_has_code cs (sarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [sarray_copy_start_def]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`,
    `fresh_label_output "typed_sa_cond" cs.cs_next_label`,
    `fresh_label_output "typed_sa_body" (cs.cs_next_label + 1)`,
    `fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)`, `Lit (n2w copy_count)`,
    `dst`, `src`, `type_memory_bytes cenv dst_ty`, `type_memory_bytes cenv src_ty`,
    `ss`, `counter_word`, `dst_addr`, `src_addr`] typed_array_loop_addresses_path) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  qexists_tac `(typed_array_loop_address_state cs.cs_next_var counter_word dst_addr src_addr
    (type_memory_bytes cenv dst_ty) (type_memory_bytes cenv src_ty) ss) with vs_inst_idx := 4` >>
  simp[sarray_copy_start_def, typed_array_loop_start_def, typed_array_loop_addresses_straight,
    eval_op_inst_idx, typed_array_loop_address_values, typed_array_loop_address_operand_frame]
QED

Theorem sarray_copy_child_names_avoid:
  !cenv dst dst_ty src src_ty copy_count cs num_names j.
    j < 7 ==>
    EVERY (\name. Var (compiler_var_name cs.cs_next_var j) <> Var name)
      (compiler_var_names (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs).cs_next_var num_names)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `7`, `num_names`, `j`] compiler_var_names_before) >>
  simp[sarray_copy_start_def, typed_array_loop_start_def]
QED
