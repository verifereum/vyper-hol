(* TOP-LEVEL: initialization, back edge and final branch for the actual
   fixed-array copy compiler. The recursive child may add arbitrary blocks.
   The open exit's no-PHI condition is checked in the containing function. *)
Theory typedSArrayControl
Ancestors
  typedSArrayLoop typedArrayLoopCode typedArrayLoopStructure typedArrayLoopEntry
  typedArrayLoopHeader typedArrayLoopCounter abiStaticLoopCode
  fragBlockPath fragExec compileEnv exprLoweringProps emitHelperProps venomState venomInst list words arithmetic

Theorem compile_copy_sarray_loop_entry:
  !ctx func cenv dst dst_ty src src_ty copy_count cs ret cs' ss.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) /\
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs = (ret,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "typed_sa_cond" cs.cs_next_label)
        (update_var (compiler_var_name cs.cs_next_var 0) 0w ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_sarray_loop_contains >> strip_tac >>
  qpat_x_assum `fn_has_code cs (sarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [sarray_copy_start_def]) >> DISCH_TAC >>
  drule_all_then (qspec_then `ctx` mp_tac) typed_array_loop_entry_path >> simp[]
QED

Theorem sarray_copy_loop_back_edge:
  !ctx func cenv dst dst_ty src src_ty copy_count cs after ss counter_word.
    fn_has_code cs (sarray_copy_start cenv dst dst_ty src src_ty copy_count cs) func /\
    fn_has_code after (sarray_copy_finish cs after) func /\
    ss.vs_current_bb = after.cs_current_bb /\ ss.vs_inst_idx = LENGTH after.cs_current_insts /\
    ~ss.vs_halted /\ eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_word ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "typed_sa_cond" cs.cs_next_label)
        (typed_array_loop_counter_state after.cs_next_var (compiler_var_name cs.cs_next_var 0)
          counter_word ss))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code cs (sarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [sarray_copy_start_def]) >> DISCH_TAC >>
  drule_all typed_array_loop_prefix_contains >> strip_tac >>
  qpat_x_assum `fn_has_code after (sarray_copy_finish _ _) func`
    (mp_tac o REWRITE_RULE [sarray_copy_finish_def]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `after`, `compiler_var_name cs.cs_next_var 0`,
    `fresh_label_output "typed_sa_cond" cs.cs_next_label`,
    `fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)`, `ss`, `counter_word`,
    `<| bb_label := fresh_label_output "typed_sa_cond" cs.cs_next_label;
        bb_instructions := typed_array_loop_header cs.cs_next_id cs.cs_next_var
          (fresh_label_output "typed_sa_body" (cs.cs_next_label + 1))
          (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) (Lit (n2w copy_count)) |>`]
    typed_array_loop_counter_path) >> simp[typed_array_loop_header_no_phi]
QED

Theorem compile_copy_sarray_loop_exit:
  !ctx func cenv dst dst_ty src src_ty copy_count cs ret cs' ss exit_bb.
    ~(type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
      ~is_abi_dynamic cenv.ce_struct_fields dst_ty) /\
    compile_copy_sarray_typed cenv dst dst_ty src src_ty copy_count cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME (n2w copy_count) /\
    lookup_block (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to cs'.cs_current_bb
        (typed_array_loop_header_state cs.cs_next_var (n2w copy_count) (n2w copy_count) ss)) /\
    cs'.cs_current_insts = []
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_sarray_loop_contains >> strip_tac >>
  qpat_x_assum `fn_has_code cs (sarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [sarray_copy_start_def]) >> DISCH_TAC >>
  drule_all typed_array_loop_prefix_contains >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`,
    `fresh_label_output "typed_sa_body" (cs.cs_next_label + 1)`,
    `fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)`, `Lit (n2w copy_count)`,
    `ss`, `(n2w copy_count:bytes32)`, `(n2w copy_count:bytes32)`,
    `<| bb_label := fresh_label_output "typed_sa_cond" cs.cs_next_label;
        bb_instructions := typed_array_loop_header cs.cs_next_id cs.cs_next_var
          (fresh_label_output "typed_sa_body" (cs.cs_next_label + 1))
          (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) (Lit (n2w copy_count)) |>`,
    `exit_bb`] typed_array_loop_header_path) >>
  simp[eval_operand_lit, sarray_copy_finish_def, typed_array_loop_finish_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed fixed-array loop control theorem: " ^ name)
  end) (DB.thms "typedSArrayControl")
