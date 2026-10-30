(* TOP-LEVEL: entry, live-length test, child addresses, back edge and exit
   for the actual recursive dynamic-array loop. No global SSA freshness is
   required; the saved length and payload pointers precede the loop names. *)
Theory typedDynLoopControl
Ancestors
  typedCopyStateFrame
  typedCopyLoopStateFrame typedDynLoopCode typedDynLoopStructure typedArrayLoopCode typedArrayLoopStructure
  typedArrayLoopEntry typedArrayLoopHeader typedArrayLoopAddress typedArrayLoopCounter
  abiStaticLoopCode fragBlockPath fragExec compileEnv exprLoweringProps emitHelperProps
  instIdxIndep venomState venomInst list words arithmetic

Theorem dynarray_copy_loop_blocks:
  !cenv dst dst_ty capacity src src_ty cs func.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func ==>
    lookup_block (fresh_label_output "typed_dyn_cond" cs.cs_next_label) func.fn_blocks = SOME
      <| bb_label := fresh_label_output "typed_dyn_cond" cs.cs_next_label;
         bb_instructions := typed_array_loop_header (cs.cs_next_id + 7) (cs.cs_next_var + 5)
           (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1))
           (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) (Var (compiler_var_name cs.cs_next_var 0)) |> /\
    ?body_bb. lookup_block (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1)) func.fn_blocks = SOME body_bb /\
      isPREFIX (typed_array_loop_addresses (cs.cs_next_id + 7) (cs.cs_next_var + 5)
        (Var (compiler_var_name cs.cs_next_var 4)) (Var (compiler_var_name cs.cs_next_var 3))
        (type_memory_bytes cenv dst_ty) (type_memory_bytes cenv src_ty)) body_bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code _ (dynarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [dynarray_copy_start_def]) >> DISCH_TAC >>
  drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) typed_array_loop_prefix_contains >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexists_tac `body_bb` >> simp[]
QED

Theorem dynarray_copy_loop_entry:
  !ctx func cenv dst dst_ty capacity src src_ty cs ss.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH (dyn_copy_prefix_state cs dst src capacity).cs_current_insts /\ ~ss.vs_halted ==>
    fragment_path ctx func ss (jump_to (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
      (update_var (compiler_var_name cs.cs_next_var 5) 0w ss))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code _ (dynarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [dynarray_copy_start_def]) >> DISCH_TAC >>
  `ss.vs_current_bb = (dyn_copy_prefix_state cs dst src capacity).cs_current_bb` by simp[] >>
  drule_all_then (qspec_then `ctx` mp_tac) typed_array_loop_entry_path >>
  simp[compiler_var_name_add]
QED

Theorem dynarray_copy_loop_enter_body:
  !ctx func cenv dst dst_ty capacity src src_ty cs ss i n.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func /\
    ss.vs_current_bb = fresh_label_output "typed_dyn_cond" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME (n2w i) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME (n2w n) /\
    i < n /\ n < dimword(:256) ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1))
        (typed_array_loop_header_state (cs.cs_next_var + 5) (n2w i) (n2w n) ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all dynarray_copy_loop_blocks >> strip_tac >>
  `phi_prefix_length body_bb.bb_instructions = 0` by
    (drule_all typed_array_loop_body_no_phi >> simp[]) >>
  `i < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id + 7`, `cs.cs_next_var + 5`,
    `fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1)`,
    `fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)`, `Var (compiler_var_name cs.cs_next_var 0)`,
    `ss`, `(n2w i:bytes32)`, `(n2w n:bytes32)`,
    `<| bb_label := fresh_label_output "typed_dyn_cond" cs.cs_next_label;
        bb_instructions := typed_array_loop_header (cs.cs_next_id + 7) (cs.cs_next_var + 5)
          (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1))
          (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) (Var (compiler_var_name cs.cs_next_var 0)) |>`,
    `body_bb`] typed_array_loop_header_path) >> impl_tac >- simp[compiler_var_name_add] >> simp[]
QED

Theorem dynarray_copy_loop_child_entry:
  !ctx func cenv dst dst_ty capacity src src_ty cs ss counter_word dst_data src_data.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func /\
    ss.vs_current_bb = fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1) /\
    ss.vs_inst_idx = 0 /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME counter_word /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 4)) ss = SOME dst_data /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 3)) ss = SOME src_data ==>
    ?child_ss. fragment_path ctx func ss child_ss /\ copy_state_frame ss child_ss /\
      child_ss.vs_current_bb = (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_current_bb /\
      child_ss.vs_inst_idx = LENGTH (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs).cs_current_insts /\
      child_ss.vs_halted = ss.vs_halted /\ child_ss.vs_memory = ss.vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 10)) child_ss =
        SOME (src_data + counter_word * n2w (type_memory_bytes cenv src_ty)) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 11)) child_ss =
        SOME (dst_data + counter_word * n2w (type_memory_bytes cenv dst_ty)) /\
      (!arg_op. EVERY (\j. arg_op <> Var (compiler_var_name (cs.cs_next_var + 5) j)) [3;4;5;6] ==>
        eval_operand arg_op child_ss = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code _ (dynarray_copy_start _ _ _ _ _ _ _) func`
    (mp_tac o REWRITE_RULE [dynarray_copy_start_def]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dyn_copy_prefix_state cs dst src capacity`,
    `fresh_label_output "typed_dyn_cond" cs.cs_next_label`,
    `fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1)`,
    `fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)`, `Var (compiler_var_name cs.cs_next_var 0)`,
    `Var (compiler_var_name cs.cs_next_var 4)`, `Var (compiler_var_name cs.cs_next_var 3)`,
    `type_memory_bytes cenv dst_ty`, `type_memory_bytes cenv src_ty`, `ss`, `counter_word`, `dst_data`, `src_data`]
    typed_array_loop_addresses_path) >> impl_tac >- simp[compiler_var_name_add] >> DISCH_TAC >>
  qpat_x_assum `fragment_path ctx func ss _`
    (ASSUME_TAC o SIMP_RULE (srw_ss()) []) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [compiler_var_name_add]
    (Q.SPECL [`cs.cs_next_var + 5`, `counter_word`, `dst_data`, `src_data`,
      `type_memory_bytes cenv dst_ty`, `type_memory_bytes cenv src_ty`, `ss`]
      typed_array_loop_address_values)) >>
  qexists_tac `(typed_array_loop_address_state (cs.cs_next_var + 5) counter_word dst_data src_data
    (type_memory_bytes cenv dst_ty) (type_memory_bytes cenv src_ty) ss) with vs_inst_idx := 4` >>
  simp[dynarray_copy_start_def, typed_array_loop_start_def, typed_array_loop_addresses_straight,
    eval_op_inst_idx, typed_array_loop_address_operand_frame]
QED

Theorem dynarray_copy_loop_back_edge:
  !ctx func cenv dst dst_ty capacity src src_ty cs after ss counter_word.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func /\
    fn_has_code after (dynarray_copy_finish cs after) func /\
    ss.vs_current_bb = after.cs_current_bb /\ ss.vs_inst_idx = LENGTH after.cs_current_insts /\
    ~ss.vs_halted /\ eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME counter_word ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
        (typed_array_loop_counter_state after.cs_next_var (compiler_var_name cs.cs_next_var 5) counter_word ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all dynarray_copy_loop_blocks >> strip_tac >>
  qpat_x_assum `fn_has_code after (dynarray_copy_finish _ _) func`
    (mp_tac o REWRITE_RULE [dynarray_copy_finish_def]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `after`, `compiler_var_name cs.cs_next_var 5`,
    `fresh_label_output "typed_dyn_cond" cs.cs_next_label`, `fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)`,
    `ss`, `counter_word`,
    `<| bb_label := fresh_label_output "typed_dyn_cond" cs.cs_next_label;
        bb_instructions := typed_array_loop_header (cs.cs_next_id + 7) (cs.cs_next_var + 5)
          (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1))
          (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) (Var (compiler_var_name cs.cs_next_var 0)) |>`]
    typed_array_loop_counter_path) >> simp[typed_array_loop_header_no_phi]
QED

Theorem dynarray_copy_loop_exit:
  !ctx func cenv dst dst_ty capacity src src_ty cs ss n exit_bb.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst dst_ty capacity src src_ty cs) func /\
    ss.vs_current_bb = fresh_label_output "typed_dyn_cond" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME (n2w n) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME (n2w n) /\
    lookup_block (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2))
        (typed_array_loop_header_state (cs.cs_next_var + 5) (n2w n) (n2w n) ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all dynarray_copy_loop_blocks >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id + 7`, `cs.cs_next_var + 5`,
    `fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1)`,
    `fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)`, `Var (compiler_var_name cs.cs_next_var 0)`,
    `ss`, `(n2w n:bytes32)`, `(n2w n:bytes32)`,
    `<| bb_label := fresh_label_output "typed_dyn_cond" cs.cs_next_label;
        bb_instructions := typed_array_loop_header (cs.cs_next_id + 7) (cs.cs_next_var + 5)
          (fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1))
          (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) (Var (compiler_var_name cs.cs_next_var 0)) |>`,
    `exit_bb`] typed_array_loop_header_path) >> impl_tac >- simp[compiler_var_name_add] >> simp[]
QED
