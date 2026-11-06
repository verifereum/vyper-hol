(* TOP-LEVEL: connect the actual fixed-array child compiler and its
   typed copy contract to the parent loop. Cuts and allocation ranges
   are obtained from the actual compiler result. *)
Theory typedSArrayChildContract
Ancestors
  typedCopyStateFrame
  typedCopyContract typedSArrayLoop typedCopyVarFlow typedArrayLoopCode typedArrayLoopStructure
  typedSArrayDynInvariant abiBytestringCode abiStaticLoopCode memoryValueDefs valueEncoding
  context compileEnv fragBlockPath fragExec venomExecSemantics venomState venomInst list words arithmetic

Theorem compile_typed_sarray_dispatch:
  !cenv dst dst_elem src src_elem dst_count src_count.
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    compile_store_memory_typed cenv dst (ArrayT dst_elem (Fixed dst_count))
      src (ArrayT src_elem (Fixed src_count)) =
    compile_copy_sarray_typed cenv dst dst_elem src src_elem dst_count
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem sarray_copy_child_counts:
  !cenv dst fty src aty copy_count cs ret after child_names.
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty
      (sarray_copy_start cenv dst fty src aty copy_count cs) = (ret,after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 7) ==>
    after.cs_next_var = cs.cs_next_var + 7 + child_names /\
    (sarray_copy_finish cs after).cs_next_var = cs.cs_next_var + 8 + child_names
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (ASSUME_TAC o SIMP_RULE (srw_ss()) [sarray_copy_start_def, typed_array_loop_start_def])
    compile_store_memory_typed_next_var >>
  `after.cs_next_var = cs.cs_next_var + 7 + child_names` by decide_tac >>
  qpat_x_assum `child_names = _` kall_tac >>
  simp[sarray_copy_finish_def, typed_array_loop_finish_def]
QED

Theorem sarray_copy_child_continuation:
  !cs after func.
    fn_has_code after (sarray_copy_finish cs after) func ==>
    cut_continuation_no_phi after func
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [cut_continuation_no_phi_def] >> DISCH_TAC >>
  qpat_x_assum `fn_has_code _ _ _` (mp_tac o REWRITE_RULE [sarray_copy_finish_def]) >> DISCH_TAC >>
  drule typed_array_loop_suffix_contains >> DISCH_TAC >>
  qexists_tac `<| bb_label := after.cs_current_bb;
    bb_instructions := after.cs_current_insts ++ typed_array_loop_counter after.cs_next_id after.cs_next_var
      (compiler_var_name cs.cs_next_var 0) (fresh_label_output "typed_sa_cond" cs.cs_next_label) |>` >>
  simp[typed_array_loop_counter_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem compile_copy_sarray_contains_child:
  !cenv dst fty src aty copy_count cs ret cs' after func.
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\ fn_has_code cs cs' func /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) ==>
    ret = () /\ cs' = sarray_copy_finish cs after /\
    fn_has_code cs (sarray_copy_start cenv dst fty src aty copy_count cs) func /\
    fn_has_code (sarray_copy_start cenv dst fty src aty copy_count cs) after func /\ fn_has_code after cs' func
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then (qx_choose_then `built_after` strip_assume_tac) compile_copy_sarray_loop_contains >>
  `built_after = after` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = ((),built_after)` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem sarray_copy_child_contract_path:
  !ctx func cenv dst fty src aty copy_count cs after ftv atv ss v dst_addr src_addr.
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
      (Var (compiler_var_name cs.cs_next_var 5)) ftv atv
      (sarray_copy_start cenv dst fty src aty copy_count cs) after /\
    fn_has_code (sarray_copy_start cenv dst fty src aty copy_count cs) after func /\
    fn_has_code after (sarray_copy_finish cs after) func /\
    ss.vs_current_bb = (sarray_copy_start cenv dst fty src aty copy_count cs).cs_current_bb /\
    ss.vs_inst_idx = LENGTH (sarray_copy_start cenv dst fty src aty copy_count cs).cs_current_insts /\ ~ss.vs_halted /\
    value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 6)) ss = SOME dst_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME src_addr /\
    w2n src_addr + type_memory_size atv < dimword(:256) /\
    w2n dst_addr + type_memory_size ftv < dimword(:256) /\
    (w2n src_addr + type_memory_size atv <= w2n dst_addr \/
      w2n dst_addr + type_memory_size ftv <= w2n src_addr) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = after.cs_current_bb /\
      out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel ftv v (w2n dst_addr) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/ w2n dst_addr + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names (cs.cs_next_var + 7) (after.cs_next_var - (cs.cs_next_var + 7))) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all sarray_copy_child_continuation >> DISCH_TAC >>
  `EVERY (\name. Var (compiler_var_name cs.cs_next_var 6) <> Var name /\
      Var (compiler_var_name cs.cs_next_var 5) <> Var name)
    (compiler_var_names (sarray_copy_start cenv dst fty src aty copy_count cs).cs_next_var
      (after.cs_next_var - (sarray_copy_start cenv dst fty src aty copy_count cs).cs_next_var))` by
    (simp_tac bool_ss [EVERY_CONJ] >> conj_tac >> irule sarray_copy_child_names_avoid >> simp[]) >>
  qpat_x_assum `typed_copy_contract _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [typed_copy_contract_def]) >>
  disch_then (qspecl_then [`ss`, `v`, `dst_addr`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [sarray_copy_start_def, typed_array_loop_start_def]) >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  simp_tac bool_ss [MULT_CLAUSES] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
