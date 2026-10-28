(* TOP-LEVEL: execute a complete field step using the actual two address
   actions and recursive child. Name protection follows the real compiler
   cuts; the child's memory frame is relative to the original input state. *)
Theory typedFieldsHead
Ancestors
  typedCopyStateFrame typedFieldsAddress typedCopyOffset typedCopyOperandFrames typedCopyVarFlow
  typedCopyContract typedSArrayDynInvariant abiBytestringCode abiStaticLoopCode
  memoryValueDefs valueEncoding compileEnv fragExec fragBlockPath
  venomState venomInst list words arithmetic

Theorem typed_copy_field_head_path:
  !ctx func cenv dst src fty aty ftv atv dst_off src_off cs dst_ptr after_dst src_ptr after_src after_child
      ss v dst_addr src_addr.
    compile_with_byte_offset dst dst_off cs = (dst_ptr,after_dst) /\
    compile_with_byte_offset src src_off after_dst = (src_ptr,after_src) /\
    compile_store_memory_typed cenv dst_ptr fty src_ptr aty after_src = ((),after_child) /\
    fn_has_code cs after_dst func /\ fn_has_code after_dst after_src func /\ fn_has_code after_src after_child func /\
    cut_continuation_no_phi after_child func /\
    typed_copy_contract ctx func dst_ptr src_ptr ftv atv after_src after_child /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name)
      (compiler_var_names cs.cs_next_var (after_child.cs_next_var - cs.cs_next_var)) /\
    value_has_type atv v /\ memory_value_rel atv v (w2n (src_addr + n2w src_off)) ss.vs_memory /\
    w2n (src_addr + n2w src_off) + type_memory_size atv < dimword(:256) /\
    w2n (dst_addr + n2w dst_off) + type_memory_size ftv < dimword(:256) /\
    (w2n (src_addr + n2w src_off) + type_memory_size atv <= w2n (dst_addr + n2w dst_off) \/
      w2n (dst_addr + n2w dst_off) + type_memory_size ftv <= w2n (src_addr + n2w src_off)) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = after_child.cs_current_bb /\
      out.vs_inst_idx = LENGTH after_child.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel ftv v (w2n (dst_addr + n2w dst_off)) out.vs_memory /\
      array_copy_frame ftv 1 (w2n (dst_addr + n2w dst_off)) ss.vs_memory out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (after_child.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `cs.cs_next_var <= after_dst.cs_next_var` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_next_var)) >>
  `after_dst.cs_next_var <= after_src.cs_next_var` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_next_var)) >>
  drule compile_store_memory_typed_next_var >> DISCH_TAC >>
  qpat_assum `EVERY _ (compiler_var_names cs.cs_next_var _)` (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  `EVERY (\name. dst <> Var name /\ src <> Var name)
    (compiler_var_names cs.cs_next_var (after_src.cs_next_var - cs.cs_next_var))` by
    (mp_tac (Q.SPECL [`dst`, `src`, `cs.cs_next_var`, `cs.cs_next_var`, `after_src.cs_next_var`, `after_child.cs_next_var`]
       compiler_operands_avoid_interval) >> impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  `EVERY (\name. src <> Var name) (compiler_var_names after_dst.cs_next_var (after_child.cs_next_var - after_dst.cs_next_var))` by
    (mp_tac (Q.SPECL [`src`, `cs.cs_next_var`, `after_dst.cs_next_var`, `after_child.cs_next_var`, `after_child.cs_next_var`]
       compiler_operand_avoid_interval) >> impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  `EVERY (\name. dst_ptr <> Var name) (compiler_var_names after_src.cs_next_var (after_child.cs_next_var - after_src.cs_next_var))` by
    (mp_tac (Q.SPECL [`dst`, `dst_off`, `cs`, `dst_ptr`, `after_dst`, `after_src.cs_next_var`, `after_child.cs_next_var`]
       compile_with_byte_offset_result_avoids) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `EVERY (\name. src_ptr <> Var name) (compiler_var_names after_src.cs_next_var (after_child.cs_next_var - after_src.cs_next_var))` by
    (mp_tac (Q.SPECL [`src`, `src_off`, `after_dst`, `src_ptr`, `after_src`, `after_src.cs_next_var`, `after_child.cs_next_var`]
       compile_with_byte_offset_result_avoids) >> impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  `EVERY (\name. dst_ptr <> Var name /\ src_ptr <> Var name)
    (compiler_var_names after_src.cs_next_var (after_child.cs_next_var - after_src.cs_next_var))` by simp[EVERY_CONJ] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `dst_off`, `src_off`, `cs`, `dst_ptr`, `after_dst`, `src_ptr`, `after_src`,
    `ss`, `dst_addr`, `src_addr`] typed_copy_field_addresses_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then (qx_choose_then `addressed` strip_assume_tac) >>
  qpat_x_assum `typed_copy_contract _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [typed_copy_contract_def]) >>
  disch_then (qspecl_then [`addressed`, `v`, `dst_addr + n2w dst_off`, `src_addr + n2w src_off`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, asm_simp_tac bool_ss []]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `after_src.cs_next_var`, `after_child.cs_next_var`, `ss`, `addressed`, `out`]
    compiler_operands_frame_intervals) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> DISCH_TAC >>
  `fragment_path ctx func ss out` by (irule fragment_path_trans >> qexists_tac `addressed` >> simp[]) >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `addressed` >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete typed field head path: " ^ name)
  end) (DB.thms "typedFieldsHead")
