(* TOP-LEVEL: execute the first field of the actual tuple copy, deriving
   the child continuation and lifetimes from the complete compiler result.
   The remaining field action and its containing span are preserved. *)
Theory typedFieldsStep
Ancestors
  typedCopyStateFrame
  typedFieldsHead typedFieldsCode typedFieldsContinuation typedCopyTypeContract
  typedCopyOperandFrames typedCopyVarFlow typedCopyContract typedSArrayDynInvariant
  abiBytestringCode abiStaticLoopCode memoryValueDefs valueEncoding
  context compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem typed_fields_copy_step_path:
  !ctx func cenv dst src fty fts aty ats ftv atv dst_off src_off cs ret cs' ss v dst_addr src_addr.
    compile_typed_copy_fields cenv dst src (fty::fts) (aty::ats) dst_off src_off cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func /\
    typed_copy_type_contract ctx func cenv fty aty ftv atv /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) /\
    value_has_type atv v /\ memory_value_rel atv v (w2n (src_addr + n2w src_off)) ss.vs_memory /\
    w2n (src_addr + n2w src_off) + type_memory_size atv < dimword(:256) /\
    w2n (dst_addr + n2w dst_off) + type_memory_size ftv < dimword(:256) /\
    (w2n (src_addr + n2w src_off) + type_memory_size atv <= w2n (dst_addr + n2w dst_off) \/
      w2n (dst_addr + n2w dst_off) + type_memory_size ftv <= w2n (src_addr + n2w src_off)) ==>
    ?after_child out.
      compile_typed_copy_fields cenv dst src fts ats
        (dst_off + type_memory_bytes cenv fty) (src_off + type_memory_bytes cenv aty) after_child = (ret,cs') /\
      fn_has_code after_child cs' func /\ cs.cs_next_var <= after_child.cs_next_var /\
      after_child.cs_next_var <= cs'.cs_next_var /\
      fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = after_child.cs_current_bb /\
      out.vs_inst_idx = LENGTH after_child.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel ftv v (w2n (dst_addr + n2w dst_off)) out.vs_memory /\
      array_copy_frame ftv 1 (w2n (dst_addr + n2w dst_off)) ss.vs_memory out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (after_child.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_typed_copy_fields_cons_contains >>
  disch_then (qx_choose_then `dst_ptr` (qx_choose_then `after_dst` (qx_choose_then `src_ptr`
    (qx_choose_then `after_src` (qx_choose_then `after_child` strip_assume_tac))))) >>
  `cs.cs_next_var <= after_dst.cs_next_var` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_next_var)) >>
  `after_dst.cs_next_var <= after_src.cs_next_var` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_next_var)) >>
  `after_src.cs_next_var <= after_child.cs_next_var` by
    (first_assum (ACCEPT_TAC o MATCH_MP compile_store_memory_typed_next_var)) >>
  `after_child.cs_next_var <= cs'.cs_next_var` by
    (first_assum (ACCEPT_TAC o MATCH_MP compile_typed_copy_fields_next_var)) >>
  `EVERY (\name. dst <> Var name /\ src <> Var name)
    (compiler_var_names cs.cs_next_var (after_child.cs_next_var - cs.cs_next_var))` by
    (mp_tac (Q.SPECL [`dst`, `src`, `cs.cs_next_var`, `cs.cs_next_var`, `after_child.cs_next_var`, `cs'.cs_next_var`]
       compiler_operands_avoid_interval) >> impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  `cut_continuation_no_phi after_child func` by
    (mp_tac (Q.SPECL [`cenv`, `dst`, `src`, `fts`, `ats`, `dst_off + type_memory_bytes cenv fty`,
       `src_off + type_memory_bytes cenv aty`, `after_child`, `ret`, `cs'`, `func`]
       compile_typed_copy_fields_continuation) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  drule_all typed_copy_type_contract_result >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `src`, `fty`, `aty`, `ftv`, `atv`, `dst_off`, `src_off`, `cs`,
    `dst_ptr`, `after_dst`, `src_ptr`, `after_src`, `after_child`, `ss`, `v`, `dst_addr`, `src_addr`]
    typed_copy_field_head_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexistsl_tac [`after_child`, `out`] >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual tuple field step path: " ^ name)
  end) (DB.thms "typedFieldsStep")
