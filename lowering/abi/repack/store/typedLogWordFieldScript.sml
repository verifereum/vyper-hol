(* TOP-LEVEL: scalar Log fields use the same actual allocation interval
   and typed memory frame as memory-backed fields. Their source is a word. *)
Theory typedLogWordField
Ancestors
  typedCopyStateFrame typedLogFieldCode typedStoreFrames typedSArrayDynFieldCode fieldAddressProps
  memoryStoreProps localValueStoreProps valueLoadProps logBytesStoreProps
  typedSArrayDynInvariant memoryValueDefs valueEncoding abiStaticLoopCode
  context stmtLowering compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem compile_log_word_field_path:
  !tenv ctx func cenv ty tv buf src field_offset cs ret cs' ss v buf_addr src_word.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    compile_log_store_data cenv [(src,ty)] [ty] buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    lowered_value_rel ty tv v src ss /\
    eval_operand buf ss = SOME buf_addr /\ eval_operand src ss = SOME src_word /\
    EVERY (\name. src <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) /\
    w2n buf_addr + field_offset + type_memory_size tv < dimword(:256) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      value_has_type tv v /\ memory_value_rel tv v (w2n buf_addr + field_offset) out.vs_memory /\
      lowered_value_rel ty tv v src out /\
      array_copy_frame tv 1 (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all evaluated_word_memory_size >> DISCH_TAC >>
  `w2n buf_addr + field_offset < dimword(:256)` by decide_tac >>
  `w2n (buf_addr + n2w field_offset) = w2n buf_addr + field_offset` by
    (irule log_field_address >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all compile_log_field_store_cuts >>
  disch_then (qx_choose_then `dst` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) emit_field_address_path >>
  rename1 `fragment_path ctx func ss addressed` >>
  `lowered_value_rel ty tv v src addressed` by
    (qpat_x_assum `!ty tv v arg_op. _` (qspecl_then [`ty`, `tv`, `v`, `src`] mp_tac) >> simp[]) >>
  `eval_operand src addressed = SOME src_word` by
    (qpat_x_assum `!arg_op. arg_op <> dst ==> _` (qspec_then `src` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `dst`, `src`, `ty`, `mid`, `ret`, `cs'`,
    `addressed`, `buf_addr + n2w field_offset`, `src_word`] compile_store_memory_word_value_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_assum `w2n (buf_addr + n2w field_offset) = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qpat_assum `addressed.vs_memory = ss.vs_memory`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  mp_tac (Q.SPECL [`buf`, `field_offset`, `cs`, `dst`, `mid`, `ss`, `addressed`, `out`,
    `cs'.cs_next_var - mid.cs_next_var`] emit_field_copy_operand_frame) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [] >> NO_TAC]) >>
  qpat_assum `cs'.cs_next_var - cs.cs_next_var = SUC _`
    (fn delta => disch_then (ASSUME_TAC o PURE_REWRITE_RULE [GSYM delta])) >>
  `eval_operand src out = SOME src_word` by
    (mp_tac (Q.SPECL [`compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)`,
       `src`, `ss`, `out`, `src_word`] compiler_operand_frame_value) >> simp[]) >>
  `lowered_value_rel ty tv v src out` by
    (qpat_x_assum `lowered_value_rel ty tv v src ss` mp_tac >> simp[lowered_value_rel_def]) >>
  `array_copy_frame tv 1 (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory` by
    (asm_simp_tac bool_ss [array_copy_frame_def, MULT_CLAUSES] >> first_assum MATCH_ACCEPT_TAC) >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `addressed` >> simp[]) >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `addressed` >> simp[]) >>
  qexists_tac `out` >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[] >> NO_TAC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed scalar Log field path and frame: " ^ name)
  end) (DB.thms "typedLogWordField")
