(* TOP-LEVEL: execute an actual Log field's address ADD and outer memory
   store using its complete compiler allocation interval and typed frame. *)
Theory typedLogFieldPath
Ancestors
  typedCopyStateFrame typedLogFieldCode typedStoreContract typedStoreFrames typedCopyContract typedSArrayDynInvariant
  typedSArrayDynFieldCode fieldAddressProps logBytesStoreProps
  abiBytestringCode abiStaticLoopCode memoryValueDefs valueEncoding
  context stmtLowering compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem compile_log_memory_field_path:
  !ctx func cenv src aty fty ftv atv buf field_offset cs ret cs' ss v buf_addr src_addr.
    memory_store_type_contract ctx func cenv fty aty ftv atv /\
    compile_log_store_data cenv [(src,aty)] [fty] buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory /\
    eval_operand buf ss = SOME buf_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) /\
    w2n src_addr + type_memory_size atv < dimword(:256) /\
    w2n buf_addr + field_offset + type_memory_size ftv < dimword(:256) /\
    (w2n src_addr + type_memory_size atv <= w2n buf_addr + field_offset \/
      w2n buf_addr + field_offset + type_memory_size ftv <= w2n src_addr) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel ftv v (w2n buf_addr + field_offset) out.vs_memory /\
      array_copy_frame ftv 1 (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
      memory_value_rel atv v (w2n src_addr) out.vs_memory /\ eval_operand src out = SOME src_addr /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `w2n buf_addr + field_offset < dimword(:256)` by decide_tac >>
  `w2n (buf_addr + n2w field_offset) = w2n buf_addr + field_offset` by
    (irule log_field_address >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all compile_log_field_store_cuts >>
  disch_then (qx_choose_then `dst` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) emit_field_address_path >>
  rename1 `fragment_path ctx func ss addressed` >>
  `eval_operand src addressed = SOME src_addr` by
    (qpat_x_assum `!arg_op. arg_op <> dst ==> _` (qspec_then `src` mp_tac) >> simp[]) >>
  drule_all memory_store_type_contract_result >>
  simp_tac bool_ss [typed_copy_contract_def] >>
  disch_then (qspecl_then [`addressed`, `v`, `buf_addr + n2w field_offset`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [] >> NO_TAC]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_assum `w2n (buf_addr + n2w field_offset) = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qpat_assum `addressed.vs_memory = ss.vs_memory`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  mp_tac (Q.SPECL [`buf`, `field_offset`, `cs`, `dst`, `mid`, `ss`, `addressed`, `out`,
    `cs'.cs_next_var - mid.cs_next_var`] emit_field_copy_operand_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `cs'.cs_next_var - cs.cs_next_var = SUC _`
    (fn delta => disch_then (ASSUME_TAC o PURE_REWRITE_RULE [GSYM delta])) >>
  `memory_value_rel atv v (w2n src_addr) out.vs_memory` by
    (mp_tac (Q.SPECL [`ftv`, `atv`, `v`, `1`, `w2n (buf_addr:bytes32) + field_offset`,
       `w2n (src_addr:bytes32)`, `ss.vs_memory`, `out.vs_memory`] array_copy_frame_source) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]) >>
  `eval_operand src out = SOME src_addr` by
    (mp_tac (Q.SPECL [`compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)`,
       `src`, `ss`, `out`, `src_addr`] compiler_operand_frame_value) >> simp[]) >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `addressed` >> simp[]) >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `addressed` >> simp[]) >>
  qexists_tac `out` >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [] >> NO_TAC]
QED
