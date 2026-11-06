(* TOP-LEVEL: bytes/string stores execute the actual compiler fragment and
   establish the declared field's typed value, including capacity widening. *)
Theory bytesCopyProps
Ancestors
  vyperEventArgCompat
  typedCopyStateFrame bytesCopyCode bytesCopyExec bytesCopyMemory bytesSnapshotMemory
  memoryValueDefs valueLoadProps eventTopicValueProps abiBytestringCode
  vyperEventCompatibility vyperTypeSystem vyperValue vyperTyping vyperAST
  compileEnv context exprLoweringProps fragBlockPath fragExec instIdxIndep
  venomState list words

Theorem event_arg_compatible_bytestring:
  !fty aty. is_bytestring_type fty /\ event_arg_compatible fty aty ==> is_bytestring_type aty
Proof
  rpt gen_tac >> strip_tac >> drule bytestring_type_cases >> strip_tac >> gvs[] >>
  Cases_on `aty` >> gvs[event_arg_compatible_def, is_bytestring_type_def] >>
  rename1 `BaseT ab` >> Cases_on `ab` >>
  gvs[event_arg_compatible_def, is_bytestring_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[event_arg_compatible_def, is_bytestring_type_def]
QED

Theorem compile_store_bytestring_execution:
  !dst src cs ret cs' ss dst_addr src_addr.
    compile_store_bytestring src dst cs = (ret,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 4) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (bytes_copy_result cs.cs_next_var dst_addr src_addr ss)
Proof
  rpt strip_tac >> drule_all compile_store_bytestring_code >> strip_tac >>
  simp[bytes_copy_execution]
QED

Theorem compile_store_bytestring_path:
  !tenv ctx func fty aty ftv atv v dst src cs ret cs' ss dst_addr src_addr.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    compile_store_bytestring src dst cs = (ret,cs') /\
    lowered_value_rel aty atv v src ss /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    type_memory_size atv < dimword(:256) /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 4) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\ lowered_value_rel fty ftv v dst out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 4) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt strip_tac >> drule_all compile_store_bytestring_execution >> strip_tac >>
  drule_all compile_store_bytestring_code >> strip_tac >>
  `is_bytestring_type aty` by (drule_all event_arg_compatible_bytestring >> simp[]) >>
  `~is_word_type fty /\ ~is_word_type aty` by
    (conj_tac >> irule bytestring_type_not_word >> simp[]) >>
  `memory_value_rel atv v (w2n src_addr) ss.vs_memory /\ value_has_type atv v` by
    gvs[lowered_value_rel_def] >>
  `value_has_type ftv v` by
    (drule_all (cj 1 event_arg_compatible_value_has_type) >> simp[]) >>
  `memory_value_rel ftv v (w2n dst_addr)
    (bytes_copy_result cs.cs_next_var dst_addr src_addr ss).vs_memory` by
    (mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `cs.cs_next_var`,
       `dst_addr`, `src_addr`, `ss`] bytes_copy_result_widened_layout) >> simp[]) >>
  `EVERY (\name. dst <> Var name) (compiler_var_names cs.cs_next_var 4)` by fs[EVERY_CONJ] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `bytes_copy_result cs.cs_next_var dst_addr src_addr ss`] fragment_path_emitted) >>
  impl_tac >- simp[bytes_copy_straight] >> strip_tac >>
  qexists_tac `(bytes_copy_result cs.cs_next_var dst_addr src_addr ss) with
    vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[lowered_value_rel_def, eval_op_inst_idx, bytes_copy_result_operand_frame] >>
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `cs.cs_next_var`,
    `dst_addr`, `src_addr`, `ss`, `other_tv`, `other_v`, `offset`]
    bytes_copy_result_preserves_field_region) >> simp[]
QED

Theorem compile_store_memory_bytes_path:
  !tenv ctx func cenv fty aty ftv atv v dst src cs ret cs' ss dst_addr src_addr.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    compile_store_memory cenv src dst fty aty cs = (ret,cs') /\
    lowered_value_rel aty atv v src ss /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    type_memory_size atv < dimword(:256) /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 4) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\ lowered_value_rel fty ftv v dst out /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 4) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt strip_tac >> `~is_word_type fty` by (drule_all bytestring_type_not_word >> simp[]) >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_store_memory_def] >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `fty`, `aty`, `ftv`, `atv`, `v`, `dst`, `src`,
    `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_store_bytestring_path) >> simp[]
QED
