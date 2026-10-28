(* TOP-LEVEL: the recursive typed-store dispatcher executes the verified
   bytes/string copy, including widening and complete typed memory frames.
   This is the recursive child of nested string and bytes array copies. *)
Theory typedBytesStoreProps
Ancestors
  typedCopyStateFrame bytesCopyCode bytesCopyProps typedCopyContract typedSArrayDynInvariant eventTopicValueProps valueLoadProps memoryValueDefs
  context compileEnv exprLoweringProps abiBytestringCode
  vyperTypeSystem vyperValue vyperTyping fragBlockPath fragExec venomState list words

Theorem compile_store_memory_typed_bytes_dispatch:
  !cenv dst fty src aty.
    is_bytestring_type fty /\ is_bytestring_type aty ==>
    compile_store_memory_typed cenv dst fty src aty = compile_store_bytestring src dst
Proof
  rpt gen_tac >> strip_tac >>
  `~is_word_type fty` by (irule bytestring_type_not_word >> simp[]) >>
  simp[Once compile_store_memory_typed_def]
QED

Theorem compile_store_memory_typed_bytes_code:
  !cenv dst fty src aty cs ret cs'.
    is_bytestring_type fty /\ is_bytestring_type aty /\
    compile_store_memory_typed cenv dst fty src aty cs = (ret,cs') ==>
    ret = () /\ same_blocks cs cs' /\ cs'.cs_next_var = cs.cs_next_var + 4 /\
    emitted_insts cs cs' = bytes_copy_insts cs.cs_next_id (compiler_var_names cs.cs_next_var 4) dst src /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_store_memory_typed_bytes_dispatch] >> DISCH_TAC >>
  drule compile_store_bytestring_code >> simp[]
QED

Theorem compile_store_memory_typed_bytes_path:
  !tenv ctx func cenv fty aty ftv atv v dst src cs ret cs' ss dst_addr src_addr.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    compile_store_memory_typed cenv dst fty src aty cs = (ret,cs') /\
    lowered_value_rel aty atv v src ss /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    type_memory_size atv < dimword(:256) /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 4) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\ lowered_value_rel fty ftv v dst out /\
      value_has_type ftv v /\ memory_value_rel ftv v (w2n dst_addr) out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 4) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `is_bytestring_type aty` by (drule_all event_arg_compatible_bytestring >> simp[]) >>
  `~is_word_type fty` by (irule bytestring_type_not_word >> simp[]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_store_memory_typed_bytes_dispatch] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `fty`, `aty`, `ftv`, `atv`, `v`, `dst`, `src`,
    `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_store_bytestring_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `eval_operand dst out = SOME dst_addr` by
    (qpat_x_assum `!arg_op. _` (qspec_then `dst` mp_tac) >> impl_tac >- fs[EVERY_CONJ] >> simp[]) >>
  `value_has_type ftv v /\ memory_value_rel ftv v (w2n dst_addr) out.vs_memory` by
    (qpat_x_assum `lowered_value_rel fty ftv v dst out` mp_tac >> simp[lowered_value_rel_def]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_store_memory_typed_bytes_contract:
  !tenv ctx func cenv dst fty ftv src aty atv cs ret cs'.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    compile_store_memory_typed cenv dst fty src aty cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `is_bytestring_type aty` by (drule_all event_arg_compatible_bytestring >> simp[]) >>
  `~is_word_type aty` by (irule bytestring_type_not_word >> simp[]) >>
  drule_all compile_store_memory_typed_bytes_code >> strip_tac >>
  asm_simp_tac (srw_ss()) [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `type_memory_size atv < dimword(:256)` by decide_tac >>
  `lowered_value_rel aty atv v src ss` by simp[lowered_value_rel_def] >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`, `v`, `dst`, `src`,
    `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_store_memory_typed_bytes_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qexists_tac `out` >> asm_simp_tac (srw_ss()) [array_copy_frame_def] >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive bytes/string store theorem: " ^ name)
  end) (DB.thms "typedBytesStoreProps")
