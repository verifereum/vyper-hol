(* TOP-LEVEL: a uniform actual Log-field contract covers source words and
   source pointers. Memory bounds and separation apply only to pointers. *)
Theory typedLogFieldContract
Ancestors
  typedCopyStateFrame
  typedLogWordField typedLogFieldPath typedStoreContract typedSArrayDynInvariant
  valueLoadProps memoryValueDefs valueEncoding context stmtLowering compileEnv
  abiStaticLoopCode fragExec fragBlockPath venomState venomInst list words arithmetic

Definition log_field_type_contract_def:
  log_field_type_contract ctx func cenv fty aty ftv atv <=>
    !buf src field_offset cs ret cs'.
      compile_log_store_data cenv [(src,aty)] [fty] buf field_offset cs = (ret,cs') ==>
      !ss v buf_addr src_word.
        fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func /\
        ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
        lowered_value_rel aty atv v src ss /\
        eval_operand buf ss = SOME buf_addr /\ eval_operand src ss = SOME src_word /\
        w2n buf_addr + field_offset + type_memory_size ftv < dimword(:256) /\
        (~is_word_type aty ==>
          w2n src_word + type_memory_size atv < dimword(:256) /\
          (w2n src_word + type_memory_size atv <= w2n buf_addr + field_offset \/
            w2n buf_addr + field_offset + type_memory_size ftv <= w2n src_word)) /\
        EVERY (\name. src <> Var name)
          (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
        ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
          out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
          value_has_type ftv v /\ memory_value_rel ftv v (w2n buf_addr + field_offset) out.vs_memory /\
          lowered_value_rel aty atv v src out /\
          array_copy_frame ftv 1 (w2n buf_addr + field_offset) ss.vs_memory out.vs_memory /\
          (!arg_op. EVERY (\name. arg_op <> Var name)
            (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
            eval_operand arg_op out = eval_operand arg_op ss)
End

Theorem log_field_type_contract_word:
  !tenv ctx func cenv ty tv.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
    log_field_type_contract ctx func cenv ty ty tv tv
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [log_field_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`buf`, `src`, `field_offset`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `buf_addr`, `src_word`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `ty`, `tv`, `buf`, `src`, `field_offset`, `cs`, `ret`, `cs'`,
    `ss`, `v`, `buf_addr`, `src_word`] compile_log_word_field_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem log_field_type_contract_memory:
  !ctx func cenv fty aty ftv atv.
    memory_store_type_contract ctx func cenv fty aty ftv atv /\ ~is_word_type aty /\
    (!v. value_has_type atv v ==> value_has_type ftv v) ==>
    log_field_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [log_field_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`buf`, `src`, `field_offset`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `buf_addr`, `src_word`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `~is_word_type aty ==> _` mp_tac >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `value_has_type atv v /\ memory_value_rel atv v (w2n src_word) ss.vs_memory` by
    (qpat_x_assum `lowered_value_rel _ _ _ _ ss` mp_tac >> simp[lowered_value_rel_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `src`, `aty`, `fty`, `ftv`, `atv`, `buf`, `field_offset`, `cs`, `ret`, `cs'`,
    `ss`, `v`, `buf_addr`, `src_word`] compile_log_memory_field_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `value_has_type ftv v` by (first_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  `lowered_value_rel aty atv v src out` by simp[lowered_value_rel_def] >>
  qexists_tac `out` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed uniform Log field type contract: " ^ name)
  end) (DB.thms "typedLogFieldContract")
