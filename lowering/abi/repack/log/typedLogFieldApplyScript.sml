(* TOP-LEVEL: apply a field type contract directly to a saved argument's
   safety predicate, retaining its actual compiler cuts and name interval. *)
Theory typedLogFieldApply
Ancestors
  typedCopyStateFrame
  typedLogArgs typedLogFieldContract typedSArrayDynInvariant typedCopyContract
  valueLoadProps memoryValueDefs valueEncoding abiStaticLoopCode
  context stmtLowering compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem log_field_type_contract_path:
  !ctx func cenv fty aty ftv atv src buf field_offset cs ret cs' ss v buf_addr.
    log_field_type_contract ctx func cenv fty aty ftv atv /\
    compile_log_store_data cenv [(src,aty)] [fty] buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    lowered_value_rel aty atv v src ss /\ eval_operand buf ss = SOME buf_addr /\
    w2n buf_addr + field_offset + type_memory_size ftv < dimword(:256) /\
    log_arg_safe src aty atv ss (w2n buf_addr + field_offset) (type_memory_size ftv) /\
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
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `lowered_value_rel _ _ _ _ ss` (mp_tac o REWRITE_RULE [lowered_value_rel_def]) >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qx_choose_then `src_word` strip_assume_tac)) >>
  qpat_x_assum `log_field_type_contract _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [log_field_type_contract_def]) >>
  disch_then (qspecl_then [`buf`, `src`, `field_offset`, `cs`, `ret`, `cs'`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`ss`, `v`, `buf_addr`, `src_word`] mp_tac) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        DISCH_TAC >> qpat_x_assum `log_arg_safe _ _ _ _ _ _` (mp_tac o REWRITE_RULE [log_arg_safe_def]) >>
        impl_tac >- first_assum MATCH_ACCEPT_TAC >> disch_then (qspec_then `src_word` mp_tac) >> simp[]]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed saved-argument field contract application: " ^ name)
  end) (DB.thms "typedLogFieldApply")
