(* TOP-LEVEL: execute a tuple's first field from its complete source
   layout, retaining the source tail for the remaining compiler action. *)
Theory typedFieldsReady
Ancestors
  typedCopyStateFrame
  typedFieldsStep typedFieldsSafety typedFieldsMemory typedCopyTypeContract
  typedCopyContract typedSArrayDynInvariant abiStaticLoopCode
  memoryValueDefs valueEncoding vyperTyping vyperValue
  context compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem typed_fields_copy_head_ready:
  !ctx func cenv dst src fty fts aty ats ftv ftvs atv atvs dst_off src_off
      cs ret cs' ss v vs dst_addr src_addr.
    compile_typed_copy_fields cenv dst src (fty::fts) (aty::ats) dst_off src_off cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func /\
    typed_copy_type_contract ctx func cenv fty aty ftv atv /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) /\
    values_have_types (atv::atvs) (v::vs) /\
    memory_tuple_rel (atv::atvs) (v::vs) (w2n src_addr + src_off) ss.vs_memory /\
    w2n src_addr + src_off + type_memory_size (TupleTV (atv::atvs)) < dimword(:256) /\
    w2n dst_addr + dst_off + type_memory_size (TupleTV (ftv::ftvs)) < dimword(:256) /\
    (w2n src_addr + src_off + type_memory_size (TupleTV (atv::atvs)) <= w2n dst_addr + dst_off \/
      w2n dst_addr + dst_off + type_memory_size (TupleTV (ftv::ftvs)) <= w2n src_addr + src_off) ==>
    ?after_child mid.
      compile_typed_copy_fields cenv dst src fts ats
        (dst_off + type_memory_bytes cenv fty) (src_off + type_memory_bytes cenv aty) after_child = (ret,cs') /\
      fn_has_code after_child cs' func /\ cs.cs_next_var <= after_child.cs_next_var /\
      after_child.cs_next_var <= cs'.cs_next_var /\
      fragment_path ctx func ss mid /\ copy_state_frame ss mid /\ mid.vs_current_bb = after_child.cs_current_bb /\
      mid.vs_inst_idx = LENGTH after_child.cs_current_insts /\ ~mid.vs_halted /\
      memory_value_rel ftv v (w2n dst_addr + dst_off) mid.vs_memory /\
      memory_tuple_rel atvs vs (w2n src_addr + src_off + type_memory_size atv) mid.vs_memory /\
      array_copy_frame ftv 1 (w2n dst_addr + dst_off) ss.vs_memory mid.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (after_child.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op mid = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`atv`, `atvs`, `ftv`, `ftvs`, `w2n (src_addr:bytes32) + src_off`,
    `w2n (dst_addr:bytes32) + dst_off`, `dimword(:256)`] tuple_copy_parts_safety) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`src_addr`, `src_off`, `atv`] tuple_copy_field_pointer) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`dst_addr`, `dst_off`, `ftv`] tuple_copy_field_pointer) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `src`, `fty`, `fts`, `aty`, `ats`, `ftv`, `atv`,
    `dst_off`, `src_off`, `cs`, `ret`, `cs'`, `ss`, `v`, `dst_addr`, `src_addr`]
    typed_fields_copy_step_path) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    fs[memory_value_rel_def, value_has_type_def] >> NO_TAC]) >>
  disch_then (qx_choose_then `after_child` (qx_choose_then `mid` strip_assume_tac)) >>
  qpat_x_assum `w2n (dst_addr + n2w dst_off) = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  `memory_tuple_rel atvs vs (w2n src_addr + src_off + type_memory_size atv) mid.vs_memory` by
    (mp_tac (Q.SPECL [`atv`, `atvs`, `v`, `vs`, `w2n (src_addr:bytes32) + src_off`, `ftv`, `ftvs`,
      `w2n (dst_addr:bytes32) + dst_off`, `ss.vs_memory`, `mid.vs_memory`] tuple_copy_source_tail) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qexistsl_tac [`after_child`, `mid`] >> asm_rewrite_tac []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete-source tuple field execution: " ^ name)
  end) (DB.thms "typedFieldsReady")
