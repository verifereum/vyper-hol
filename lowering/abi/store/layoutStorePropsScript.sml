(* TOP-LEVEL: checked compatible tuple widening uses the compiler's actual
   bulk-copy path when complete physical layouts agree. Unchanged aggregate
   types use the same theorem. Operand and disjoint-memory frames are kept. *)
Theory layoutStoreProps
Ancestors
  memoryLayoutSource memoryLayoutRel memoryLayoutDefs memoryStoreProps
  fieldStoreComposition fieldAddressProps logBytesStoreProps
  memoryValueDefs memoryValueTyping valueLoadProps valueEncoding typeLayoutProps typedCopyProducer
  vyperEventCompatibility vyperTypeContract vyperContext vyperTypeSystem vyperValue vyperTyping
  context compileVyper compileEnv fragBlockPath fragExec venomState list words arithmetic

Theorem bulk_store_layout_keys:
  !fty aty. (fty = aty \/ tuple_memory_layout_eq fty aty) ==>
    memory_layout_key fty = memory_layout_key aty /\ (is_word_type fty = is_word_type aty)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `fty = aty` >- gvs[] >>
  `tuple_memory_layout_eq fty aty` by fs[] >>
  Cases_on `fty` >> Cases_on `aty` >>
  gvs[tuple_memory_layout_eq_def, memory_layout_key_def, is_word_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem checked_compile_store_memory_bulk_path:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv v dst src cs ret cs' ss dst_addr src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    event_arg_compatible fty aty /\ ~is_word_type fty /\ ~is_bytestring_type fty /\
    (fty = aty \/ tuple_memory_layout_eq fty aty) /\
    compile_store_memory cenv src dst fty aty cs = (ret,cs') /\
    lowered_value_rel aty atv v src ss /\ type_memory_size ftv < dimword(:256) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ value_has_type ftv v /\
      memory_value_rel ftv v (w2n dst_addr) out.vs_memory /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  drule_all bulk_store_layout_keys >> strip_tac >>
  `~is_word_type aty` by fs[] >>
  `value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory` by
    (qpat_x_assum `lowered_value_rel aty atv v src ss` mp_tac >> simp[lowered_value_rel_def]) >>
  `value_has_type ftv v` by
    (drule_all (cj 1 event_arg_compatible_value_has_type) >> simp[]) >>
  `val_wf ftv v` by (irule value_has_type_val_wf >> simp[]) >>
  `memory_layout_rel ftv atv` by
    (drule_all memory_layout_key_evaluated >> simp[]) >>
  `memory_value_rel ftv v (w2n src_addr) ss.vs_memory` by
    (drule_all memory_layout_rel_value >> simp[]) >>
  `type_memory_bytes cenv fty = type_memory_size ftv` by
    (mp_tac (Q.SPECL [`tops`, `cenv`, `fty`, `ftv`] type_memory_bytes_evaluated) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `v`, `dst`, `src`,
    `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_store_memory_bulk_path) >>
  impl_tac >- simp[] >> strip_tac >> qexists_tac `out` >> simp[] >>
  rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >> simp[ADD_COMM]
QED

Theorem checked_compile_log_bulk_field_path:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv v buf src offset
      cs ret cs' ss buf_addr src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    event_arg_compatible fty aty /\ ~is_word_type fty /\ ~is_bytestring_type fty /\
    (fty = aty \/ tuple_memory_layout_eq fty aty) /\
    compile_log_store_data cenv [(src,aty)] [fty] buf offset cs = (ret,cs') /\
    lowered_value_rel aty atv v src ss /\ type_memory_size ftv < dimword(:256) /\
    eval_operand buf ss = SOME buf_addr /\ eval_operand src ss = SOME src_addr /\
    w2n buf_addr + offset < dimword(:256) /\
    src <> Var (STRING #"%" (toString cs.cs_next_var)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ value_has_type ftv v /\
      memory_value_rel ftv v (w2n buf_addr + offset) out.vs_memory /\
      (!arg_op. arg_op <> Var (STRING #"%" (toString cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v other_offset.
        memory_value_rel other_tv other_v other_offset ss.vs_memory /\ val_wf other_tv other_v /\
        (other_offset + type_memory_size other_tv <= w2n buf_addr + offset \/
          w2n buf_addr + offset + type_memory_size ftv <= other_offset) ==>
        memory_value_rel other_tv other_v other_offset out.vs_memory)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_log_store_field_contains >> strip_tac >>
  drule emit_field_address_code >> strip_tac >> `src <> dst` by simp[] >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) emit_field_address_path >>
  rename1 `fragment_path ctx func ss addressed` >>
  `lowered_value_rel aty atv v src addressed` by
    (qpat_x_assum `!ty tv v arg_op. _` (qspecl_then [`aty`, `atv`, `v`, `src`] mp_tac) >> simp[]) >>
  `eval_operand src addressed = SOME src_addr` by
    (qpat_x_assum `!arg_op. _` (qspec_then `src` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `fty`, `aty`, `ftv`, `atv`, `v`, `dst`, `src`, `mid`, `ret`, `cs'`, `addressed`,
    `buf_addr + n2w offset`, `src_addr`] checked_compile_store_memory_bulk_path) >>
  impl_tac >- simp[] >> strip_tac >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `addressed` >> simp[]) >>
  `memory_value_rel ftv v (w2n buf_addr + offset) out.vs_memory` by
    (qpat_x_assum `memory_value_rel ftv v _ out.vs_memory` mp_tac >> simp[log_field_address]) >>
  qexists_tac `out` >> simp[log_field_address] >> rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`other_tv`, `other_v`, `other_offset`] mp_tac) >> impl_tac
  >- (qpat_x_assum `memory_value_rel other_tv other_v other_offset ss.vs_memory /\ _`
        (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
      asm_simp_tac bool_ss [log_field_address] >> decide_tac) >> simp[]
QED
