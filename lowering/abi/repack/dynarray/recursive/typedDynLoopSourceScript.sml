(* TOP-LEVEL: the checked recursive dynamic-array parent copies its complete
   source into the declared target, assuming the actual child compiler's
   typed contract. Strides and name ranges come from checked metadata and code. *)
Theory typedDynLoopSource
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame
  typedDynLoopPath typedDynLoopPrefix typedDynChildContract typedCopyContract
  typedDynLoopCode typedDynLoopNames typedSArrayDynInvariant typedArrayCopyMemory
  dynCopyPrefixPath typedArrayLoopNames abiBytestringCode abiStaticLoopCode
  bytesCopyProps memoryValueDefs valueEncoding valueEncodingProps context compileEnv
  compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_compile_copy_dynarray_path:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv capacity src aty atv src_capacity vs cs ret cs' after child_names ss dst_addr src_addr exit_bb.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\ fty <> aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    src_capacity <= capacity /\ capacity < dimword(:256) /\
    compile_copy_dynarray_typed cenv dst fty capacity src aty cs = (ret,cs') /\ fn_has_code cs cs' func /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 12) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
      (Var (compiler_var_name cs.cs_next_var 10)) ftv atv (dynarray_copy_start cenv dst fty capacity src aty cs) after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    value_has_type (ArrayTV atv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) /\
    memory_value_rel (ArrayTV atv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) (w2n src_addr) ss.vs_memory /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (13 + child_names)) /\
    w2n src_addr + type_memory_size (ArrayTV atv (Dynamic src_capacity)) < dimword(:256) /\
    w2n dst_addr + type_memory_size (ArrayTV ftv (Dynamic capacity)) < dimword(:256) /\
    (w2n src_addr + type_memory_size (ArrayTV atv (Dynamic src_capacity)) <= w2n dst_addr \/
      w2n dst_addr + type_memory_size (ArrayTV ftv (Dynamic capacity)) <= w2n src_addr) /\
    lookup_block (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel (ArrayTV ftv (Dynamic capacity)) (ArrayV (DynArrayV vs)) (w2n dst_addr) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_size (ArrayTV ftv (Dynamic capacity)) <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (13 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ fty = aty)` by simp[] >>
  drule_all compile_copy_dynarray_contains_child >> strip_tac >>
  `fn_has_code after (dynarray_copy_finish cs after) func` by
    (qpat_assum `cs' = _` (fn th => PURE_REWRITE_TAC [SYM th]) >> first_assum MATCH_ACCEPT_TAC) >>
  drule array_copy_dynamic_values >> strip_tac >> `LENGTH vs <= capacity` by decide_tac >>
  `LENGTH vs < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`atv`, `src_capacity`, `LENGTH (vs:value list)`, `src_addr`] array_copy_dynamic_payload_bounds) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`ftv`, `capacity`, `LENGTH (vs:value list)`, `dst_addr`] array_copy_dynamic_payload_bounds) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`ftv`, `atv`, `src_capacity`, `capacity`, `LENGTH (vs:value list)`,
    `w2n (src_addr:bytes32)`, `w2n (dst_addr:bytes32)`] array_copy_dynamic_payload_separated) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ftv`, `atv`, `src_capacity`, `capacity`, `w2n (src_addr:bytes32)`, `w2n (dst_addr:bytes32)`]
    array_copy_dynamic_header_separated) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  `EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 5)` by
    (qpat_assum `EVERY _ (compiler_var_names cs.cs_next_var (13 + child_names))`
       (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
     simp_tac bool_ss [EVERY_CONJ] >> conj_tac >> irule compiler_var_names_avoid_prefix >>
     qexists_tac `13 + child_names` >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) dynarray_copy_prefix_source_path >>
  `array_copy_prefix atv (\j. EL j vs) (LENGTH vs) (w2n (src_addr + 32w)) entry_ss.vs_memory` by
    (qpat_x_assum `w2n (src_addr + 32w) = _` (fn th => simp_tac bool_ss [th]) >> first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`, `capacity`, `src`, `aty`, `atv`,
    `cs`, `after`, `child_names`, `\j. EL j vs`, `LENGTH (vs:value list)`, `src_addr + 32w`, `dst_addr + 32w`,
    `entry_ss`, `exit_bb`] checked_dynarray_copy_payload_path) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, asm_simp_tac bool_ss []]) >> strip_tac >>
  qpat_x_assum `array_copy_memory_inv _ _ _ _ _ _ _ _ _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ftv`, `atv`, `vs`, `capacity`, `w2n (src_addr:bytes32) + 32`, `w2n (dst_addr:bytes32)`,
    `ss`, `entry_ss`, `out.vs_memory`] dynarray_copy_complete_layout_frame) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC]) >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `5`, `8 + child_names`, `ss`, `entry_ss`, `out`] compiler_operands_frame_ranges) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (ASSUME_TAC o SIMP_RULE (srw_ss()) [ADD_ASSOC]) >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `entry_ss` >> simp[]) >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `entry_ss` >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
