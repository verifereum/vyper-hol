(* TOP-LEVEL: recursive fixed-array repacking preserves the complete sparse
   source and establishes the target layout. Compatible element defaults
   agree, so omitted source slots retain their meaning in the target. *)
Theory typedSArraySource
Ancestors
  vyperEventArgCompat
  typedCopyStateFrame typedCopyLoopStateFrame
  typedSArrayPath typedArrayLoopValues typedArrayCopyMemory typedSArrayDynInvariant
  typedSArrayLoop typedCopyContract memoryValueDefs valueEncoding vyperEventCompatibility
  abiBytestringCode abiStaticLoopCode context compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue vyperTyping
  fragBlockPath fragExec venomState venomInst list alist words arithmetic

Theorem checked_sarray_copy_memory_path:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs' after child_names
      sparse ss dst_addr src_addr exit_bb.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\ fn_has_code cs cs' func /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 7) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
      (Var (compiler_var_name cs.cs_next_var 5)) ftv atv (sarray_copy_start cenv dst fty src aty copy_count cs) after /\
    copy_count < dimword(:256) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) /\
    value_has_type (ArrayTV atv (Fixed copy_count)) (ArrayV (SArrayV sparse)) /\
    memory_value_rel (ArrayTV atv (Fixed copy_count)) (ArrayV (SArrayV sparse)) (w2n src_addr) ss.vs_memory /\
    w2n src_addr + type_memory_size (ArrayTV atv (Fixed copy_count)) < dimword(:256) /\
    w2n dst_addr + type_memory_size (ArrayTV ftv (Fixed copy_count)) < dimword(:256) /\
    (w2n src_addr + type_memory_size (ArrayTV atv (Fixed copy_count)) <= w2n dst_addr \/
      w2n dst_addr + type_memory_size (ArrayTV ftv (Fixed copy_count)) <= w2n src_addr) /\
    lookup_block (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel (ArrayTV ftv (Fixed copy_count)) (ArrayV (SArrayV sparse)) (w2n dst_addr) out.vs_memory /\
      memory_value_rel (ArrayTV atv (Fixed copy_count)) (ArrayV (SArrayV sparse)) (w2n src_addr) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_size (ArrayTV ftv (Fixed copy_count)) <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all memory_fixed_array_elements >> strip_tac >>
  drule (CONJUNCT1 event_arg_compatible_defaults) >>
  disch_then (qspecl_then [`type_env tops`, `ftv`, `atv`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `w2n src_addr + type_memory_size _ < _` (ASSUME_TAC o REWRITE_RULE [type_memory_size_def]) >>
  qpat_x_assum `w2n dst_addr + type_memory_size _ < _` (ASSUME_TAC o REWRITE_RULE [type_memory_size_def]) >>
  qpat_x_assum `_ \/ _` (ASSUME_TAC o REWRITE_RULE [type_memory_size_def]) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`, `after`, `child_names`,
    `\j. case ALOOKUP sparse j of NONE => default_value atv | SOME v => v`,
    `ss`, `dst_addr`, `src_addr`, `exit_bb`] checked_sarray_copy_path) >> BETA_TAC >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_x_assum `array_copy_memory_inv _ _ _ _ _ _ _ _ _` mp_tac >>
  PURE_REWRITE_TAC [array_copy_memory_inv_def] >> strip_tac >>
  `memory_value_rel (ArrayTV ftv (Fixed copy_count)) (ArrayV (SArrayV sparse)) (w2n dst_addr) out.vs_memory` by
    (PURE_REWRITE_TAC [array_copy_fixed_layout] >>
     qpat_assum `default_value ftv = _` (fn th => PURE_REWRITE_TAC [th]) >> first_assum MATCH_ACCEPT_TAC) >>
  `memory_value_rel (ArrayTV atv (Fixed copy_count)) (ArrayV (SArrayV sparse)) (w2n src_addr) out.vs_memory` by
    (PURE_REWRITE_TAC [array_copy_fixed_layout] >> first_assum MATCH_ACCEPT_TAC) >>
  drule array_copy_fixed_frame >> DISCH_TAC >>
  qexists_tac `out` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
