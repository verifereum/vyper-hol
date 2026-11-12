Theory bodyFullBuiltinWordNot
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame exprSimWordBuiltins exprSimHypsDefs
  exprSimUnopProps exprSimUnopCompose gasOutcomeFullCompose
  fragGasSeqPtr fragGasOriginPtr exprSimSource
  emitHelperProps emitHelper compileEnv fragExec venomInst venomState
  finite_map venomExecSemantics builtinSimple vyperValueOperation valueEncoding vyperInterpreter vyperContext
  vyperTypeSystem vyperTyping vyperAST list

Theorem word_not_pre[local]:
  expr_body_pre cenv cx env (Builtin ann Not args) es ==>
  ?e. args = [e] /\ ann = expr_type e /\
      expr_body_pre cenv cx env e es /\
      (is_bool_type ann \/ is_uint256_type ann \/
       is_bytes32_type ann \/ is_flag_type ann)
Proof
  strip_tac >>
  `well_typed_builtin_app ann Not (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >>
  (irule expr_body_pre_builtin_arg >> simp[] >>
   conj_tac >- gvs[expr_body_pre_def] >>
   qexistsl_tac [`expr_type h`, `[h]`, `Not`, `es`] >> simp[])
QED

Theorem word_not_bool_origin_path[local]:
  emit_op ISZERO [x] sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand x s = SOME (bool_to_word b) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ op_taint tn x = {} ==>
  ?t G' tn'.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn') /\
    eval_operand op t = SOME (bool_to_word (~b)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    unop_result cx (BaseT BoolT) Not tys (BoolV b) es = INL (BoolV (~b)) /\
    ?out inst u.
      out = STRING #"%" (toString sa.cs_next_var) /\
      inst = mk_inst sa.cs_next_id ISZERO [x] [out] /\
      u = update_var out (bool_to_word (~b)) s /\
      t = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
      G' = step_prov PG G inst u /\ tn' = step_taint inst s u tn
Proof
  strip_tac >>
  `!out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id ISZERO [x] [out]) s` by
    (gen_tac >> simp[ptrSafeRunTheory.ptr_inst_ok_def,
       ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
     `step_inst 0 ctx (mk_inst sa.cs_next_id ISZERO [x] [out]) s =
       OK (update_var out (bool_to_word (~b)) s)` by
       (simp[step_inst_non_invoke, mk_inst_def] >>
        drule step_ISZERO >> Cases_on `b` >>
        simp[bool_to_word_def, mk_inst_def]) >>
     gvs[mk_inst_def, update_var_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ISZERO [x]
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var))
    (bool_to_word (~b)) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qexistsl_tac [`step_prov PG G inst (update_var (STRING #"%" (toString sa.cs_next_var)) (bool_to_word (~b)) s)`,
    `step_taint inst s (update_var (STRING #"%" (toString sa.cs_next_var)) (bool_to_word (~b)) s) tn`] >>
  conj_tac
  >- (`gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (update_var (STRING #"%" (toString sa.cs_next_var))
          (bool_to_word (~b)) s with vs_inst_idx := SUC s.vs_inst_idx),
         step_prov PG G inst (update_var (STRING #"%" (toString sa.cs_next_var)) (bool_to_word (~b)) s),
         step_taint inst s (update_var (STRING #"%" (toString sa.cs_next_var)) (bool_to_word (~b)) s) tn)` by
        (mp_tac (straight_line_origin_ptr_edge |> Q.INST
           [`i` |-> `inst`, `u` |-> `update_var (STRING #"%" (toString sa.cs_next_var)) (bool_to_word (~b)) s`]) >>
         simp[Abbr `inst`, mk_inst_def] >>
         disch_then irule >>
         simp[GSYM mk_inst_def, is_terminator_def, step_ISZERO,
              bool_to_word_def] >>
         conj_tac
         >- (drule step_ISZERO >> Cases_on `b` >> simp[bool_to_word_def]) >>
         simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
              contextCodegenRelTheory.source_memory_read_ranges_def,
              codegenRelTheory.source_memory_write_ranges_def,
              mk_inst_def]) >>
      `~(update_var (STRING #"%" (toString sa.cs_next_var))
        (bool_to_word (~b)) s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
        simp[update_var_def] >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, unop_result_def,
       evaluate_builtin_def, bool_to_word_def, FLOOKUP_UPDATE]
QED
