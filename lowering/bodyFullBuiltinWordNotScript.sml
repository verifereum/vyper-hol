Theory bodyFullBuiltinWordNot
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame exprSimWordBuiltins exprSimHypsDefs
  exprSimUnopProps exprSimUnopCompose gasOutcomeFullCompose
  fragGasSeqPtr fragGasOriginPtr exprSimSource
  emitHelperProps emitHelper compileEnv fragExec venomInst venomState exprLowering
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

Theorem word_not_typed_suffix[local]:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
   is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ op_taint tn x = {} ==>
  ?v' t G' tn'.
    unop_result cx ann Not tys v es = INL v' /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn') /\
    eval_operand op t = SOME (typed_val_to_w256 tv v') /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN ``?k xs v' w'.
    emit_op k xs sa = (op,sb) /\
    unop_result cx ann Not tys v es = INL v' /\
    w' = typed_val_to_w256 tv v' /\
    (k = ISZERO \/ k = NOT \/ k = XOR) /\
    EVERY (\a. op_taint tn a = {}) xs /\
    (!out. step_inst_base (mk_inst sa.cs_next_id k xs [out]) s =
      OK (update_var out w' s))``
    (qx_choose_then `k` (qx_choose_then `xs`
      (qx_choose_then `v'` (qx_choose_then `w'`
        (map_every assume_tac o CONJUNCTS)))))
  >- (drule not_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     Cases_on `v` >>
     gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
       type_to_int_bound_def, typed_val_to_w256_def, val_to_w256_def,
       compile_invert_def, vyperValueTheory.evaluate_type_def]
     >~ [`emit_op ISZERO`]
     >- (qexistsl_tac [`ISZERO`, `[x]`] >> simp[] >> gen_tac >>
         drule step_ISZERO >> Cases_on `b` >> simp[bool_to_word_def])
     >~ [`i2w i`]
     >- (qexistsl_tac [`NOT`, `[x]`] >> simp[] >> gen_tac >>
         `~(i < 0)` by intLib.COOPER_TAC >>
         drule step_NOT >> simp[integer_wordTheory.i2w_def])
     >~ [`LENGTH bs = 32`]
     >- (qexistsl_tac [`NOT`, `[x]`] >>
         simp[PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes] >>
         gen_tac >> drule step_NOT >> simp[PAD_RIGHT]) >>
     qmatch_asmsub_abbrev_tac `emit_op XOR [x; mask]` >>
     qexistsl_tac [`XOR`, `[x; mask]`] >>
     simp[Abbr `mask`, ptrDisciplineTheory.op_taint_def] >>
     gen_tac >> drule_all flag_not_xor >> disch_then (rewrite_tac o single o GSYM) >>
     irule step_XOR >> simp[eval_operand_def]) >>
  `!out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id k xs [out]) s` by
    (gen_tac >> simp[ptrSafeRunTheory.ptr_inst_ok_def,
       ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
     `step_inst 0 ctx (mk_inst sa.cs_next_id k xs [out]) s =
       OK (update_var out w' s)` by
       (qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
        simp[step_inst_non_invoke, mk_inst_def] >>
        metis_tac[mk_inst_def]) >>
     gvs[mk_inst_def, update_var_def, EVERY_MEM] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id k xs
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var out w' s` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qexistsl_tac [`v'`, `z`, `step_prov PG G inst u`,
    `step_taint inst s u tn`] >> simp[] >>
  conj_tac
  >- (`gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK z, step_prov PG G inst u, step_taint inst s u tn)` by
       (`k <> GAS` by
          (qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >> simp[]) >>
        mp_tac (straight_line_origin_ptr_edge |> Q.INST
         [`i` |-> `inst`, `u` |-> `u`]) >>
        simp[Abbr `inst`, mk_inst_def] >> disch_then irule >>
        simp[GSYM mk_inst_def, Abbr `u`, Abbr `z`, Abbr `out`] >>
        gvs[is_terminator_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
      `~z.vs_halted` by simp[Abbr `z`, Abbr `u`, update_var_def] >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
    comp_ignore_bind_def, comp_return_def, emit_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    Abbr `z`, Abbr `u`, Abbr `out`]
QED
