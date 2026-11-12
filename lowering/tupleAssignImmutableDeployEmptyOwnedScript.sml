(* Empty tuple production retains its physical envelope at the gas endpoint. *)
Theory tupleAssignImmutableDeployEmptyOwned
Ancestors
  tupleAssignImmutableDeployConstructors exprSimAggregates
  exprSimBufferEmptyExec exprSimBuffer exprSimProps exprSimHypsDefs
  exprSimDefs exprSimSource exprSimValues exprLoweringProps
  loweringStateRelDefs loweringPosts gasNormalPrefix gasSummary gasOutcome
  gasContext fragGasMode fragGasPath fragGasSeq fragExec
  exprSimAggregateLayout exprSimAggregateSource exprSimAlloc
  builtinSimple emitHelper context compileEnv valueEncoding valueEncodingDefs
  vyperInterpreter vyperTypeSystem venomState venomInstProofs venomExecSemantics
  vyperState vyperContext vyperValueOperation exprLowering allocLimits
  exprSimConvert exprSimHyps vyperValue list rich_list

Theorem tuple_immutable_empty_owned:
  expr_sim_pre cenv cx env (TypeBuiltin ann Empty target args) es /\
  evaluate_type (get_tenv cx) target = SOME (TupleTV tvs) /\
  compile_expr cenv ty (TypeBuiltin ann Empty target args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (TypeBuiltin ann Empty target args)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?buf. vv = LocatedValue ann (base_ptr buf) /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_expr cx (TypeBuiltin ann Empty target args)) (es,s0)
      (\res ee r. ?tv w. res = INL tv /\
        vv_post ctx func cenv cx (TypeBuiltin ann Empty target args)
          es sa sb s0 ee tv vv r /\
        r.vs_current_bb = sb.cs_current_bb /\
        r.vs_inst_idx = LENGTH sb.cs_current_insts /\
        eval_operand buf.buf_operand r = SOME w /\
        (type_memory_size_list tvs = 0 \/
         ?aid b n. FLOOKUP r.vs_allocas aid = SOME (b,n) /\
           sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
           b <= w2n w /\ w2n w + type_memory_size_list tvs <= b+n /\
           (!name lb lsz. local_region cenv ee.scopes r name lb lsz ==>
             b+n <= lb \/ lb+lsz <= b)))
      (\res ee exit. expr_exit res exit)
Proof
  strip_tac >>
  `!gs. args = [] /\
    eval_expr cx (TypeBuiltin ann Empty target args) (es with gas_obs := gs) =
      (INL (Value (default_value (TupleTV tvs))),es with gas_obs := gs)` by
    (gen_tac >>
     Cases_on `eval_expr cx (TypeBuiltin ann Empty target args) (es with gas_obs := gs)` >>
     rename1 `eval_expr _ _ _ = (res,ee)` >>
     `expr_vv_res_ok res` by (fs[gas_admissible_def] >> metis_tac[]) >>
     reverse (Cases_on `res`)
     >- (rename1 `INR exc` >>
         `(do r <- eval_expr cx (TypeBuiltin ann Empty target args); read_result cx r od)
            (es with gas_obs := gs) = (INR exc,ee)` by simp[bind_def] >>
         drule eval_expr_empty >> gvs[expr_vv_res_ok_def, expr_res_ok_def]) >>
     drule eval_expr_type_builtin_value >> strip_tac >> gvs[] >>
     `(do r <- eval_expr cx (TypeBuiltin ann Empty target args); read_result cx r od)
       (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def,read_result_def,return_def] >>
     drule eval_expr_empty >> simp[expr_res_ok_def] >> strip_tac >> gvs[]) >>
  first_assum (qspec_then `[]` strip_assume_tac) >> gvs[] >>
  `ann = target` by
    gvs[expr_sim_pre_def,well_typed_expr_def,type_builtin_result_ok_def] >>
  `~is_word_type target` by
    (Cases_on `target` >> gvs[is_word_type_def,evaluate_type_def,AllCaseEqs()]) >>
  gvs[compile_expr_type_builtin_dispatch,Once compile_expr_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `type_memory_bytes cenv ann < dimword (:256)` by
    (gvs[expr_sim_pre_def,alloc_limits_expr_def] >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  `gas_path ctx func s0 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
     t.vs_current_bb = sb.cs_current_bb` by suspend "gas" >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`t.vs_gas_readings`,`LENGTH sb.cs_current_insts`,`[]`] mp_tac) >> simp[NoAsms]) >>
  qexists `buf` >> simp[] >>
  simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl [`INL (Value (default_value (TupleTV tvs)))`,`es`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac >- simp[gas_marked_exec_def,gas_marked_path_def] >>
  simp[] >> conj_tac >- suspend "value" >>
  `type_memory_bytes cenv ann = type_memory_size_list tvs` by
    (drule_all expr_sim_inv_memory_size >> simp[type_memory_size_def]) >>
  fs[] >>
  disj2_tac >> qexistsl [`sa.cs_next_id`,`w2n w`,`type_memory_size_list tvs`] >> simp[] >>
  rpt strip_tac >>
  `local_region cenv es.scopes t name lb lsz` by
    gvs[local_region_def,eval_operand_def,lookup_var_def] >>
  `local_region cenv es.scopes s0 name lb lsz` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def,state_rel_def]) >>
     qexistsl [`sa`,`es.scopes`,`t`] >> gvs[local_region_def,eval_operand_def,lookup_var_def]) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >> simp[]
QED

Resume tuple_immutable_empty_owned[gas]:
  qmatch_asmsub_abbrev_tac `compile_builtin_empty_complex sz header sa` >>
  qpat_x_assum `Abbrev (header = _)` kall_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `!n pop sa sb. compile_zero_words pop n sa = ((),sb) ==>
     sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
     EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (Induct_on `n`
     >- simp[compile_zero_words_def,comp_return_def,emitted_insts_def] >>
     rpt gen_tac >>
     simp[Once compile_zero_words_def,comp_bind_def,comp_ignore_bind_def] >>
     pairarg_tac >> rename1 `compile_zero_words pop n si = (u,sm)` >>
     Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     gvs[emit_op_def,emit_void_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
     qpat_x_assum `sm.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     `!a b:num. a - (a+b) = 0 /\ a - (a+b+1) = 0` by decide_tac >>
     simp[emitted_insts_def,DROP_APPEND,EVERY_APPEND] >>
     fs[emitted_insts_def,venomInstTheory.mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_builtin_empty_complex _ _ _ = _` mp_tac >>
     simp[compile_builtin_empty_complex_def,comp_bind_def,comp_return_def] >>
     pairarg_tac >> rename1 `compile_alloc_buffer sz sa = (ba,sm)` >>
     simp[] >> Cases_on `header` >>
     simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     pairarg_tac >> rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >>
     strip_tac >> gvs[]
     >- (gvs[compile_alloc_buffer_def,emit_op_def,emit_void_def,comp_bind_def,
           comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
         simp[emitted_insts_def,DROP_APPEND1,venomInstTheory.mk_inst_def]) >>
     first_x_assum drule >> strip_tac >>
     `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
        EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm)` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[compile_alloc_buffer_def,emit_op_def,comp_bind_def,comp_return_def,
          comp_ignore_bind_def,fresh_id_def,fresh_var_def,emit_def] >>
        strip_tac >> gvs[] >>
        simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND,venomInstTheory.mk_inst_def]) >>
     `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
       (irule emitted_insts_append >> simp[]) >> simp[EVERY_APPEND]) >>
  `t.vs_current_bb = s0.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts sa sb` >> simp[] >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow,step_inst_non_invoke]) >>
  gvs[fn_has_code_def,rich_listTheory.IS_PREFIX_APPEND] >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions)` by
    simp[emitted_insts_def,rich_listTheory.DROP_APPEND1] >>
  drule_all tuple_run_inst_seq_gas_path >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  simp[emitted_insts_def]
QED

Resume tuple_immutable_empty_owned[value]:
  once_rewrite_tac[GSYM (Q.INST [`gs` |-> `[]`] vv_post_initial_gas)] >>
  drule_all empty_type_default_memory >> strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin ann Empty ann []`, `p` |-> `base_ptr buf`]
      (SPEC_ALL buffer_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[base_ptr_def,valueEncodingProofsTheory.val_wf_default_value_proof] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
      strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ b len` drule >>
      simp[regions_disjoint_def] >> strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[val_footprint_le,valueEncodingProofsTheory.val_wf_default_value_proof] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s0 n lb lsz` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def,state_rel_def]) >>
     qexistsl [`sa`,`es.scopes`,`t`] >> simp[]) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >>
  decide_tac
QED

Finalise tuple_immutable_empty_owned
