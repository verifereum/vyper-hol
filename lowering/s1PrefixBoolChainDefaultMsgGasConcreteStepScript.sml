(* Concrete machine and ghost updates at the reached GAS cursor. *)
Theory s1PrefixBoolChainDefaultMsgGasConcreteStep
Ancestors
  msgGasSim gasSummary gasOracleReplay gasExplicitSites gasShadowState
  fragFuel fragGasSeqPtr fragGasOriginPtr memSafeRun ptrSafeRun unitTransformDefs
  contextCodegenRel codegenRel
  venomInst venomState venomExecSemantics vyperAST vyperInterpreter vyperState
  vyperTypeSystem vyperStorageFootprint finite_map list

Theorem bool_chain_default_msggas_step_concrete:
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  gas_shadow_function func shadow_func /\
  ~s.vs_halted /\ s.vs_gas_readings = w::readings /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) /\
  lookup_block shadow_lbl shadow_func.fn_blocks = SOME shadow_bb /\
  get_instruction shadow_bb shadow_idx = SOME (mk_inst id GASPRICE [] [out]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn (mk_inst id GAS [] [out]) s) ==>
  ?t G1 tn1.
    (!tail. bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
      (read_result cx)
      (es with gas_obs := gas_explicit [T] s.vs_gas_readings ++ tail) =
      (INL (IntV (&w2n w)), es with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G,tn) [T] (OK t,G1,tn1)) /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ t.vs_gas_readings = readings /\
    eval_operand (Var out) t = SOME w /\
    G1 = step_prov PG G (mk_inst id GAS [] [out])
           (update_var out w (s with vs_gas_readings := readings)) /\
    tn1 = step_taint (mk_inst id GAS [] [out]) s
            (update_var out w (s with vs_gas_readings := readings)) tn /\
    t = ((update_var out w (s with vs_gas_readings := readings))
           with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id GAS [] [out]` >>
  qabbrev_tac `j = mk_inst id GASPRICE [] [out]` >>
  `MEM i (fn_insts func) /\ MEM j (fn_insts shadow_func)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  `gas_shadow_inst i j /\ i.inst_opcode = GAS /\ j.inst_opcode = GASPRICE` by
    simp[Abbr `i`, Abbr `j`, gas_shadow_inst_def, mk_inst_def] >>
  `(func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx` by
    (drule_all gas_explicit_sites_classify >> simp[]) >>
  qabbrev_tac `u = update_var out w (s with vs_gas_readings := readings)` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, exec_gas_def, mk_inst_def] >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
               `step_prov PG G i u`, `step_taint i s u tn`] >>
  simp[] >> conj_tac
  >- simp[gas_explicit_def, gas_prefix_def, msg_gas_source] >>
  reverse conj_tac
  >- simp[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `gas_origin_ptr_edge (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s,G,tn) [T] (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
                   step_prov PG G i u, step_taint i s u tn)` by
    (`gas_origin_ptr_edge (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) (if i.inst_opcode = GAS then
                    [(func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx]
                  else [])
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
         step_prov PG G i u, step_taint i s u tn)` suffices_by simp[] >>
     `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> simp[]) >>
     irule straight_line_origin_ptr_edge >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          inst_dload_in_section_def, dalloca_no_wrap_def]) >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`, update_var_def]
QED
