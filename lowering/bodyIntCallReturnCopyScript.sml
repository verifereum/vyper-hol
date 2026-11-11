(* Equal-type internal memory returns need size headroom, not address headroom. *)
Theory bodyIntCallReturnCopy
Ancestors
  intCallReturnMem valueCopy intCallResult loweringSlice loweringPosts instIdxIndep
  stmtSimReturn fragExec exprLoweringProps stmtLowering exprLowering
  emitHelper emitHelperProps compileEnv loweringStateRelDefs context valueEncoding
  vyperState vyperTyping venomExecSemantics venomInst venomState
  list rich_list

Theorem internal_return_copy_frag[local]:
  !ctx func cenv cx es ty tv v src dst rpc sa sb bw R.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size tv)) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           val_in_memory tv v (w2n bw) s.vs_memory /\
           ?pc. eval_operand rpc s = SOME pc)
      R
Proof
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `?s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
    expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
    ?pc. eval_operand rpc s = SOME pc`)
  >- (simp[frag_exec_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) sin = OK sout` >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) sin` by fs[stmt_state_rel_def, state_rel_def] >>
  `sout.vs_data_section = sin.vs_data_section` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = sin`
       (mp_tac o AP_TERM ``\z. z.vs_data_section``) >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) sout` by
    (irule immutables_rel_mem_agree >> qexists_tac `sin` >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> simp[regions_disjoint_def] >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  disj1_tac >> qexists_tac `sout` >>
  simp[stmt_state_rel_inst_idx, eval_op_inst_idx] >>
  conj_tac
  >- (irule result_state_memory_frame >> simp[] >> qexists_tac `sin` >>
      simp[local_region_def, lookup_scopes_def] >>
      fs[venom_state_component_equality] >> metis_tac[]) >>
  rename1 `eval_operand rpc sin = SOME ret_pc` >>
  qexists_tac `ret_pc` >>
  drule_all store_result_operand_frame >> simp[]
QED

Theorem compile_internal_return_memory_size_bound_frag:
  !ctx func cenv cx es ty tv v val_op rpc elem_types buf_op sa sb bw.
    compile_internal_return cenv (SOME val_op) rpc 0 ty ty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size tv)) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx ty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx tv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `?s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
    expr_val_rel cx ty v val_op s /\ eval_operand buf_op s = SOME bw`)
  >- (simp[frag_exec_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_store_memory cenv val_op buf_op ty ty sa` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
                     val_in_memory tv v (w2n bw) s.vs_memory /\
                     ?pc. eval_operand rpc s = SOME pc`, `sm`] >>
  simp[] >> conj_tac
  >- (irule internal_return_copy_frag >> simp[] >> metis_tac[]) >>
  irule emit_ret_pc_frag >> qexists_tac `rpc` >> simp[] >>
  rpt strip_tac >>
  gvs[intret_mem_q_def, intret_q_def, result_rel_def,
      intret_vals_match_def, stmt_state_rel_def]
QED
