(* Memory-safe straight-line internal return branches. *)
Theory intCallReturnDirectBranchesMem
Ancestors
  fragExecMem intCallReturnMem stmtSimReturnWiden bodyDeclMemoryCore
  bodyMemAggregateStore valueCopyBytes valueCopy stmtLowering typedMemoryCopy
  typedCopyDomain vyperTypeSystem
  intCallResult stmtSimReturn loweringSlice vyperState vyperTyping instIdxIndep
  emitHelper emitHelperProps compileEnv exprLowering exprLoweringProps
  fragExec memSafeRun instMemFrontier venomMemDefs venomExecSemantics
  venomInst venomState list rich_list exprSimBufferStore valueEncodingProps
  exprSimDefs exprSimMemDefs exprSimProps loweringPosts loweringStateRelDefs context valueEncoding unitTransformDefs contextCodegenRel codegenRel

Theorem emit_ret_pc_frag_mem:
  !ctx sm sb rpc P Q R.
    emit_inst RET [rpc] [] sm = ((),sb) /\
    (!s. P s ==> (?pc. eval_operand rpc s = SOME pc) /\
                 R (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s)) ==>
    frag_exec_mem ctx sm sb P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[frag_exec_mem_def] >> rpt strip_tac >> disj2_tac >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `0` >>
  simp[run_from_def, Once run_block_non_phis_def, step_inst_non_invoke,
       mk_inst_def, step_inst_base_opcode_eqs, eval_operands_def,
       exit_result_def] >>
  simp[mem_safe_run_def, Once run_block_non_phis_def,
       Once mem_safe_block_def, mem_safe_step_non_invoke,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def,
       mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       eval_operands_def] >>
  simp[Once run_block_non_phis_def, step_inst_non_invoke,
       mk_inst_def, step_inst_base_opcode_eqs, eval_operands_def]
QED

Theorem return_store_memory_mem_ok[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type ty /\ ~is_bytestring_type ty ==> !sw. eval_operand src s = SOME sw ==>
     type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >> gvs[]) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory tv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  Cases_on `is_bytestring_type ty`
  >- (`?len. mload (w2n sw) s = n2w len /\
              val_store_size tv v = 32 + 32 * word_size len` by
        metis_tac[buffer_typed_bytestring_header] >>
      `w2n sw + val_store_size tv v <= s.vs_alloca_next` by
        (fs[expr_store_bound_def] >>
         qpat_x_assum `!tv'. _` (qspec_then `tv` mp_tac) >> simp[]) >>
      irule body_typed_store_memory_mem_ok >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
      simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
      simp[] >> qexists_tac `v` >> simp[] >> first_assum ACCEPT_TAC) >>
  Cases_on `type_memory_size tv = 0`
  >- gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
         emitted_insts_def, run_inst_seq_mem_ok_def] >>
  irule body_typed_store_memory_mem_ok >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[] >> qexists_tac `v` >> simp[] >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  `w2n sw + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem compile_internal_return_equal_mem[local]:
  !ctx func cenv cx es ty tv v val_op rpc elem_types buf_op sa sb bw.
    compile_internal_return cenv (SOME val_op) rpc 0 ty ty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    w2n bw + type_memory_size tv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size tv)) ==>
    frag_exec_mem ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx ty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           w2n bw + type_memory_size tv <= s.vs_alloca_next /\
           expr_store_bound cx ty v val_op s /\
           (~is_word_type ty /\ ~is_bytestring_type ty ==> !sw. eval_operand val_op s = SOME sw ==>
              type_memory_size tv = 0 \/
              w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx tv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `?s0. stmt_state_rel ctx func cenv cx (es with scopes := []) s0 /\
                          expr_val_rel cx ty v val_op s0 /\
                          eval_operand buf_op s0 = SOME bw`)
  >- (simp[frag_exec_mem_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_store_memory cenv val_op buf_op ty ty sa` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ s0`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`cenv`, `val_op`, `buf_op`, `ty`, `sa`, `sm`, `s0`,
               `get_tenv cx`, `tv`, `v`, `w`, `bw`]
    mp_tac compile_store_memory_run >>
  impl_tac >- simp[] >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  irule frag_exec_mem_seq >>
  qexistsl_tac [`\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
                     val_in_memory tv v (w2n bw) s.vs_memory /\
                     ?pc. eval_operand rpc s = SOME pc`, `sm`] >>
  simp[] >> conj_tac
  >- suspend "store" >>
  irule emit_ret_pc_frag_mem >> qexists_tac `rpc` >> simp[] >>
  rpt strip_tac >>
  gvs[intret_mem_q_def, intret_q_def, result_rel_def,
      intret_vals_match_def, stmt_state_rel_def]
QED

Resume compile_internal_return_equal_mem[store]:
  irule frag_exec_mem_run_inst_seq >>
  gvs[same_blocks_def, IS_PREFIX_APPEND] >>
  rpt gen_tac >> disch_then strip_assume_tac >> conj_tac
  >- (irule return_store_memory_mem_ok >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
      simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  disj1_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  rename1 `eval_operand val_op s = SOME sw` >>
  `w2n bw + type_memory_size tv + 64 < dimword (:256)` by decide_tac >>
  drule_all compile_store_memory_run_capacity >> strip_tac >>
  rename1 `run_inst_seq _ s = OK t1` >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) s` by fs[stmt_state_rel_def, state_rel_def] >>
  `t1.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_data_section``) >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) t1` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `s` >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> simp[regions_disjoint_def] >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  qexists_tac `t1` >> simp[stmt_state_rel_inst_idx, eval_op_inst_idx] >>
  conj_tac
  >- (irule result_state_memory_frame >> simp[] >> qexists_tac `s` >>
      simp[local_region_def, lookup_scopes_def] >>
      fs[venom_state_component_equality] >> metis_tac[]) >>
  qexists_tac `pc` >>
  qspecl_then [`rpc`, `sa`, `s`, `t1`] mp_tac store_result_operand_frame >> simp[]
QED

Finalise compile_internal_return_equal_mem

Theorem return_bytestring_store_bound[local]:
  type_widens_to (get_tenv cx) sty ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  expr_store_bound cx sty v op s ==> expr_store_bound cx ty v op s
Proof
  strip_tac >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `~is_word_type sty /\ ~is_word_type ty` by
    metis_tac[is_bytestring_word_type] >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  gvs[expr_store_bound_def]
QED

Theorem compile_internal_return_direct_or_bytes_mem:
  !ctx func cenv cx es ty sty dtv stv v val_op rpc elem_types buf_op sa sb bw.
    (sty = ty \/ is_bytestring_type ty) /\
    compile_internal_return cenv (SOME val_op) rpc 0 ty sty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    w2n bw + type_memory_size dtv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size dtv)) ==>
    frag_exec_mem ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx sty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           w2n bw + type_memory_size dtv <= s.vs_alloca_next /\
           expr_store_bound cx sty v val_op s /\
           (~is_word_type sty ==> !sw. eval_operand val_op s = SOME sw ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
           (sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
            ?sw. eval_operand val_op s = SOME sw /\
                 w2n sw + type_memory_size stv < dimword (:256) /\
                 (w2n sw + type_memory_size stv <= w2n bw \/
                  w2n bw + type_memory_size dtv <= w2n sw)) /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx dtv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sty = ty`
  >- (gvs[] >>
      `w2n bw + type_memory_size dtv + 64 < dimword (:256)` by decide_tac >>
      drule_all compile_internal_return_equal_mem >>
      disch_then (qspecl_then [`ctx`, `func`] mp_tac) >>
      disch_then (irule o MATCH_MP frag_exec_mem_weaken) >> simp[] >>
      metis_tac[]) >>
  `is_bytestring_type ty` by metis_tac[] >>
  `compile_internal_return cenv (SOME val_op) rpc 0 ty ty elem_types
     (SOME buf_op) sa = ((),sb)` by
    (qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_internal_return_def, compile_store_memory_bytestring_src]) >>
  drule_all (SRULE [] compile_internal_return_equal_mem) >>
  disch_then (qspecl_then [`ctx`, `func`] mp_tac) >>
  disch_then (irule o MATCH_MP frag_exec_mem_weaken) >> simp[] >>
  rpt strip_tac >> simp[]
  >- (irule return_bytestring_expr_rel >> metis_tac[]) >>
  irule return_bytestring_store_bound >> metis_tac[]
QED
