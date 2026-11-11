(* Checked interface probes for the membership loader's memory checks. *)
Theory exprSimBopRestWordLoadSafety
Ancestors
  exprSimBopRestWordLoads exprSimBopRestWordStorageLoads
  instMemFrontier fragExecMem memSafeRun emitHelper venomInst
  words arithmetic list rich_list finite_map loweringPosts exprLoweringProps compileEnv

Theorem rest_word_load_safety_checks:
  MEM opc [MLOAD; ILOAD; SLOAD; TLOAD; DLOAD] /\
  eval_operand addr s = SOME w ==>
  (run_inst_seq_mem_ok [mk_inst iid opc [addr] outs] s <=>
   ((opc = MLOAD \/ opc = ILOAD) ==> w2n w + 32 <= s.vs_alloca_next) /\
   (opc = DLOAD ==> w2n w <= LENGTH s.vs_data_section))
Proof
  strip_tac >> fs[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD, below_frontier_ILOAD,
       inst_dload_in_section_def, mk_inst_def] >>
  simp[below_frontier_no_ranges]
QED

Theorem rest_word_immutable_region_bound:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty tv w es s /\
  evaluate_type (get_tenv cx) ty = SOME vt ==>
  w2n w + type_memory_size vt <=
    (if cenv.ce_is_ctor then s.vs_alloca_next else LENGTH s.vs_data_section)
Proof
  strip_tac >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
  simp[immutable_holds_def] >> strip_tac >>
  `k + type_memory_size vt <= type_memory_size itv` by
    fs[sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  `w2n w = off + k` by simp[] >>
  (Cases_on `cenv.ce_is_ctor`
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
      simp[exprLoweringPropsTheory.stmt_state_rel_def,
           exprLoweringPropsTheory.immutable_alloca_sep_def] >>
      rpt strip_tac >>
      qpat_x_assum `!name tv v off. _` drule_all >> strip_tac >> decide_tac) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def,
       compileEnvTheory.immutables_rel_def] >> rpt strip_tac >>
  qpat_x_assum `!name tv v byte_offset. _` drule_all >> strip_tac >> decide_tac)
QED

(* Constructor staging adds the zero immutable base before the memory load.
   The ADD changes only variables, hence preserves the allocation frontier. *)
Theorem rest_word_staged_load_safety_probe:
  MEM opc [MLOAD; ILOAD] /\
  eval_operand addr s = SOME a /\ eval_operand region s = SOME 0w /\
  w2n a + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst iid ADD [addr; region] [tmp];
     mk_inst jid opc [Var tmp] outs] s
Proof
  simp[] >> strip_tac >>
  qspecl_then [`addr`, `region`] mp_tac emitHelperPropsTheory.step_ADD >>
  disch_then (qspecl_then [`a`, `0w`, `iid`, `tmp`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       inst_dload_in_section_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD, below_frontier_ILOAD,
       inst_dload_in_section_def, mk_inst_def,
       venomStateTheory.update_var_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, FLOOKUP_UPDATE, WORD_ADD_0]
QED

Theorem rest_word_ptr_load_mem_ok:
  context$compile_ptr_load ctor imm loc addr sa = (op,sb) /\
  loc <> LocCalldata /\ eval_operand addr s = SOME a /\
  ((loc = LocMemory \/ (loc = LocCode /\ ctor)) ==>
    w2n a + 32 <= s.vs_alloca_next) /\
  (loc = LocCode /\ ~ctor ==> w2n a <= LENGTH s.vs_data_section) /\
  (loc = LocCode /\ ctor /\ imm <> NONE ==>
    eval_operand (THE imm) s = SOME 0w) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD,
       below_frontier_ILOAD, below_frontier_no_ranges,
       inst_dload_in_section_def, mk_inst_def] >>
  rewrite_tac[GSYM mk_inst_def] >>
  irule rest_word_staged_load_safety_probe >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_array_memory_load_mem_ok:
  vv_post ctx func cenv cx e es va vb s0 es' (Value (ArrayV av)) vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  expr_type e = ArrayT ty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  eval_operand (vv_operand vv) s = SOME w /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  context$compile_ptr_load ctor imm LocMemory addr sa = (op,sb) /\
  eval_operand addr s = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `type_memory_size et = 32` by
    metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) =
   w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32` by
    metis_tac[rest_word_vv_memory_offset] >>
  drule_all rest_word_array_element_extent >> strip_tac >>
  drule rest_word_vv_memory_bound >> simp[] >> strip_tac >>
  irule (Q.INST [`loc` |-> `LocMemory`] rest_word_ptr_load_mem_ok) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem rest_word_array_memory_header_mem_ok:
  vv_post ctx func cenv cx e es va vb s0 es' (Value (ArrayV av)) vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  expr_type e = ArrayT ty (Dynamic cap) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (ArrayTV et (Dynamic cap)) /\
  eval_operand (vv_operand vv) s = SOME w /\
  context$compile_ptr_load ctor imm LocMemory addr sa = (op,sb) /\
  eval_operand addr s = SOME w ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  drule rest_word_vv_memory_bound >> simp[] >> strip_tac >>
  irule (Q.INST [`loc` |-> `LocMemory`] rest_word_ptr_load_mem_ok) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  fs[valueEncodingTheory.type_memory_size_def] >> metis_tac[]
QED

Theorem rest_word_array_immutable_load_mem_ok:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) w es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode addr sa = (op,sb) /\
  eval_operand addr s = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd)` by
    fs[immutable_holds_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `type_memory_size et = 32` by
    metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  drule_all rest_word_array_element_extent >> strip_tac >>
  drule_all rest_word_immutable_region_bound >> strip_tac >>
  `w2n w + type_memory_size (ArrayTV et bd) < dimword (:256)` by
    (qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
     simp[immutable_holds_def] >> strip_tac >>
     `k + type_memory_size (ArrayTV et bd) <= type_memory_size itv` by
       fs[sub_layout_def] >>
     `off + k < dimword (:256)` by decide_tac >>
     `w2n w = off + k` by simp[] >> decide_tac) >>
  `w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) =
   w2n w + ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)` by
    (irule exprSimPropsTheory.buffer_offset_no_wrap >>
     qexists_tac `type_memory_size (ArrayTV et bd)` >> simp[]) >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        compileEnvTheory.immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  irule (Q.INST [`loc` |-> `LocCode`] rest_word_ptr_load_mem_ok) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `cenv.ce_is_ctor` >> fs[] >> decide_tac
QED

Theorem rest_word_array_immutable_header_mem_ok:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx (ArrayT ty (Dynamic cap))
    (Value (ArrayV av)) w es s /\
  evaluate_type (get_tenv cx) ty = SOME et /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode addr sa = (op,sb) /\
  eval_operand addr s = SOME w ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ty (Dynamic cap)) =
   SOME (ArrayTV et (Dynamic cap))` by
    fs[immutable_holds_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  drule_all rest_word_immutable_region_bound >> strip_tac >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        compileEnvTheory.immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  irule (Q.INST [`loc` |-> `LocCode`] rest_word_ptr_load_mem_ok) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `cenv.ce_is_ctor` >> fs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED
