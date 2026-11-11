(* Constructor immutable scalar reads and their allocated memory extent. *)
Theory immutableWordReadMemory
Ancestors
  exprSimPopImmutableTarget exprSimBopRestWordLoadSafety
  exprSimBopRestWordLoadPath exprSimUnwrap fragGasSeqMem fragGasMode
  exprSimProps exprLoweringProps vyperState venomState valueEncodingDefs
  context fragExecMem list rich_list venomInst loweringStateRelDefs

Theorem immutable_place_word_read:
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\ is_word_type ty /\
  imm_place_at cenv cx es (PlaceR (ImmutablePlace src id path)) w ty ==>
  ?tv cur.
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_place cx (ImmutablePlace src id path) es = (INL cur,es) /\
    place_type_value cx (ImmutablePlace src id path) es = (INL tv,es) /\
    value_has_type tv cur /\
    mload (w2n w) s = typed_val_to_w256 tv cur /\
    w2n w + 32 <= s.vs_alloca_next
Proof
  strip_tac >> gvs[imm_place_at_def] >>
  drule_all imm_place_at_value_type >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `val_in_memory tv v (off+k) s.vs_memory` by
    (irule imm_readable_path_memory >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     qexistsl [`ctx`, `env`, `func`] >> simp[]) >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `off + k < dimword (:256)` by decide_tac >>
  `mem_word_at (off+k) s.vs_memory = typed_val_to_w256 tv v` by
    (irule val_in_memory_word_type >> metis_tac[]) >>
  `off + type_memory_size itv <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  qexists `v` >>
  simp[read_place_def, place_type_value_def, get_immutables_def,
       get_address_immutables_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.lift_sum_def,
       vyperStateTheory.lift_option_type_def, mload_def, mem_word_at_def] >>
  gvs[mem_word_at_def, mem_bytes_at_def]
QED

Theorem immutable_word_load_path[local]:
  compile_ptr_load T imm LocCode addr sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule rest_word_ptr_load_code >> simp[] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[listTheory.EVERY_MEM, listTheory.FILTER_EQ_NIL] >>
     rpt strip_tac >> res_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_mem >>
  simp[gas_marked_path_def]
QED

Theorem immutable_word_read_mem:
  imm_target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (ImmutablePlace src id path)) ty r s /\
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\ is_word_type ty /\
  compile_ptr_load T cenv.ce_imm_alloca LocCode (FST r) sm = (op,sb) /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tv cur u.
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_place cx (ImmutablePlace src id path) es = (INL cur,es) /\
    place_type_value cx (ImmutablePlace src id path) es = (INL tv,es) /\
    value_has_type tv cur /\
    gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand op u = SOME (typed_val_to_w256 tv cur) /\
    (word_value cur ==> eval_operand op u = SOME (val_to_w256 cur)) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. (!i. MEM i (emitted_insts sm sb) ==> ~MEM x i.inst_outputs) ==>
         FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x) /\
    u = s with <|vs_vars := u.vs_vars;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>
Proof
  strip_tac >> fs[imm_target_post_def] >>
  drule_all immutable_place_word_read >> strip_tac >>
  `(cenv.ce_imm_alloca <> NONE ==>
      eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[stmt_state_rel_def, loweringStateRelDefsTheory.immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (irule rest_word_ptr_load_mem_ok >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule rest_word_ptr_load_run >> simp[] >>
  disch_then (qspecl_then [`s`, `0w`, `w`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all immutable_word_load_path >> strip_tac >>
  drule rest_word_ptr_load_run_frame >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule rest_word_ptr_load_code >> simp[] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[wordsTheory.WORD_ADD_0, typed_val_to_w256_word_value] >>
  qpat_x_assum `t = s with vs_vars := _` mp_tac >>
  simp[venom_state_component_equality]
QED
