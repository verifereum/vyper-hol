(* Normalize a linked runtime string pointer at the end of the reason head. *)
Theory bodyReasonRuntimeCodeMods
Ancestors
  bodyReasonHeadUnwrapMods bodyLocalCopyPhysicalRhsMods bodyCopyRuntimeRhsRunMods
  bodyFullUnwrapRun bodyFullUnwrapSlotPost reasonCodeResourcesPtr bodyFullPostsMods
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  loweringSlice exprSimCopy exprSimProps valueEncodingProps actualAllocExec
  exprSimMemDefs bodyPtrDefs loweringPosts loweringStateRelDefs
  exprLoweringProps freshWrites ptrDiscipline compileEnv venomInst venomState
  arithmetic words finite_map pred_set

(* Read the owner at the operand endpoint, then copy at the head endpoint.
   The path is independent of the dead footprint selected by the tail. *)
Theorem reason_runtime_code_copy_origin_execution_mods:
  ~ce.ce_is_ctor /\ p.ptr_location = LocCode /\
  vv_post_mods H ctx func ce cx e es sa sm entry ee tv (LocatedValue ty p) s /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue ty p) ee G tn s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  ~is_word_type (post_value_type ce e) /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  unwrap_value ce (LocatedValue ty p) sb = (op,sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sb /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  stmt_state_rel H ctx func ce cx ee sh /\
  alloca_history func sh /\ allocas_from lo sh /\ lo <= sh.vs_alloca_next /\
  ~sh.vs_halted /\ sh.vs_current_bb = sb.cs_current_bb /\
  sh.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand p.ptr_operand sh = eval_operand p.ptr_operand s /\
  op_taint tnh p.ptr_operand = op_taint tn p.ptr_operand /\
  sh.vs_data_section = s.vs_data_section ==>
  ?v z Gf tf.
    read_result cx tv ee = (INL v,ee) /\ val_wf rt v /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,tnh) [] (OK z,Gf,tf)) /\
    stmt_state_rel H ctx func ce cx ee z /\
    wb_frame ce ee ee sb sh z /\ ghost_kept_at lo ce ee sb Gh tnh sh Gf tf /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x sh) /\
    (!x n. not_fresh_at sb x /\ ptr_covers Gh tnh x sh n ==> ptr_covers Gf tf x z n) /\
    expr_val_rel cx (post_value_type ce e) v op z /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    allocas_from lo z /\ sh.vs_alloca_next <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_mods_def, vv_holds_mods_def, immutable_holds_mods_def,
          immutable_holds_def] >> strip_tac >> goal_assum (drule_at Any)) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac local_copy_raw_code_source_mods) >>
  disch_then (qspecl_then [`v`,`tn`,`rt`,`lo`,`G`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`owner`,`tops`,`src`] (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `ty = post_value_type ce e` SUBST_ALL_TAC >>
  qpat_assum `~ce.ce_is_ctor ==> _` (drule_then strip_assume_tac) >>
  drule immutable_holds_read_result_value >> disch_tac >>
  `immutable_holds (ce with ce_module := owner) cx (post_value_type ce e)
      (Value v) src ee s` by
    (pop_assum (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac immutable_holds_bounds >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp sh)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ sh`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `eval_operand p.ptr_operand sh = SOME src /\ op_taint tnh p.ptr_operand = {} /\
   val_in_memory rt v (w2n src) sh.vs_data_section /\
   w2n src + type_memory_size rt <= LENGTH sh.vs_data_section` by asm_simp_tac (srw_ss()) [] >>
  drule_all copy_runtime_rhs_endpoint_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gh`]
    (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`dst`,`u`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "frames"
QED

Resume reason_runtime_code_copy_origin_execution_mods[frames]:
  qabbrev_tac `inst = mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sb.cs_next_id /\
   inst.inst_outputs = [root] /\ inst.inst_operands = [Lit (n2w (type_memory_size rt))]` by
    simp[Abbr `inst`, mk_inst_def] >>
  `not_local_ptr ce ee.scopes root` by
    (qpat_assum `root = _` SUBST1_TAC >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sb` >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (drule_at (Pat `exec_alloca _ _ _ = OK u`) stmt_state_rel_exec_alloca >>
     disch_then drule_all >> simp[]) >>
  `u.vs_memory = sh.vs_memory /\
   (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x sh)` by
    (drule_all actual_literal_alloca_frame >> strip_tac >> simp[] >>
     gen_tac >> disch_tac >>
     `x <> root` by fs[not_fresh_at_def] >>
     qpat_assum `!op. op <> Var root ==> _` (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def]) >>
  `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x u` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!name b len. local_region ce ee.scopes u name b len <=> local_region ce ee.scopes sh name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sb` >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee z` by
    (irule copy_buffer_state_rel_frame >> qexistsl_tac [`w2n dst`,`inst`,`u`,`sb`,`type_memory_size rt`] >>
     asm_simp_tac (srw_ss()) [] >> rpt conj_tac >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `wb_frame ce ee ee sb sh z` by
    (irule unwrap_slot_copy_wb_frame >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`type_memory_size rt`,`w2n dst`] >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!name b len. local_region _ _ sh name b len ==> _` (drule_then mp_tac) >>
         tautLib.TAUT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!id b len. _ ==> regions_disjoint _ _ _ _` (drule_all_then mp_tac) >>
     simp[regions_disjoint_def] >> tautLib.TAUT_TAC) >>
  suspend "normalized"
QED

Resume reason_runtime_code_copy_origin_execution_mods[normalized]:
  `ghost_kept_at lo ce ee sb Gh tnh sh Gf tf` by
    simp[ghost_kept_at_def] >>
  `!x n. not_fresh_at sb x /\ ptr_covers Gh tnh x sh n ==> ptr_covers Gf tf x z n` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x sh /\ _`
       (drule_then strip_assume_tac) >> fs[ptr_covers_def]) >>
  `expr_val_rel cx (post_value_type ce e) v op z` by
    (simp[expr_val_rel_def] >> qexists_tac `dst` >> asm_rewrite_tac[] >> simp[]) >>
  `val_store_size rt v <= type_memory_size rt` by simp[val_store_size_le] >>
  `expr_store_bound cx (post_value_type ce e) v op z` by
    simp[expr_store_bound_def] >>
  `ptr_val_ok cx (post_value_type ce e) v op Gf tf z` by
    (qpat_x_assum `root = _` kall_tac >>
     qpat_assum `ptr_covers Gf tf root z _`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_val_ok_def, ptr_mem_ok_def] >> decide_tac) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`v`,`z`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Finalise reason_runtime_code_copy_origin_execution_mods
