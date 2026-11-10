(* Shared counted allocation boundary for located reason normalization. *)
Theory normalizationAllocationPathPtr
Ancestors
  storageNormalizationOwnershipPtr reasonAllocationFramePtr reasonPrefixPtr
  exprSimAlloc exprLoweringProps loweringHalt loweringPosts bodyPtrDefs
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps venomState venomInst
  venomInstProofs venomExecSemantics ptrDiscipline allocationPtr fragGasPathPtr
  finite_map words arithmetic

Theorem normalization_alloc_buffer_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
  local_ptrs_reserved cenv cc /\ fn_inst_ids_distinct func /\
  n < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted ==>
  ?u root b G1 tn1.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK u) /\
    u.vs_current_bb = cd.cs_current_bb /\
    u.vs_inst_idx = LENGTH cd.cs_current_insts /\ ~u.vs_halted /\
    stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv cd /\
    FLOOKUP u.vs_allocas cc.cs_next_id = SOME (b,n) /\
    b+n < dimword(:256) /\ lookup_var root u = SOME (n2w b) /\
    ptr_covers G1 tn1 root u n /\
    MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    (!name lb len. local_region cenv es.scopes u name lb len ==>
      regions_disjoint b n lb len) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid lb len. aid < cc.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (lb,len) ==> regions_disjoint b n lb len) /\
    (!old. not_fresh_at cc old ==>
      lookup_var old u = lookup_var old s /\ FLOOKUP G1 old = FLOOKUP G old /\
      op_taint tn1 (Var old) = op_taint tn (Var old)) /\
    (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
      ptr_covers G1 tn1 old u k) /\
    not_fresh_at cd root /\
    (!old. not_fresh_at cc old ==> not_fresh_at cd old) /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `p = STRING #"%" (toString cc.cs_next_var)` by
    (qpat_x_assum `buf.buf_operand = Var p` mp_tac >> simp[]) >>
  `cd.cs_current_bb = cc.cs_current_bb /\
   LENGTH cd.cs_current_insts = SUC (LENGTH cc.cs_current_insts)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted` by
    suspend "control" >>
  drule_all reason_encoder_alloc_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := SUC s.vs_inst_idx`, `p`, `w2n w`,
    `step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [p]) t`,
    `step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [p]) s t tn`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- suspend "reserved"
  >- gvs[eval_operand_def, lookup_var_def]
  >- suspend "local_separation"
  >- suspend "old_metadata"
  >- suspend "old_coverage"
  >> suspend "labels"
QED

Resume normalization_alloc_buffer_path_ptr[control]:
  `step_inst 0 ctx (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [p]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  conj_tac
  >- (drule step_preserves_control_flow >> simp[mk_inst_def, is_terminator_def]) >>
  drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]
QED

Resume normalization_alloc_buffer_path_ptr[reserved]:
  irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]
QED

Resume normalization_alloc_buffer_path_ptr[local_separation]:
  qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[local_region_def, lookup_var_def]
QED
Resume normalization_alloc_buffer_path_ptr[old_metadata]:
  gen_tac >> strip_tac >>
  `old <> p` by metis_tac[] >>
  `lookup_var old t = lookup_var old s` by metis_tac[] >>
  asm_rewrite_tac[GSYM lookup_var_def] >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  drule_all reason_alloca_old_metadata >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >> simp[]
QED
Resume normalization_alloc_buffer_path_ptr[old_coverage]:
  rpt gen_tac >> strip_tac >>
  `old <> p` by metis_tac[] >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `!old n'. old <> _ /\ _ ==> _` irule >> asm_rewrite_tac[]
QED
Resume normalization_alloc_buffer_path_ptr[labels]:
  simp[] >> irule hash_alloc_buffer_labels >>
  goal_assum (drule_at Any) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[run_inst_seq_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
      AllCaseEqs()]
QED
Finalise normalization_alloc_buffer_path_ptr
