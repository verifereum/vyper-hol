(* Transport the live bytecode window across the selected ALLOCA. *)
Theory bodyCreateRawMemoryResidualMods
Ancestors
  bodyCreateRawMemoryInputMods bodyCreateRawMemoryRunMods
  bodyFullPostsMods vyperStorageFootprint loweringPosts bodyPtrDefs
  assignTuplePtrCopyLen ptrDiscipline venomMemDefs venomState venomInst
  context compileEnv exprLowering emitHelper exprLoweringProps fragGasOriginPtr
  typedMemoryCopy loweringShapeDefs finite_map pred_set list words arithmetic

Theorem raw_create_memory_residual_mods:
  vv_post_mods (storage_trace_horizon ee.storage_trace) ctx func cenv cx e
    es sa a s ee raw vv t /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee G1 tn1 t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv t /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  (!src. vv_operand vv = Var src ==> not_fresh_at a src) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  emit_op MLOAD [vv_operand vv] m = (len,ml) /\
  emit_op ADD [len;Lit 32w] ml = (cnt,mc) /\
  compile_copy_memory_dynamic (Var owner) (vv_operand vv) cnt mc = ((),b) /\
  fn_has_code m b func /\ fn_inst_ids_distinct func /\
  j.vs_memory = t.vs_memory /\ t.vs_alloca_next <= j.vs_alloca_next /\
  (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
     FLOOKUP Gj x = FLOOKUP G1 x /\ op_taint tj (Var x) = op_taint tn1 (Var x)) /\
  (!i. i IN tj.t_mem <=> i IN tn1.t_mem \/ (t.vs_alloca_next <= i /\ i < pbase+cap)) /\
  not_fresh_at m owner /\ FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  lookup_var owner j = SOME (n2w pbase) /\ ptr_covers Gj tj owner j cap /\
  32+LENGTH bs <= cap /\ pbase+cap < dimword (:256) /\ pbase+cap <= j.vs_alloca_next /\
  allocas_from lo j /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  alloca_history func j /\ alloca_inv j /\
  ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?u Gu tu.
    typed_copy_state_frame m pbase cap j u /\
    (!x. not_fresh_at m x ==> FLOOKUP Gu x = FLOOKUP Gj x /\
      op_taint tu (Var x) = op_taint tj (Var x)) /\
    (!i. ~(pbase <= i /\ i < pbase+cap) ==> (i IN tu.t_mem <=> i IN tj.t_mem)) /\
    tu.t_stor = tj.t_stor /\ tu.t_trans = tj.t_trans /\ tu.t_imm = tj.t_imm /\
    lookup_var owner u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
    mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
    (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,Gu,tu))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`src`,`w`] (map_every assume_tac o CONJUNCTS))
    raw_create_memory_input_mods >>
  qpat_assum `!x. not_fresh_at a x ==> _` (drule_then strip_assume_tac) >>
  `ptr_covers Gj tj src j (32+LENGTH bs)` by
    (irule ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers G1 tn1 src t _` (irule_at Any) >> simp[]) >>
  `lookup_var src j = SOME (n2w (w2n (w:bytes32))) /\ w2n w < dimword (:256)` by
    fs[eval_operand_def,w2n_lt] >>
  `w2n w+32+LENGTH bs <= j.vs_alloca_next` by decide_tac >>
  `mload (w2n w) j = n2w (LENGTH bs) /\ read_memory (w2n w+32) (LENGTH bs) j = bs` by
    (pure_rewrite_tac[mload_def,read_memory_def] >>
     qpat_assum `j.vs_memory = t.vs_memory` SUBST1_TAC >>
     simp[GSYM mload_def,GSYM read_memory_def]) >>
  `!i. w2n w <= i /\ i < w2n w+32+LENGTH bs ==> i NOTIN tj.t_mem` by
    (gen_tac >> strip_tac >>
     `i < t.vs_alloca_next` by decide_tac >> simp[]) >>
  qpat_assum `vv_operand vv = Var src` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all raw_create_memory_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`u`,`Gu`,`tu`] >>
  `!x. not_fresh_at m x ==> FLOOKUP Gu x = FLOOKUP Gj x /\
    op_taint tu (Var x) = op_taint tj (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at m x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!i. ~(pbase <= i /\ i < pbase+cap) ==> (i IN tu.t_mem <=> i IN tj.t_mem)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. _ ==> (i IN tu.t_mem <=> i IN tj.t_mem)` irule >> decide_tac) >>
  simp[]
QED
