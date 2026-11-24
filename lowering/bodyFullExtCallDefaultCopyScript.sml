(* The equal-type, non-bytestring default store is a flat copy. *)
Theory bodyFullExtCallDefaultCopy
Ancestors
  bodyFullMemoryCopy valueEncodingProofs contextProps abiTupleProps
  typedMemoryCopy bodyPtrDefs fragGasOriginPtr
  context codegenRel ptrDiscipline venomState venomInst valueEncodingDefs
  vyperContext finite_map words

val flat_capacity_inputs = ``
  compile_store_memory ce src (Var dst) ty ty a = ((),b) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\ type_memory_bytes ce ty = type_memory_size tv /\
  (!x. src = Var x ==> not_fresh_at a x) /\ not_fresh_at a dst /\
  eval_operand src s = SOME sw /\ lookup_var dst s = SOME dw /\
  ptr_mem_ok cx ty v src G tn s /\
  (type_memory_size tv <> 0 ==>
     (?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
     ptr_covers G tn dst s (type_memory_size tv) /\
     w2n sw + type_memory_size tv <= s.vs_alloca_next /\
     w2n dw + type_memory_size tv <= s.vs_alloca_next /\
     s.vs_alloca_next < dimword (:256)) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts``;

val flat_capacity_post = ``
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tm)) /\
    (!mem. mem_agree_outside tm.t_mem u.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem) /\
    lookup_var dst u = SOME (dw:256 word) /\
    typed_copy_state_frame a (w2n dw) (type_memory_size tv) s u /\
    (!x. not_fresh_at a x ==>
      lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    u.vs_current_bb = b.cs_current_bb /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted``;

Theorem extcall_default_copy_capacity_joint_exact:
  ^flat_capacity_inputs ==>
  ?u Gf tm.
    run_inst_seq (emitted_insts a b) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
    ^flat_capacity_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_copy_memory (Var dst) src (type_memory_size tv) a = ((),b)` by
    fs[compile_store_memory_def] >>
  Cases_on `type_memory_size tv = 0`
  >- (`b = a` by fs[compile_copy_memory_zero] >>
      drule_all return_zero_wf_memory >> strip_tac >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[gas_origin_ptr_path_rules,exprLoweringPropsTheory.emitted_insts_def,
           exprLoweringPropsTheory.run_inst_seq_def,
           venom_state_component_equality]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem` by metis_tac[ptr_mem_ok_def] >>
  qpat_x_assum `type_memory_size tv <> 0 ==> _` mp_tac >>
  simp[] >> strip_tac >> gvs[eval_operand_def] >>
  rename1 `compile_copy_memory (Var dst) (Var xs) _ a = ((),b)` >>
  `w2n sw + type_memory_size tv < dimword (:256) /\
   w2n dw + type_memory_size tv < dimword (:256)` by decide_tac >>
  drule body_full_memory_copy_frame_path_exact >>
  disch_then (drule_at (Pat `lookup_var xs s = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var dst s = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers G tn xs s _`)) >>
  disch_then (drule_at (Pat `fn_has_code a b func`)) >>
  disch_then (drule_at (Pat `allocas_from lo s`)) >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu`
    (qx_choose_then `tu` strip_assume_tac))) >>
  `b.cs_current_bb = a.cs_current_bb` by
    (drule compile_copy_memory_extends >> simp[exprLoweringPropsTheory.same_blocks_def]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[] >> metis_tac[]
QED

Theorem extcall_default_copy_capacity_joint:
  ^flat_capacity_inputs ==> ?u Gf tm. ^flat_capacity_post
Proof
  disch_tac >> mp_tac (SPEC_ALL extcall_default_copy_capacity_joint_exact) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tm`] (assume_tac o CONJUNCT2)) >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> first_assum ACCEPT_TAC
QED
