(* Run the selected RawCreate LocCode residual at its actual ALLOCA endpoint. *)
Theory bodyCreateRawCodeResidualMods
Ancestors
  bodyCreateRawCodeInputMods bodyCreateRawCodeRunMods bodyFullPostsMods
  bodyFullShadowBodyInv exprSimCopy context compileEnv venomState venomInst
  ptrDiscipline typedMemoryCopy memoryReadProps valueEncodingProps valueEncodingDefs
  abiStaticAggregateProps vyperStorageFootprint arithmetic words finite_map

Triviality raw_create_alloc_keeps_code_operand:
  (j with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
            vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t) /\
  (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
    FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
  copy_old_operand a op ==>
  copy_old_operand m op /\ eval_operand op j = eval_operand op t /\
  op_taint tj op = op_taint tn op /\ op_prov Gj op = op_prov G op
Proof
  strip_tac >>
  `j.vs_labels = t.vs_labels` by
    (qpat_assum `_ = t` (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  Cases_on `op` >> gvs[copy_old_operand_def,eval_operand_def,op_taint_def,op_prov_def]
QED

Theorem raw_create_code_residual_mods:
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\
  vv_location vv = SOME LocCode /\
  ptr_vv_ok cx (post_value_type cenv code) raw vv ee G tn t /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  lowered_value_type cenv code = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv code) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  cap = type_memory_bytes cenv (lowered_value_type cenv code) /\
  32 + LENGTH bs <= cap /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv a /\
  ghost_inv_at_mods D lo d cenv cx ee G tn t /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
        eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
    (Var owner) ((type_memory_bytes cenv (vv_type vv)+31) DIV 32) 0 m = ((),b) /\
  not_fresh_at m owner /\ lookup_var owner j = SOME (n2w pbase) /\
  ptr_covers Gj tj owner j cap /\ lo <= pbase /\ pbase + cap < dimword (:256) /\
  FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  pbase + cap <= j.vs_alloca_next /\ allocas_from lo j /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  (j with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
            vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t) /\
  j.vs_memory = t.vs_memory /\ j.vs_data_section = t.vs_data_section /\
  (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
    FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
  lo <= t.vs_alloca_next /\
  (!i. i IN tj.t_mem <=> i IN tn.t_mem \/ (t.vs_alloca_next <= i /\ i < pbase+cap)) /\
  fn_has_code m b func /\ ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
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
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,Gu,tu))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) raw_create_code_input_mods >>
  disch_then (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lowered_value_type _ _ = _`)) >>
  disch_then (drule_at (Pat `_ = type_memory_bytes _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `bs` mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`ownerSrc`,`tops`,`p`,`tag`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [vv_operand_def,vv_type_def]) >>
  drule_all_then strip_assume_tac raw_create_alloc_keeps_code_operand >>
  `eval_operand p.ptr_operand j = SOME w /\ op_taint tj p.ptr_operand = {} /\
   op_prov Gj p.ptr_operand = NONE` by simp[] >>
  `cenv.ce_is_ctor ==> w2n w + cap <= lo /\
     (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tj.t_mem) /\
     !region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region j = SOME 0w /\ copy_old_operand m region /\
        op_taint tj region = {} /\ op_prov Gj region = NONE` by
    (disch_tac >>
     qpat_assum `cenv.ce_is_ctor ==> w2n w + cap <= lo /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> qx_gen_tac `region` >> disch_tac >>
     qpat_assum `!region. cenv.ce_imm_alloca = SOME region ==> _`
       (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac raw_create_alloc_keeps_code_operand >> simp[]) >>
  `word_of_bytes T (0w:bytes32) (mem_bytes_at (w2n w) 32
       (if cenv.ce_is_ctor then j.vs_memory else j.vs_data_section)) = n2w (LENGTH bs) /\
   mem_bytes_at (w2n w+32) (LENGTH bs)
       (if cenv.ce_is_ctor then j.vs_memory else j.vs_data_section) = bs` by
    (Cases_on `cenv.ce_is_ctor`
     >- (qpat_assum `cenv.ce_is_ctor ==> w2n w + cap <= lo /\ _`
           (drule_then strip_assume_tac) >>
         simp[GSYM abiStaticAggregatePropsTheory.mem_word_at_bytes,
              mem_word_at_eq_mload,GSYM read_memory_eq_mem_bytes_at]) >>
     qpat_assum `~cenv.ce_is_ctor ==> _` (drule_then strip_assume_tac) >>
     simp[GSYM abiStaticAggregatePropsTheory.mem_word_at_bytes]) >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`) raw_create_code_run_mods >>
  disch_then (drule_at (Pat `eval_operand p.ptr_operand j = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var owner j = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP j.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `ptr_covers Gj tj owner j cap`)) >>
  disch_then (drule_at (Pat `allocas_from lo j`)) >>
  disch_then (drule_at (Pat `fn_has_code m b func`)) >>
  disch_then (drule_at (Pat `mem_bytes_at _ _ _ = bs`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  impl_tac
  >- (simp[] >> disch_tac >> qpat_assum `~cenv.ce_is_ctor ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  `!i. ~(pbase <= i /\ i < pbase+cap) ==> (i IN tu.t_mem <=> i IN tj.t_mem)` by
    (pure_rewrite_tac[DE_MORGAN_THM,NOT_LESS,NOT_LESS_EQUAL] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  rpt (FIRST_ASSUM ACCEPT_TAC ORELSE conj_tac) >> simp[]
QED
