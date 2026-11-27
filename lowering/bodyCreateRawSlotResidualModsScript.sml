(* Transport the selected RawCreate slot operand through the allocation and copy. *)
Theory bodyCreateRawSlotResidualMods
Ancestors
  bodyCreateRawSlotInputMods bodyCreateRawSlotRunMods exprPtrUnwrapStorageSource
  bodyFullPostsMods loweringPosts bodyPtrDefs exprSimStorageCopy typedMemoryCopy
  stmtLowering exprLowering context fragGasOriginPtr vyperStorageFootprint
  venomState ptrDiscipline finite_map arithmetic words

Theorem raw_create_slot_residual_mods:
  vv_location vv = SOME (slot_loc tr) /\
  (!loc. vv_location vv = SOME loc /\ loc <> LocMemory ==>
    vv_type vv = BaseT (BytesT (Dynamic k))) /\
  vv_post_mods H0 ctx func cenv cx code es sa a s ee raw vv t /\
  ptr_vv_ok cx (post_value_type cenv code) raw vv ee G1 tn1 t /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  cap = type_memory_size (BaseTV (BytesT (Dynamic k))) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\
  (!l. vv_operand vv <> Label l) /\
  compile_slot_to_memory (vv_operand vv) (Var owner)
    ((cap+31) DIV 32) (slot_loc tr) m = (lab,b) /\
  (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
    FLOOKUP Gj x = FLOOKUP G1 x /\ op_taint tj (Var x) = op_taint tn1 (Var x)) /\
  j.vs_accounts = t.vs_accounts /\ j.vs_transient = t.vs_transient /\
  j.vs_call_ctx = t.vs_call_ctx /\ tj.t_stor = tn1.t_stor /\ tj.t_trans = tn1.t_trans /\
  fn_has_code m b func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  allocas_from lo j /\ not_fresh_at m owner /\
  lookup_var owner j = SOME (n2w pbase) /\ ptr_covers Gj tj owner j cap /\
  FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  pbase+cap < dimword (:256) /\ pbase+cap <= j.vs_alloca_next /\
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
  `vv_type vv = BaseT (BytesT (Dynamic k))` by
    (qpat_assum `!loc. _ ==> vv_type vv = _` (qspec_then `slot_loc tr` mp_tac) >>
     Cases_on `tr` >> simp[slot_loc_def]) >>
  drule_all_then (qx_choosel_then [`tag`,`p`,`key`] strip_assume_tac)
    raw_create_slot_input_mods >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `tag = _` SUBST_ALL_TAC >>
  rule_assum_tac (REWRITE_RULE [vv_operand_def]) >>
  `eval_operand p.ptr_operand j = eval_operand p.ptr_operand t /\
   op_taint tj p.ptr_operand = op_taint tn1 p.ptr_operand /\
   (!x. p.ptr_operand = Var x ==> not_fresh_at m x)` by
    (Cases_on `p.ptr_operand` >> fs[eval_operand_def,op_taint_def]) >>
  `ptr_vv_ok cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs))
     (LocatedValue (BaseT (BytesT (Dynamic k))) p) ee Gj tj j` by
    (irule ptr_vv_ok_storage_frame >> conj_tac >- (qexists `tr` >> FIRST_ASSUM ACCEPT_TAC) >>
     qexistsl [`G1`,`t`,`tn1`] >> asm_rewrite_tac[]) >>
  `storage_holds cx tr (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) key ee j` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ t` mp_tac >>
     asm_simp_tac bool_ss [storage_holds_def,contract_storage_def,contract_transient_def]) >>
  `(cap+31) DIV 32 = type_slot_size (BaseTV (BytesT (Dynamic k)))` by
    (qpat_assum `cap = 32 * _` SUBST1_TAC >>
     simp[Once MULT_COMM,DIV_MULT]) >>
  `compile_slot_to_memory p.ptr_operand (Var owner)
    (type_slot_size (BaseTV (BytesT (Dynamic k)))) p.ptr_location m = (lab,b)` by
    (qpat_x_assum `compile_slot_to_memory _ _ _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  `eval_operand p.ptr_operand j = SOME key` by asm_rewrite_tac[] >>
  drule_all raw_create_slot_run_mods >>
  disch_then (qspecl_then [`st0`,`explicit`,`PG`,`DF`]
    (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `u with <|vs_vars := j.vs_vars;vs_memory := j.vs_memory;vs_prev_bb := j.vs_prev_bb;
            vs_current_bb := j.vs_current_bb;vs_inst_idx := j.vs_inst_idx|> = j` by
    (qpat_assum `copy_static u = copy_static j` mp_tac >>
     simp[NoAsms,copy_static_def,venom_state_component_equality]) >>
  qexistsl [`u`,`Gu`,`tu`] >> asm_rewrite_tac[typed_copy_state_frame_def] >>
  rpt conj_tac
  >- (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at m x ==> lookup_var x u = _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at m x ==> lookup_var x u = _ /\ _`
        (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  pure_rewrite_tac[DE_MORGAN_THM,NOT_LESS_EQUAL,NOT_LESS] >>
  qpat_assum `!i. i < pbase \/ pbase+cap <= i ==> _` mp_tac >>
  qpat_assum `cap = 32 * _` SUBST1_TAC >> simp[]
QED
