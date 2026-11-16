Theory createCtorTupleSlotUnwrap
Ancestors
  createCtorTupleUnwrap createCtorTupleCaptureFrame
  exprSimMemoryPath exprSimProps exprBopSimProps
  exprSimWordArgs exprLoweringProps emitHelperProps fragGasMode fragGasPath
  loweringPosts loweringStateRelDefs exprLowering context compileEnv emitHelper venomState venomInst venomExecSemantics
  freshWrites exprOperandVar words finite_map ASCIInumbers arithmetic

(* The address instruction is pure, but advances the execution cursor. *)
Theorem ctor_slot_add_path[local]:
  emit_op ADD [src; Lit (n2w off)] a = (dst,a1) /\
  eval_operand src s = SOME (n2w source_base) /\
  local_ptrs_reserved ce a /\ stmt_state_rel H ctx func ce cx es s /\
  fn_has_code a a1 func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    eval_operand dst q = SOME (n2w (source_base + off)) /\
    (!x. dst = Var x ==> not_fresh_at a1 x) /\ (!l. dst <> Label l) /\
    stmt_state_rel H ctx func ce cx es q /\ wb_frame ce es es a s q /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
    ~q.vs_halted /\ q.vs_current_bb = a1.cs_current_bb /\
    q.vs_inst_idx = LENGTH a1.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `q = (update_var (STRING #"%" (toString a.cs_next_var))
    (n2w (source_base + off)) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_marked_path F ctx func s 0 (OK q)` by
    (qunabbrev_tac `q` >> pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
     irule emit_op_zero_path >>
     simp[] >> qexistsl [`[src; Lit (n2w off)]`, `dst`, `ADD`, `a1`] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operands_def, eval_operand_def, word_add_n2w, is_terminator_def]) >>
  `stmt_state_rel H ctx func ce cx es q` by
    (simp[Abbr `q`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists `a` >> simp[]) >>
  `a1.cs_current_bb = a.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists `q` >>
  simp[Abbr `q`, update_var_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, wb_frame_def, locals_kept_mem, not_fresh_at_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]
QED

(* Capture provenance stays at c_vvs.  The later cutoff a protects the
   already allocated tuple, including slots completed by earlier stores. *)
Theorem ctor_slot_unwrap_path:
  emit_op ADD [src; Lit (n2w off)] a = (dst,a1) /\
  unwrap_value ce vv a1 = (op,a2) /\
  fn_has_code a a2 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce c_vvs /\
  origin.cs_next_var <= c_vvs.cs_next_var /\
  origin.cs_next_id <= c_vvs.cs_next_id /\
  c_vvs.cs_next_var <= a.cs_next_var /\ c_vvs.cs_next_id <= a.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
  (!l. vv_operand vv <> Label l) /\
  (!x. src = Var x ==> not_fresh_at a x) /\ (!l. src <> Label l) /\
  eval_operand src s = SOME (n2w source_base) /\
  source_base + off < dimword (:256) /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty ==>
     type_memory_bytes ce ty = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin c_vvs es raw vv s /\
  read_result cx raw es = (INL v,es) /\
  FLOOKUP s.vs_allocas tuple_aid = SOME (source_base,source_cap) /\
  c_vvs.cs_next_id <= tuple_aid /\ tuple_aid < a.cs_next_id /\
  (!n b k. local_region ce es.scopes s n b k ==>
     source_base + source_cap <= b \/ b + k <= source_base) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    eval_operand dst u = SOME (n2w (source_base + off)) /\
    eval_operand src u = SOME (n2w source_base) /\
    expr_val_rel cx ty v op u /\ expr_val_at ce cx ty origin a2 es v op u /\
    stmt_state_rel H ctx func ce cx es u /\
    storage_well_formed_on cx es (FST H) /\
    alloca_inv u /\ alloca_room ctx func u /\ fmp_room ctx func u /\
    ~u.vs_halted /\ u.vs_current_bb = a2.cs_current_bb /\
    u.vs_inst_idx = LENGTH a2.cs_current_insts /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx /\
    wb_frame ce es es a s u /\
    FLOOKUP u.vs_allocas tuple_aid = SOME (source_base,source_cap) /\
    source_base + source_cap <= u.vs_alloca_next /\
    mem_bytes_at source_base source_cap u.vs_memory =
      mem_bytes_at source_base source_cap s.vs_memory /\
    (!n b k. local_region ce es.scopes u n b k ==>
       source_base + source_cap <= b \/ b + k <= source_base) /\
    (!ty' raw' vv' value'.
       vv_holds ce cx ty' raw' vv' es s /\
       vv_at ce cx ty' origin c_vvs es raw' vv' s /\
       read_result cx raw' es = (INL value',es) /\
       (!x. vv_operand vv' = Var x ==> not_fresh_at c_vvs x) /\
       (!l. vv_operand vv' <> Label l) ==>
       vv_holds ce cx ty' raw' vv' es u /\
       vv_at ce cx ty' origin c_vvs es raw' vv' u /\
       read_result cx raw' es = (INL value',es))
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2` by
    metis_tac[ci_mono_emit_op, ci_mono_unwrap_value, pairTheory.SND] >>
  `a.cs_next_var <= a1.cs_next_var /\ a.cs_next_id <= a1.cs_next_id /\
   fn_has_code a a1 func /\ fn_has_code a1 a2 func` by
    metis_tac[ci_mono_def, fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved ce a` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all ctor_slot_add_path >> strip_tac >>
  `vv_holds ce cx ty raw vv es q /\
   vv_at ce cx ty origin a1 es raw vv q /\
   read_result cx raw es = (INL v,es)` by
    (`(!t op. vv = StackValue t op ==>
         (!x. op = Var x ==> not_fresh_at a x) /\ (!l. op <> Label l)) /\
      (!t p. vv = LocatedValue t p ==>
         (!x. p.ptr_operand = Var x ==> not_fresh_at a x) /\
         (!l. p.ptr_operand <> Label l))` by
       (Cases_on `vv` >> gvs[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
     `contract_storage q = contract_storage s /\
      contract_transient q = contract_transient s` by
       simp[contract_storage_def, contract_transient_def] >>
     drule_at (Pat `vv_holds _ _ _ _ _ _ _`)
       (INST_TYPE [beta |-> alpha] ctor_capture_frame) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     simp[] >>
     disch_then (qspecl_then [`origin`,`a1`,`c_vvs`,`a`] mp_tac) >> simp[]) >>
  `origin.cs_next_var <= a1.cs_next_var /\
   origin.cs_next_id <= a1.cs_next_id /\
   (!x. vv_operand vv = Var x ==> not_fresh_at a1 x)` by
    metis_tac[LESS_EQ_TRANS, not_fresh_at_mono] >>
  drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`) ctor_captured_unwrap_path >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  `wb_frame ce es es a1 q u` by
    (simp[wb_frame_def] >> metis_tac[]) >>
  `wb_frame ce es es a s u` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`es`,`a1`,`q`] >> simp[]) >> metis_tac[]) >>
  `!n b k. local_region ce es.scopes u n b k <=>
             local_region ce es.scopes s n b k` by
    (rpt gen_tac >> irule exprSimSubscriptArrayFrameTheory.local_region_wb_frame >>
     simp[] >> conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     metis_tac[]) >>
  `wb_frame ce es es c_vvs s u` by
    (gvs[wb_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!x w. not_fresh_at a x /\ lookup_var x s = SOME w ==> _` irule >>
         simp[] >> metis_tac[not_fresh_at_mono]) >>
     rpt strip_tac >>
     qpat_x_assum `!aid b sz. _ /\ aid < a.cs_next_id /\ _ ==> _` irule >>
     conj_tac >- metis_tac[] >>
     qexists `aid` >> simp[] >> decide_tac) >>
  qexists `u` >> simp[] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac
  >- (irule eval_operand_frame >> conj_tac >- simp[] >>
      qexistsl [`a1`,`q`] >> simp[ADD_COMM]) >>
  conj_tac
  >- (irule eval_operand_frame >> conj_tac >- simp[] >>
      qexistsl [`a`,`s`] >> gvs[wb_frame_def]) >>
  conj_tac
  >- (gvs[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[wb_frame_def] >>
      qpat_x_assum `!aid b sz. _ /\ aid < a.cs_next_id /\ _ ==> _` irule >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)
    (INST_TYPE [beta |-> alpha] ctor_capture_frame) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  simp[contract_storage_def, contract_transient_def] >>
  disch_then (qspecl_then [`c_vvs`,`c_vvs`] mp_tac) >>
  simp[] >>
  `(!t op. vv' = StackValue t op ==>
      (!x. op = Var x ==> not_fresh_at c_vvs x) /\ (!l. op <> Label l)) /\
   (!t p. vv' = LocatedValue t p ==>
      (!x. p.ptr_operand = Var x ==> not_fresh_at c_vvs x) /\
      (!l. p.ptr_operand <> Label l))` by
    (Cases_on `vv'` >> gvs[vv_operand_def]) >> simp[]
QED
