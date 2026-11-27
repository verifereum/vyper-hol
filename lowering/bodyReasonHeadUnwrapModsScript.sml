(* The concrete reason prefix, at the endpoint where unwrapping starts. *)
Theory bodyReasonHeadUnwrapMods
Ancestors
  bodyFullRaiseReasonHeadFrame bodyFullPostsMods bodyFullRaiseReasonHead
  bodyFullRaiseReasonHeadGhost bodyFullRaiseReasonHeadValue
  revertReasonPrefixPtr revertReasonPrefixFramePtr revertReasonLayout
  stateRelProj revertAllocationPtr abiPathAllocInv stmtReasonMemory
  stmtReasonLitFragMemory venomMemDefs
  exprLoweringProps loweringStateRelDefs loweringPosts freshWrites
  bodyFullShadowBodyInv bodyPtrIfExpAllocSource bodyPtrDefs ptrDiscipline
  fragGasSeqPtr instMemFrontier ghostPcTransportPtr
  exprSimMemDefs vyperStorageFootprint venomState venomInst venomExecSemantics
  context finite_map arithmetic list rich_list words


Theorem reason_head_prefix_eq[local]:
  reason_head id vn M = revert_reason_prefix id vn M
Proof
  simp[reason_head_def, revert_reason_prefix_def, stringTheory.STRCAT_EQNS]
QED

Theorem reason_head_lookup_idx[local,simp]:
  lookup_var x (s with vs_inst_idx := i) = lookup_var x s
Proof
  simp[lookup_var_def]
QED

Theorem reason_head_store_bound_idx[local,simp]:
  vv_store_bound cx ty lt ee tv vv (s with vs_inst_idx := i) <=>
  vv_store_bound cx ty lt ee tv vv s
Proof
  simp[vv_store_bound_def]
QED

Theorem reason_head_holds_idx[local,simp]:
  vv_holds cenv cx ty tv vv ee (s with vs_inst_idx := i) <=>
  vv_holds cenv cx ty tv vv ee s
Proof
  Cases_on `vv` >> simp[vv_holds_def, expr_val_rel_def] >>
  Cases_on `p.ptr_location` >>
  simp[storage_holds_def, immutable_holds_def, contract_storage_def, contract_transient_def]
QED

Theorem reason_head_unwrap_inputs_mods:
  sb = sm with <|cs_next_var := sm.cs_next_var + 3;
    cs_next_id := sm.cs_next_id + 4;
    cs_current_insts := sm.cs_current_insts ++
      revert_reason_prefix sm.cs_next_id sm.cs_next_var M|> /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  64+M < dimword (:256) /\ local_ptrs_reserved cenv sm /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op G s) /\
  (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rty w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rty <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rty v (w2n w) mem)) ==>
  ?sh Gh tnh B TP.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK sh,Gh,tnh)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee sh) /\
    alloca_history func sh /\ s0.vs_alloca_next <= sh.vs_alloca_next /\
    ~sh.vs_halted /\ sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\
    allocas_from lo sh /\ lo <= sh.vs_alloca_next /\
    FLOOKUP sh.vs_allocas sm.cs_next_id = SOME (B,64+M) /\
    FLOOKUP sh.vs_allocas (sm.cs_next_id+3) = SOME (TP,M) /\
    lookup_var ("%" ++ toString sm.cs_next_var) sh = SOME (n2w B) /\
    lookup_var ("%" ++ toString (sm.cs_next_var+1)) sh = SOME (n2w (B+32)) /\
    lookup_var ("%" ++ toString (sm.cs_next_var+2)) sh = SOME (n2w TP) /\
    ptr_covers Gh tnh ("%" ++ toString sm.cs_next_var) sh (64+M) /\
    ptr_covers Gh tnh ("%" ++ toString (sm.cs_next_var+1)) sh (32+M) /\
    ptr_covers Gh tnh ("%" ++ toString (sm.cs_next_var+2)) sh M /\
    mem_bytes_at 0 lo sh.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!i. i < lo /\ i IN tnh.t_mem ==> i IN tn.t_mem) /\
    eval_operand (vv_operand vv) sh = eval_operand (vv_operand vv) s /\
    op_taint tnh (vv_operand vv) = op_taint tn (vv_operand vv) /\
    op_prov Gh (vv_operand vv) = op_prov G (vv_operand vv) /\
    (!x. not_fresh_at sm x ==>
      lookup_var x sh = lookup_var x s /\ FLOOKUP Gh x = FLOOKUP G x /\
      op_taint tnh (Var x) = op_taint tn (Var x)) /\
    sh.vs_data_section = s.vs_data_section /\
    (vv_location vv <> SOME LocCode ==>
      vv_holds cenv cx (post_value_type cenv e) tv vv ee sh) /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv sh /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gh tnh sh /\
    (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op Gh sh) /\
    (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand Gh sh) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rty w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
          eval_operand (vv_operand vv) sh = SOME w ==>
          w2n w + type_memory_size rty <= lo /\
          (!mem. mem_agree_outside tnh.t_mem sh.vs_memory mem ==>
            val_in_memory rty v (w2n w) mem))
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  rewrite_tac[vv_post_mods_def] >> strip_tac >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `alloca_next_valid s` by fs[alloca_inv_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ reason_head sm.cs_next_id sm.cs_next_var M` by
    simp[reason_head_def, revert_reason_prefix_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (64+M))]
      ["%" ++ toString sm.cs_next_var]) (fn_insts func) /\
   MEM (mk_inst (sm.cs_next_id+3) ALLOCA [Lit (n2w M)]
      ["%" ++ toString (sm.cs_next_var+2)]) (fn_insts func)` by
    (conj_tac >> first_x_assum irule >> simp[reason_head_def]) >>
  `M < dimword(:256)` by decide_tac >>
  `(!x. FLOOKUP s.vs_allocas sm.cs_next_id = SOME x ==> SND x = 64+M) /\
   (!x. FLOOKUP s.vs_allocas (sm.cs_next_id+3) = SOME x ==> SND x = M)` by
    (drule_all (Q.INST [`id` |-> `sm.cs_next_id`, `n` |-> `64+M`]
       stmt_state_rel_alloca_bounds) >> strip_tac >>
     drule_all (Q.INST [`id` |-> `sm.cs_next_id+3`, `n` |-> `M`]
       stmt_state_rel_alloca_bounds) >> strip_tac >>
     conj_tac >> gen_tac >> PairCases_on `x` >> simp[NoAsms] >>
     strip_tac >> first_x_assum drule >> simp[NoAsms, Once ADD_COMM]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (reason_head sm.cs_next_id sm.cs_next_var M)
     (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all reason_head_origin_ptr_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`th`,`Gh`,`thn`,`B`,`TP`] strip_assume_tac)) >>
  suspend "frame"
QED

Resume reason_head_unwrap_inputs_mods[frame]:
  `!k. k < 3 ==> not_local_ptr cenv ee.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `!k. k < 2 ==> not_local_ptr cenv ee.scopes
    ("%" ++ toString (sm.cs_next_var+k))` by
    (rpt strip_tac >> qpat_assum `!k. k < 3 ==> _` (qspec_then `k` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[NoAsms, stringTheory.STRCAT_EQNS, ADD_COMM]) >>
  `!x k. vv_operand vv = Var x /\ k < 3 ==>
     x <> STRING #"%" (toString (sm.cs_next_var+k))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. vv_operand vv = Var x ==> _` drule >>
     simp[NoAsms, not_fresh_at_def] >> disch_then irule >> decide_tac) >>
  `alloca_inv th` by (irule run_inst_seq_alloca_inv >> metis_tac[]) >>
  `inst_seq_ptr (DF (storage_trace_horizon ee.storage_trace)) lo ctx func PG G tn
      (reason_head sm.cs_next_id sm.cs_next_var M) s Gh thn` by metis_tac[] >>
  drule_all reason_head_compiler_frame >> strip_tac >>
  drule_all reason_head_lo_frame >> strip_tac >>
  qabbrev_tac `sh = th with vs_inst_idx := s.vs_inst_idx + 4` >>
  qexistsl_tac [`sh`,`Gh`,`thn`,`B`,`TP`] >>
  suspend "endpoint"
QED

Resume reason_head_unwrap_inputs_mods[endpoint]:
  conj_tac >- (gen_tac >> qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `D` (ACCEPT_TAC o CONJUNCT2))) >>
  conj_tac >- suspend "active" >>
  `ptr_covers Gh thn ("%" ++ toString sm.cs_next_var) th (64+M) /\
   ptr_covers Gh thn ("%" ++ toString (sm.cs_next_var+1)) th (32+M) /\
   ptr_covers Gh thn ("%" ++ toString (sm.cs_next_var+2)) th M` by
    (qpat_assum `fn_inst_ids_distinct func /\ _ ==> _` mp_tac >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[NoAsms]) >>
  `s0.vs_alloca_next <= th.vs_alloca_next` by decide_tac >>
  simp[Abbr `sh`, ptr_covers_inst_idx] >>
  suspend "saved"
QED

Resume reason_head_unwrap_inputs_mods[active]:
  gen_tac >> disch_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac[vv_post_mods_def] >> strip_tac >>
  simp[Abbr `sh`, stmt_state_rel_inst_idx] >>
  irule revert_reason_prefix_state_rel >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`sm.cs_next_id`,`M`,`s`,`sm.cs_next_var`] >>
  qpat_assum `run_inst_seq (reason_head _ _ _) s = OK th` mp_tac >>
  qpat_assum `!k. k < 3 ==> _` mp_tac >>
  pure_rewrite_tac[reason_head_def, revert_reason_prefix_def, stringTheory.STRCAT_EQNS] >>
  strip_tac >> strip_tac >>
  qpat_assum `MEM (mk_inst _ ALLOCA [Lit (n2w (64+M))] _) _` mp_tac >>
  qpat_assum `MEM (mk_inst (sm.cs_next_id+3) ALLOCA _ _) _` mp_tac >>
  pure_rewrite_tac[stringTheory.STRCAT_EQNS] >>
  ntac 2 strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume reason_head_unwrap_inputs_mods[saved]:
  `run_inst_seq (revert_reason_prefix sm.cs_next_id sm.cs_next_var M) s = OK th` by
    (qpat_assum `run_inst_seq (reason_head _ _ _) s = OK th` mp_tac >>
     pure_rewrite_tac[reason_head_prefix_eq] >> disch_then ACCEPT_TAC) >>
  `!x. not_fresh_at sm x ==>
       lookup_var x th = lookup_var x s /\ FLOOKUP Gh x = FLOOKUP G x /\
       op_taint thn (Var x) = op_taint tn (Var x)` by suspend "old_vars" >>
  `eval_operand (vv_operand vv) th = eval_operand (vv_operand vv) s` by
    (irule reason_head_operand_frame >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >> first_assum ACCEPT_TAC) >>
  `op_taint thn (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov Gh (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> simp[op_taint_def, op_prov_def] >>
     `not_fresh_at sm s'` by (first_x_assum irule >> simp[]) >>
     first_x_assum drule >> simp[op_taint_def]) >>
  `th.vs_data_section = s.vs_data_section` by
    (drule run_inst_seq_data_section >>
     simp[NoAsms, revert_reason_prefix_def, mk_inst_def, is_terminator_def]) >>
  simp[] >>
  conj_tac >- suspend "noncode" >> suspend "value_resources"
QED

Resume reason_head_unwrap_inputs_mods[old_vars]:
  `inst_seq_ptr (DF (storage_trace_horizon ee.storage_trace)) lo ctx func PG G tn
    (revert_reason_prefix sm.cs_next_id sm.cs_next_var M) s Gh thn` by
    (qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (reason_head _ _ _) _ _ _` mp_tac >>
     pure_rewrite_tac[reason_head_prefix_eq] >> disch_then ACCEPT_TAC) >>
  drule revert_reason_prefix_ghost_observations >> strip_tac >>
  gen_tac >> disch_tac >>
  `!k. k < 3 ==> x <> STRING #"%" (toString (sm.cs_next_var+k))` by
    (qpat_assum `not_fresh_at sm x` mp_tac >>
     pure_rewrite_tac[not_fresh_at_def] >>
     disch_then (fn th => gen_tac >>
       qspec_then `sm.cs_next_var+k` mp_tac th) >>
     `sm.cs_next_var <= sm.cs_next_var+k` by decide_tac >>
     pure_asm_rewrite_tac[] >> simp[NoAsms]) >>
  conj_tac
  >- (irule revert_reason_prefix_lookup_frame >>
      goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x. (!k. k < 3 ==> _) ==> FLOOKUP _ _ = _ /\ _` drule >> simp[NoAsms]
QED

Resume reason_head_unwrap_inputs_mods[noncode]:
  disch_tac >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee s` by
    (qpat_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     Cases_on `vv` >> fs[vv_location_def, vv_holds_mods_def]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (INST_TYPE [alpha |-> ``:256``] reason_head_vv_holds) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  disch_then (Q.ISPEC_THEN `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- (
    qpat_assum `MEM (mk_inst _ ALLOCA [Lit (n2w (64+M))] _) _` mp_tac >>
    qpat_assum `MEM (mk_inst (sm.cs_next_id+3) ALLOCA _ _) _` mp_tac >>
    pure_rewrite_tac[stringTheory.STRCAT_EQNS] >> ntac 2 strip_tac >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then ACCEPT_TAC
QED

Resume reason_head_unwrap_inputs_mods[value_resources]:
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    (INST_TYPE [alpha |-> ``:256``] reason_head_unwrap_value_resources) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (qspecl_then [`rt`,`e`,`storage_trace_horizon ee.storage_trace`] mp_tac) >>
  (impl_tac >- (
    qpat_assum `MEM (mk_inst _ ALLOCA [Lit (n2w (64+M))] _) _` mp_tac >>
    qpat_assum `MEM (mk_inst (sm.cs_next_id+3) ALLOCA _ _) _` mp_tac >>
    pure_rewrite_tac[stringTheory.STRCAT_EQNS] >> ntac 2 strip_tac >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED

Finalise reason_head_unwrap_inputs_mods
