Theory bodyFullForArrayExit
Ancestors
  bodyFullForArray bodyFullGhostFrame bodyFullForRangeEmpty
  bodyMemoryDefs stmtSimProps fragGasEmitCtrl ptrDiscipline
  venomExecSemantics venomInst venomState exprLoweringProps
  loweringStateRelDefs loweringPosts bodyPtrDefs finite_map pred_set
  list rich_list words vyperStorageFootprint bodyPtrBopInLiteralSuffix
  allocaHistory vyperStorageBackend fragGasSeqPtr ptrSafeRun
  contextCodegenRel codegenRel fragGasSeqMem instMemFrontier memSafeRun
  fragExecMem fragGasOriginPtrLoop fragGasOriginPtr

Theorem for_array_exhausted_exit_full:
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; bound_op] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  r.cs_current_bb = exit_lbl /\ r.cs_current_insts = [] /\
  sa.cs_next_var <= r.cs_next_var /\ ~block_is_terminated r /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> x <> dv) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_sim_inv cenv cx env ee /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    k <= LENGTH vs /\ MAP Value (DROP k vs) = [] /\
    LENGTH vs < dimword (:256) /\
    lookup_var idx s = SOME (n2w k) /\
    eval_operand bound_op s = SOME (n2w (LENGTH vs)) /\
    FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
    op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
    lookup_var p s = SOME dst /\ ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= s.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) ==>
  ?u G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1) /\
    stmt_lands lctx r (INL ()) u /\ ~u.vs_halted /\
    ~block_is_terminated r /\ cenv_top_ext cenv cenv (ee with gas_obs := []).scopes /\
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) u /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    return_buf_frame d cenv r u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G1 tn1 u /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x u = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP u.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G0 x /\
      op_taint tn1 (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  `k = LENGTH vs` by fs[MAP_EQ_NIL,DROP_EQ_NIL] >>
  qabbrev_tac `i = mk_inst j1 EQ [Var idx; bound_op] [dv]` >>
  qabbrev_tac `v = update_var dv 1w s` >>
  qabbrev_tac `u = jump_to exit_lbl v` >>
  qabbrev_tac `G1 = step_prov PG G i v` >>
  qabbrev_tac `tn1 = step_taint i s v tn` >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i] s G1 tn1` by
    (gen_tac >>
     `step_inst_base i s = OK v` by
       simp[Abbr `i`,Abbr `v`,step_inst_base_opcode_eqs,mk_inst_def,
         exec_pure2_def,eval_operand_def,bool_to_word_def] >>
     `ptr_inst_ok D lo 0 ctx func G tn i s` by
       (simp[Abbr `i`,ptr_inst_ok_def,access_ok_def,taint_ok_def,
         mk_inst_def,source_memory_write_ranges_def,source_memory_read_ranges_def] >>
        simp[GSYM mk_inst_def,step_inst_non_invoke] >>
        simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
          eval_operand_def,update_var_def,allocas_from_def,op_prov_def] >>
        simp[Abbr `v`,update_var_def] >>
        conj_tac
        >- (rpt strip_tac >> gvs[op_prov_def,FLOOKUP_DEF]) >>
        gen_tac >> Cases_on `op = Var idx` >> simp[] >>
        Cases_on `op = bound_op` >> simp[]) >>
     simp[inst_seq_ptr_def,Abbr `G1`,Abbr `tn1`]) >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)` by
    (gen_tac >>
     `run_inst_seq [i] s = OK v` by
       simp[run_inst_seq_def,Abbr `i`,Abbr `v`,step_inst_base_opcode_eqs,
         mk_inst_def,eval_operand_def,exec_pure2_def,bool_to_word_def] >>
     `run_inst_seq_mem_ok [i] s` by
       (irule run_inst_seq_mem_ok_every >>
        simp[Abbr `i`,mk_inst_def,below_frontier_no_ranges,inst_dload_in_section_other]) >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) [] (OK (v with vs_inst_idx := 1),G1,tn1)` by
       (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
        simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
        disch_then irule >> conj_tac
        >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
        gvs[mk_inst_def]) >>
     `op_taint tn1 (Var dv) = {}` by
       simp[Abbr `tn1`,Abbr `i`,Abbr `v`,step_taint_def,op_taint_def,
         set_var_taint_def,out_taint_def,mk_inst_def,eval_operand_def,FLOOKUP_UPDATE] >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (v with vs_inst_idx := 1,G1,tn1) []
        (OK (jump_to exit_lbl (v with vs_inst_idx := 1)),G1,tn1)` by
       (irule (jnz_origin_ptr_path |> Q.INST [`w` |-> `1w`, `l1` |-> `exit_lbl`, `l2` |-> `body_lbl`]
          |> SIMP_RULE (srw_ss()) []) >>
        simp[Abbr `v`,update_var_def,eval_operand_def,lookup_var_def,
          FLOOKUP_UPDATE,allocas_from_def] >>
        qexistsl_tac [`body_lbl`,`Var dv`,`j2`] >>
        gvs[Abbr `i`,get_instruction_def,update_var_def,eval_operand_def,
          lookup_var_def,FLOOKUP_UPDATE]) >>
     drule_all gas_origin_ptr_path_trans >> simp[Abbr `u`,jump_to_def]) >>
  qexistsl_tac [`u`,`G1`,`tn1`] >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`,Abbr `i`,Abbr `v`,membership_scalar_ghost_frame] >>
  `!x. x <> dv ==> FLOOKUP G1 x = FLOOKUP G x /\
        op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `G1`,Abbr `i`,step_prov_def,out_prov_def,set_prov_def,
          mk_inst_def,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `u`,Abbr `v`,lookup_var_def,jump_to_def,update_var_def,FLOOKUP_UPDATE]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G1 tn1 u` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >>
     simp[Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >> metis_tac[]) >>
  `not_local_ptr cenv ee.scopes dv` by
    (gvs[not_local_ptr_def,local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (simp[Abbr `u`,Abbr `v`,stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `return_buf_frame d cenv r u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >>
     simp[Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >> metis_tac[]) >>
  `alloca_history func u` by
    (irule alloca_history_jump >>
     simp[Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >> metis_tac[]) >>
  simp[stmt_lands_def,cenv_top_ext_def,Abbr `u`,Abbr `v`,jump_to_def,update_var_def] >>
  qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
  simp[storage_well_formed_on_def,oneline get_storage_def]
QED
