(* Fixed-endpoint data posts for the literal MethodId buffer. *)
Theory bodyFullBuiltinEnvMethodIdPost
Ancestors
  bodyFullLiteralBuffer bodyFullUnwrapSlotPost bodySimFull exprSimLiteralBuffer
  exprSimPtrLiteralBuffer allocationPathGrowth
  exprSimMemDefs bodyPtrDefs loweringPosts loweringStateRelDefs exprLoweringProps
  exprSimProps exprSimVVFrame exprLowering compileEnv context ptrDiscipline
  venomState vyperAST vyperInterpreter vyperState vyperValue vyperContext
  valueEncoding valueEncodingDefs vyperTypeBytesCrypto words list finite_map pred_set

Theorem method_id_literal_dynamic_endpoint_post:
  !DF lo d ctx PG func cenv cx st0 es s0 G0 tn0 la l bs sa sb buf
    u t b p sh G' tn'.
    method_id_literal (Literal la l) = SOME bs /\
    compile_bytelike_literal (TAKE 4 (Keccak_256_w64 bs))
      (LENGTH (TAKE 4 (Keccak_256_w64 bs))) sa = (buf,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    buf.buf_operand = Var p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    run_inst_seq (emitted_insts sa sb) s0 = OK t /\
    u.vs_memory = s0.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,64) /\ lo <= b /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint b 64 a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
       regions_disjoint b 64 a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
    u.vs_labels = s0.vs_labels /\ wb_frame cenv es es sa s0 u /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
    (!a len. a + len <= b \/ b + 64 <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    FLOOKUP G' p = SOME (b,64) /\ lookup_var p t = SOME (n2w b) /\
    op_taint tn' (Var p) = {} /\ b + 64 < dimword (:256) /\
    mem_word_at b t.vs_memory = 4w /\
    mem_bytes_at (b + 32) 4 t.vs_memory = TAKE 4 (Keccak_256_w64 bs) /\
    tn'.t_mem = tn0.t_mem DIFF {i | b <= i /\ i < b + 64} /\
    tn'.t_stor = tn0.t_stor /\ tn'.t_trans = tn0.t_trans /\ tn'.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G0 x /\
       FLOOKUP tn'.t_var x = FLOOKUP tn0.t_var x) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G0 tn0 (emitted_insts sa sb) s0 G' tn' /\
       stmt_state_rel H ctx func cenv cx es u) ==>
    !H. valid_horizon cx st0 H es.storage_trace ==>
      vv_post H ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es sa sb s0
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic 4))) (BaseT (BytesT (Dynamic 4)))
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
      ptr_vv_ok cx (BaseT (BytesT (Dynamic 4)))
        (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) es G' tn' t /\
      ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l])
        buf.buf_operand G' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (simp[ghost_kept_at_def, op_taint_def, IN_DIFF] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx es u /\
   ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
   storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0` by metis_tac[] >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
   t.vs_immutables = u.vs_immutables /\ t.vs_labels = u.vs_labels` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u`
       mp_tac >> simp[venom_state_component_equality] >> metis_tac[]) >>
  `LENGTH (TAKE 4 (Keccak_256_w64 bs)) = 4` by
    simp[LENGTH_TAKE, LENGTH_Keccak_256_w64] >>
  `32 + 32 * word_size (LENGTH (TAKE 4 (Keccak_256_w64 bs))) < dimword (:256)` by
    simp[vfmConstantsTheory.word_size_def, dimword_def] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32 + 32 * word_size (LENGTH (TAKE 4 (Keccak_256_w64 bs)))))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule literal_bytelike_alloca_mem >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!name a len. local_region cenv es.scopes s0 name a len ==>
    local_region cenv es.scopes u name a len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[]) >>
  drule_all literal_bytelike_run >> strip_tac >>
  gvs[vfmConstantsTheory.word_size_def] >>
  conj_tac
  >- (`vv_post H ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es sa sb s0
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf))
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
        (irule (SRULE [expr_type_def]
           (Q.INST [`e` |-> `Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]`]
             (SPEC_ALL literal_memory_vv_post))) >>
         goal_assum (drule_at Any) >>
         simp[post_value_type_def, lowered_value_type_def, expr_type_def,
              is_word_type_def, vyperValueTheory.evaluate_type_def,
              val_footprint_def, valueEncodingDefsTheory.val_wf_def,
              valueEncodingDefsTheory.val_in_memory_def,
              type_memory_size_def, compatible_bound_def,
              type_slot_size_def, vfmConstantsTheory.word_size_def,
              stmt_state_rel_inst_idx, lookup_var_def, local_region_def] >>
         fs[local_region_def, lookup_var_def] >> rpt conj_tac >> metis_tac[]) >>
      gvs[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def, vv_own_def,
           expr_val_rel_def, expr_val_at_def, expr_val_own_def, lookup_var_def,
           local_region_def, storage_holds_def, immutable_holds_def,
           eval_operand_def, contract_storage_def, contract_transient_def,
           post_value_type_def, lowered_value_type_def, expr_type_def,
           base_ptr_def, pure_frame_def, locals_kept_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[vv_store_bound_def, base_ptr_def, read_result_def,
           vyperValueTheory.evaluate_type_def, eval_operand_def, lookup_var_def,
           type_slot_size_def, val_store_size_def, return_def,
           type_memory_size_def, vfmConstantsTheory.word_size_def] >>
      `alloca_next_valid t` by (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
      fs[venomMemDefsTheory.alloca_next_valid_def, eval_operand_def,
         lookup_var_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (conj_tac
      >- (simp[ptr_vv_ok_def, base_ptr_def, read_result_def, return_def,
               ptr_mem_ok_def, vyperValueTheory.evaluate_type_def,
               vfmConstantsTheory.word_size_def, val_store_size_def,
               val_footprint_def, type_slot_size_def] >> strip_tac >>
          rpt strip_tac >> irule literal_clean_representation_robust >>
          conj_tac >- simp[val_wf_def, type_memory_size_def, vfmConstantsTheory.word_size_def] >>
          goal_assum (drule_at Any) >>
          simp[val_in_memory_def, val_wf_def, val_footprint_def,
               vfmConstantsTheory.word_size_def, IN_DIFF] >> decide_tac) >>
      simp[ptr_buf_ok_def, lowered_value_type_def, expr_type_def,
           type_memory_bytes_def, type_memory_size_def, vfmConstantsTheory.word_size_def,
           vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
  `allocation_growth s0 t` by (drule run_inst_seq_allocation_growth >> simp[]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[allocationGrowthTheory.allocation_growth_def, allocas_from_def] >> rpt strip_tac >>
     Cases_on `FLOOKUP s0.vs_allocas aid`
     >- (gvs[] >>
         qpat_x_assum `!id region_base region_size. FLOOKUP u.vs_allocas id = SOME (region_base,region_size) /\ FLOOKUP s0.vs_allocas id = NONE ==> _`
           (qspecl_then [`aid`, `b`, `sz`] mp_tac) >> simp[]) >>
     rename1 `FLOOKUP s0.vs_allocas aid = SOME entry` >>
     `FLOOKUP u.vs_allocas aid = SOME entry` by metis_tac[] >>
     Cases_on `entry` >> gvs[] >> first_x_assum irule >> goal_assum drule) >>
  `t.vs_call_ctx = s0.vs_call_ctx /\
   t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient` by
    (irule literal_bytelike_ptr_nonmemory_frame >> metis_tac[]) >>
  `t.vs_immutables = s0.vs_immutables` by
    (irule literal_bytelike_ptr_immutables_frame >> metis_tac[]) >>
  irule unwrap_slot_copy_ghost_inv_at >>
  simp[] >> conj_tac
  >- (`ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
      fs[ghost_inv_at_def, stor_taint_ok_at_def, pure_frame_def]) >>
  qexistsl [`G0`, `func`, `64`, `s0`, `sa`, `w2n w`, `tn0`] >>
  simp[op_taint_def, IN_DIFF] >> rpt conj_tac >>
  fs[stmt_state_rel_def, regions_disjoint_def] >> metis_tac[]
QED
