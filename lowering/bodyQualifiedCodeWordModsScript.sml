(* Force a linked immutable word at the literal offset resolved by the
   qualified lookup.  Loading changes only registers and the cursor. *)
Theory bodyQualifiedCodeWordMods
Ancestors
  bodyFullPostsMods bodyFullUnwrapRun fragGasOriginPtrDead
  exprPtrCtorCodeLoad exprPtrCodeCopyLoad exprSimBopRestWordLoadSafety
  bodyPtrSignedConvertSourceFrame representationCleanPtr entrySinkExtraction
  exprSimCopy exprSimStorageCopy exprSimProps exprSimMemDefs stateRelProj
  emitHelperProps memSafeRun loweringStateRelDefs arithmetic words pred_set
  list context venomState venomInst ptrDiscipline bodyPtrDefs bodyInvSplit
  bodyFullShadowBodyInv exprLoweringProps loweringSlice finite_map
  vyperStorageFootprint exprLowering loweringPosts

Theorem code_word_load_shape[local]:
  compile_imm_load_word ctor imm arg sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> DALLOCA)
    (emitted_insts sa sb)
Proof
  Cases_on `ctor` >> strip_tac
  >- (drule copy_ctor_load_shape >> simp[EVERY_MEM] >>
      strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      strip_tac >> gvs[is_terminator_def]) >>
  fs[compile_imm_load_word_runtime] >> drule emitted_insts_emit_op >>
  simp[mk_inst_def,is_terminator_def]
QED

(* Both pointer-checked loaders return the result of the same physical run
   used by the ordinary loader, so we can recover its read-only frame. *)
Theorem code_word_run[local]:
  compile_imm_load_word ctor imm (Lit a) sa = (op,sb) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (ctor ==> w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
    (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
       copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE)) ==>
  ?Gf tf u.
    copy_runtime_frame sa s sb u /\ u.vs_memory = s.vs_memory /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tf /\
    eval_operand op u = SOME (immutable_copy_read ctor a s) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
                               op_taint tf (Var x) = op_taint tn (Var x))
Proof
  Cases_on `ctor` >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `copy_old_operand sa (Lit a) /\ eval_operand (Lit a) s = SOME a /\
   op_taint tn (Lit a) = {} /\ op_prov G (Lit a) = NONE` by
     simp[copy_old_operand_def,eval_operand_def,op_taint_def,op_prov_def]
  >- (drule copy_ctor_load >> disch_then (qspecl_then [`s`,`a`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
      drule_all code_copy_ctor_load >>
      disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
      `s with vs_inst_idx := s.vs_inst_idx = s` by
        simp[venom_state_component_equality] >>
      pop_assum (fn cursor =>
        qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `s.vs_inst_idx` (assume_tac o PURE_REWRITE_RULE [cursor]))) >>
      qexistsl [`Gf`,`tnf`,`t`] >> gvs[copy_runtime_frame_def]) >>
  drule_all copy_runtime_load >> strip_tac >>
  drule_all code_copy_runtime_load >>
  disch_then (qspecl_then [`func`,`PG`,`G`,`D`] strip_assume_tac) >>
  `s with vs_inst_idx := s.vs_inst_idx = s` by simp[venom_state_component_equality] >>
  pop_assum (fn cursor =>
    qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` (assume_tac o PURE_REWRITE_RULE [cursor]))) >>
  qexistsl [`Gf`,`tnf`,`t`] >> gvs[copy_runtime_frame_def]
QED

Theorem code_word_immutable_frame[local]:
  immutable_frame_mods func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  immutable_frame_mods func cenv cx es t
Proof
  rw[immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def]
  >- (irule immutables_rel_mem_agree >> qexists `s` >> simp[]) >>
  irule immutable_alloca_sep_fields >> qexistsl [`s`,`es`] >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists `id` >>
  fs[local_region_def,local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem code_word_ghost_frame[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm ==>
  ghost_inv_at_mods D lo d cenv cx es Gf tf t
Proof
  simp[ghost_inv_at_mods_def,local_ptrs_reserved_def,stor_taint_ok_at_def,
       allocas_from_def] >> rpt strip_tac
  >- (gvs[ptr_covers_def] >> metis_tac[])
  >- metis_tac[]
  >- (Cases_on `d` >- gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def,ptr_covers_def] >> metis_tac[])
  >> metis_tac[]
QED

Theorem ctor_word_bits[local]:
  is_word_type ty /\ evaluate_type tenv ty = SOME rty /\ value_has_type rty v /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory rty v (w2n a) mem) ==>
  immutable_copy_read T a s = typed_val_to_w256 rty v /\
  mem_word_taint M (w2n a) = {}
Proof
  strip_tac >>
  `!mem. mem_agree_outside M s.vs_memory mem ==>
         mem_word_at (w2n a) mem = typed_val_to_w256 rty v` by
    (rpt strip_tac >> irule val_in_memory_word_type >>
     conj_tac >- (qexistsl [`ty`,`tenv`] >> simp[]) >> simp[]) >>
  conj_tac
  >- (simp[immutableCopyExecutionTheory.immutable_copy_read_def,
           GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
      first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_then assume_tac robust_mem_word_at_clean >>
  simp[mem_word_taint_def,EXTENSION] >> gen_tac >>
  Cases_on `x < 32` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

(* The qualified raw certificate supplies the represented word (runtime),
   or the robust representation in the selected owner's memory (ctor).
   Neither mode changes the active compile environment. *)
Theorem qualified_code_word_read_mods:
  unwrap_value cenv (LocatedValue (post_value_type cenv e) (mk_ptr (Lit a) LocCode))
    sa = (op,sb) /\
  is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  value_has_type rty v /\ ee.scopes = es.scopes /\
  (~cenv.ce_is_ctor ==> w2n a + 32 <= LENGTH s0.vs_data_section /\
    immutable_copy_read F a s0 = typed_val_to_w256 rty v) /\
  (cenv.ce_is_ctor ==> w2n a + 32 <= lo /\
    !mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
          val_in_memory rty v (w2n a) mem) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s0 /\ immutable_frame_mods func cenv cx ee s0 /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G0 tn0 s0) ==>
  ?z G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK z,G',tn') /\
    expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit a) sa = (op,sb)` by
    fs[unwrap_value_def,compile_ptr_load_def,mk_ptr_def] >>
  `cenv.ce_is_ctor ==> immutable_copy_read T a s0 = typed_val_to_w256 rty v /\
                      mem_word_taint tn0.t_mem (w2n a) = {}` by
    (strip_tac >> irule ctor_word_bits >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexistsl [`get_tenv cx`,`post_value_type cenv e`] >> simp[]) >> simp[]) >>
  `cenv.ce_is_ctor ==> !base. cenv.ce_imm_alloca = SOME base ==>
     eval_operand base s0 = SOME 0w /\ copy_old_operand sa base /\
     op_taint tn0 base = {} /\ op_prov G0 base = NONE` by
    (strip_tac >> qx_gen_tac `region` >> strip_tac >>
     `w2n a + 32 <= lo` by metis_tac[] >>
     `lo <> 0` by decide_tac >>
     conj_tac
     >- (drule stmt_state_rel_immutable_base_zero >>
         simp[immutable_base_zero_def] >> metis_tac[]) >>
     Cases_on `region` >> simp[copy_old_operand_def,op_taint_def,op_prov_def] >>
     conj_tac >- metis_tac[local_ptrs_reserved_imm_base] >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     qpat_assum `!x. lo <> 0 /\ _ ==> FLOOKUP G0 x = NONE /\ _`
       (drule_all_then strip_assume_tac) >> fs[op_taint_def]) >>
  qabbrev_tac `D0 = <|d_stor := (\a st. {}); d_trans := (\a st. {});
                      d_imm := (\im. {}); d_ret := (\ret. {})|>` >>
  `?Gf tf u.
    copy_runtime_frame sa s0 sb u /\ u.vs_memory = s0.vs_memory /\
    inst_seq_ptr D0 lo ctx func PG G0 tn0 (emitted_insts sa sb) s0 Gf tf /\
    eval_operand op u = SOME (immutable_copy_read cenv.ce_is_ctor a s0) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn0.t_mem /\ tf.t_stor = tn0.t_stor /\
    tf.t_trans = tn0.t_trans /\ tf.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
                               op_taint tf (Var x) = op_taint tn0 (Var x))` by
    (irule code_word_run >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (irule rest_word_ptr_load_mem_ok >>
     qexistsl [`a`,`Lit a`,`cenv.ce_is_ctor`,`cenv.ce_imm_alloca`,`LocCode`,`op`] >>
     simp[compile_ptr_load_def,eval_operand_def] >>
     Cases_on `cenv.ce_imm_alloca` >> fs[] >> rpt strip_tac >> fs[] >> decide_tac) >>
  drule_then assume_tac code_word_load_shape >>
  `run_inst_seq (emitted_insts sa sb) s0 = OK u /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[copy_runtime_frame_def,same_blocks_def] >>
  drule run_inst_seq_preserves_entry_control >>
  impl_tac >- fs[EVERY_MEM] >> strip_tac >>
  qabbrev_tac `z = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK z,Gf,tf)` by
    (qunabbrev_tac `z` >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     simp[] >> qexistsl [`emitted_insts sa sb`,`sa`] >> simp[] >>
     reverse conj_tac >- fs[EVERY_MEM] >>
     rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >> fs[EVERY_APPEND]) >>
  `alloca_history func z` by
    (qunabbrev_tac `z` >> irule emitted_alloca_history >>
     simp[] >> qexistsl [`emitted_insts sa sb`,`s0`,`sa`] >> fs[EVERY_MEM]) >>
  `z = s0 with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|>` by
    fs[copy_runtime_frame_def,copy_static_def,Abbr `z`,venom_state_component_equality] >>
  `eval_operand op z = SOME (typed_val_to_w256 rty v)` by
    (Cases_on `op` >> Cases_on `cenv.ce_is_ctor` >>
     fs[Abbr `z`,eval_operand_def,lookup_var_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s0` by
    fs[copy_runtime_frame_def,Abbr `z`,lookup_var_def] >>
  `z.vs_memory = s0.vs_memory /\ z.vs_data_section = s0.vs_data_section /\
   z.vs_allocas = s0.vs_allocas /\ z.vs_alloca_next = s0.vs_alloca_next /\
   z.vs_fmp = s0.vs_fmp /\ z.vs_initial_fmp = s0.vs_initial_fmp /\
   z.vs_call_ctx = s0.vs_call_ctx /\ z.vs_accounts = s0.vs_accounts /\
   z.vs_transient = s0.vs_transient /\ z.vs_immutables = s0.vs_immutables` by
    fs[copy_runtime_frame_def,copy_static_def,Abbr `z`,venom_state_component_equality] >>
  qexistsl [`z`,`Gf`,`tf`] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac
  >- (drule gas_origin_ptr_path_dead_mono >> simp[Abbr `D0`])
  >- (simp[expr_post_mods_def] >> conj_tac
      >- (simp[expr_post_def,expr_val_rel_def,expr_val_at_def,expr_val_own_def,
               pure_frame_def] >> conj_tac
          >- (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s0`,`sa`] >> simp[]) >>
          irule locals_kept_mem >> simp[]) >>
      irule code_word_immutable_frame >> qexistsl [`s0`,`sa`] >> simp[])
  >- simp[expr_store_bound_word]
  >- fs[Abbr `z`]
  >- fs[Abbr `z`]
  >- first_assum ACCEPT_TAC
  >- (strip_tac >> fs[allocas_below_fmp_def] >> first_assum ACCEPT_TAC)
  >- simp[]
  >- (irule code_word_ghost_frame >> qexistsl [`G0`,`s0`,`sa`,`tn0`] >> simp[])
  >- simp[ptr_val_ok_word]
  >> simp[ghost_kept_at_def]
QED
