(* The last instruction of the Concat prefix and the self-anchored fold entry. *)
Theory bodyConcatZeroEntryMods
Ancestors
  bodyConcatFrameLawsMods bodyFullBuiltinConcatZero bodyECRecoverWriteFrameMods
  bodyFullIfExpReach bodyPtrMakeArrayPrimitiveInstall bodyFullHashKeccakFixed
  bodyInvCodeProps wordLoadStorePtr ghostPcTransportPtr reasonCopySourcePtr
  decoderGhostFramePtr allocasBelowFmpUpdatesProps fragGasOriginPtrLoop
  exprSimAbiEncodeMemoryLength gasShadowState bodyMemoryDefs
  vyperStorageFootprint stateRelProj emitHelperProps contextRawReachable
  contextCodegenRelProps venomMemProps arithmetic finite_map pred_set words
  fragGasOriginPtr venomInst venomState venomExecSemantics exprLoweringProps
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit bodyPtrDefs compileEnv
  loweringStateRelDefs bodyConcatCutsMods freshWrites list alist
  fragExec ptrDiscipline bodyFullUnwrapRun valueEncodingDefs gasExplicitSites
  bodyFullPredsMods vyperAST vyperExprEffects vyperState

Theorem concat_zero_reachable[local]:
  emit_void MSTORE [Var ov;Lit 0w] s3 = ((),s4) /\ fn_has_code s3 s4 func /\
  t3.vs_current_bb = s3.cs_current_bb /\ t3.vs_inst_idx = LENGTH s3.cs_current_insts /\
  lookup_var ov t3 = SOME ow /\
  t4 = (mstore (w2n ow) 0w t3 with vs_inst_idx := LENGTH s4.cs_current_insts) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK t3,G,tn) /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) ==>
  !fn inst z. frag_reachable ctx func t4 fn inst z ==> dalloca_fmp_headroom inst z
Proof
  strip_tac >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst s3.cs_next_id MSTORE [Var ov;Lit 0w] []` >>
  `active_inst func i t3` by (irule lookup_instruction_active >> simp[]) >>
  `!j. active_inst func j t3 ==> frag_reachable ctx func s0 func j t3` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     drule ifexp_ptr_path_reachable >> disch_then (qspec_then `t3` mp_tac) >>
     simp[Abbr `i`,mk_inst_def]) >>
  `i.inst_opcode <> INVOKE` by simp[Abbr `i`,mk_inst_def] >>
  `step_inst 0 ctx i t3 = OK (mstore (w2n ow) 0w t3)` by
    (simp[step_inst_non_invoke] >> simp[Abbr `i`,step_MSTORE,eval_operand_def]) >>
  `!j. active_inst func j t4 ==> frag_reachable ctx func t3 func j t4` by
    (rpt gen_tac >> strip_tac >>
     `t4 = (mstore (w2n ow) 0w t3 with vs_inst_idx := SUC t3.vs_inst_idx)` by simp[] >>
     pop_assum SUBST_ALL_TAC >>
     irule frag_reachable_next >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`0`,`i`] >> simp[frag_reachable_start] >>
     simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  rpt gen_tac >> strip_tac >>
  `frag_reachable ctx func t3 fn inst z` by
    (drule frag_reachable_trans >> disch_then irule >> simp[]) >>
  `frag_reachable ctx func s0 fn inst z` by
    (qpat_assum `frag_reachable ctx func t3 fn inst z`
       (mp_tac o MATCH_MP frag_reachable_trans) >> disch_then irule >> simp[]) >>
  qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _` irule >>
  qexists `fn` >> first_assum ACCEPT_TAC
QED

Theorem concat_zero_single_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn t3 /\ local_ptrs_rel func ce es.scopes t3 /\
  (!name b n. local_region ce es.scopes t3 name b n ==> regions_disjoint (w2n ow) 64 b n) /\
  tn4.t_var = tn.t_var /\ tn4.t_stor = tn.t_stor /\
  tn4.t_trans = tn.t_trans /\ tn4.t_imm = tn.t_imm /\
  tn4.t_mem = tn.t_mem DIFF {i | w2n ow <= i /\ i < w2n ow+32} ==>
  ghost_inv_at D 0 d ce cx es G tn4
    (mstore (w2n ow) 0w t3 with vs_inst_idx := k)
Proof
  strip_tac >> rewrite_tac[ghost_inv_at_inst_idx] >>
  irule ghost_inv_at_mstore_clean >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (qexists `func` >> first_assum ACCEPT_TAC) >>
  qexists `tn` >> simp[] >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def,allocas_from_def]) >>
  simp[ghost_inv_at_def,allocas_from_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem concat_zero_registered[local]:
  immutable_frame_mods func ce cx es t /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (off,64) ==>
  (ce.ce_is_ctor ==> !src tops name tv v p.
    ALOOKUP ce.ce_modules src = SOME tops /\
    FLOOKUP (ce with ce_module := src).ce_module_vars (src,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off 32 p (type_memory_size tv))
Proof
  simp[immutable_frame_mods_def,immutable_alloca_sep_mods_def] >>
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [immutable_alloca_sep_def])) >>
  qpat_assum `_ ==> !name tv v off. _` (mp_tac o SIMP_RULE (srw_ss()) []) >>
  asm_rewrite_tac[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`p`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!inst b sz. _ ==> regions_disjoint p _ b sz`
    (qspecl_then [`oinst`,`off`,`64`] mp_tac) >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem concat_zero_entry_mods:
  emit_void MSTORE [Var ov;Lit 0w] s3 = ((),s4) /\
  emit_void MSTORE [Var ov;Lit 0w] h3 = ((),h4) /\ gas_shadow_state s3 h3 /\
  ci_mono sa s3 /\ fn_has_code sa s4 func /\ fn_inst_ids_distinct func /\
  concat_loop_code_mods (ctx,hctx,func,hfunc) ce (dv,ov,ow,binst,oinst,B,bsz)
    args (s4,s5,h4,h5) /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx hctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods ce cx env es /\
  (!e ee. MEM e args /\ expr_sim_inv_mods mods ce cx env ee ==>
         expr_body_pre_mods mods ce cx env e ee) /\
  body_exprs_full_ok_mods mods exps cx args /\
  EVERY (\e. is_bytestring_type (expr_type e) \/
              ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
  (pure ==> ~EXISTS expr_has_effect args) /\
  32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
  32 + concat_data_bound 0 (MAP expr_type args) <= bsz /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es t3 /\ immutable_frame_mods func ce cx es t3 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn t3) /\
  (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
    (s0,G0,tn0) [] (OK t3,G,tn)) /\
  ~t3.vs_halted /\ t3.vs_current_bb = s3.cs_current_bb /\
  t3.vs_inst_idx = LENGTH s3.cs_current_insts /\
  alloca_history func t3 /\ allocas_from lo t3 /\ s0.vs_alloca_next <= t3.vs_alloca_next /\
  lookup_var bv t3 = SOME (n2w B) /\ lookup_var dv t3 = SOME (n2w (B+32)) /\
  lookup_var ov t3 = SOME ow /\
  ptr_covers G tn bv t3 bsz /\ ptr_covers G tn dv t3 (bsz-32) /\ ptr_covers G tn ov t3 64 /\
  not_fresh_at s3 bv /\ not_fresh_at s3 dv /\ not_fresh_at s3 ov /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\ binst.inst_id < s4.cs_next_id /\
  FLOOKUP t3.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\ oinst.inst_id < s4.cs_next_id /\
  FLOOKUP t3.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  lo <= B /\ lo <= w2n ow /\ B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
  B+bsz <= t3.vs_alloca_next /\ w2n ow+64 <= t3.vs_alloca_next /\
  regions_disjoint B bsz (w2n ow) 64 /\
  (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
    regions_disjoint B bsz b n /\ regions_disjoint (w2n ow) 64 b n) /\
  (!name b n. local_region ce es.scopes t3 name b n ==>
    regions_disjoint B bsz b n /\ regions_disjoint (w2n ow) 64 b n) /\
  return_buf_frame d ce s3 t3 /\ local_ptrs_reserved ce s3 /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
  t3.vs_memory = s0.vs_memory /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!aid e. FLOOKUP s0.vs_allocas aid = SOME e ==> FLOOKUP t3.vs_allocas aid = SOME e) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t3 = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ?t4 tn4.
    concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,ce,pure)
      (DF,lo,d,ctx,hctx,PG,func,hfunc) (dv,ov,ow,binst,oinst,B,bsz)
      (es,s4,t4,G,tn4) args (s5,h4,h5) (es,s4,t4,G,tn4) [] 0 /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK t4,G,tn4)) /\
    gas_shadow_state s4 h4 /\ ci_mono sa s4 /\
    not_fresh_at s4 bv /\ lookup_var bv t4 = SOME (n2w B) /\ ptr_covers G tn4 bv t4 bsz /\
    FLOOKUP t4.vs_allocas binst.inst_id = SOME (B,bsz) /\
    FLOOKUP t4.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    s0.vs_alloca_next <= t4.vs_alloca_next /\ B+bsz <= t4.vs_alloca_next /\
    (!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id ==>
       regions_disjoint b n B bsz /\ regions_disjoint b n (w2n ow) 64) /\
    (!name b n. local_region ce es.scopes s0 name b n ==>
       regions_disjoint b n B bsz /\ regions_disjoint b n (w2n ow) 64) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t4 = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn4 (Var x) = op_taint tn0 (Var x)) /\
    (!aid e. FLOOKUP s0.vs_allocas aid = SOME e ==> FLOOKUP t4.vs_allocas aid = SOME e) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn4 /\
    (!p n. regions_disjoint p n (w2n ow) 32 ==>
      mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory)
Proof
  strip_tac >>
  `ci_mono s3 s4` by
    (qspecl_then [`MSTORE`,`[Var ov;Lit 0w]`,`s3`] mp_tac ci_mono_emit_void >> simp[]) >>
  `cs_extends sa s3 /\ cs_extends s3 s4 /\ s3.cs_next_var <= s4.cs_next_var` by
    (fs[ci_mono_def]) >>
  `fn_has_code s3 s4 func` by (drule_all fn_has_code_split >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_all concat_offset_zero_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx hctx`,`PG`]
    (qx_choosel_then [`t4`,`tn4`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "machine"
QED

Resume concat_zero_entry_mods[machine]:
  `(!x. lookup_var x t4 = lookup_var x t3 /\ op_taint tn4 (Var x) = op_taint tn (Var x)) /\
    t4.vs_allocas = t3.vs_allocas /\ t4.vs_alloca_next = t3.vs_alloca_next /\
    t4.vs_data_section = t3.vs_data_section /\
    LENGTH t3.vs_memory <= LENGTH t4.vs_memory /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t4)` by
    (qpat_assum `t4 = _` SUBST1_TAC >>
     rpt conj_tac
     >- simp[lookup_var_def,mstore_def,op_taint_def]
     >- simp[mstore_def]
     >- simp[mstore_def]
     >- simp[mstore_def]
     >- simp[NoAsms,abi_encode_mstore_memory_length] >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  `tn4.t_mem SUBSET tn.t_mem` by simp[] >>
  `!name b n. local_region ce es.scopes t4 name b n <=> local_region ce es.scopes t3 name b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >> simp[]) >>
  `!p n. regions_disjoint p n (w2n ow) 32 ==>
    mem_bytes_at p n t4.vs_memory = mem_bytes_at p n t3.vs_memory` by
    (pure_rewrite_tac[regions_disjoint_def] >>
     qpat_assum `!p n. p+n <= w2n ow \/ _ ==> _` ACCEPT_TAC) >>
  `ptr_covers G tn4 bv t4 bsz /\ ptr_covers G tn4 dv t4 (bsz-32) /\
    ptr_covers G tn4 ov t4 32` by
    (rpt conj_tac >> irule ptr_covers_frame >> qexistsl [`G`,`t3`,`tn`] >> simp[] >>
     irule ptr_covers_mono >> qexists `64` >> simp[]) >>
  `not_fresh_at s4 bv /\ not_fresh_at s4 dv /\ not_fresh_at s4 ov` by
    (rpt conj_tac >> irule not_fresh_at_mono >> qexists `s3` >> simp[]) >>
  `local_ptrs_reserved ce s4 /\ return_buf_frame d ce s4 t4` by
    (conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `s3` >> simp[]) >>
     irule return_buf_frame_frame >> qexistsl [`ce`,`t3`,`s3`] >> simp[]) >>
  suspend "horizons"
QED

Resume concat_zero_entry_mods[horizons]:
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    concat_horizon_mods (ctx,func,ce,cx,lo,d) (H,DF H) (es,s4,t4,G,tn4)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     `ghost_inv_at (DF H) 0 d ce cx es G tn4 t4` by
       (qpat_assum `t4 = _` SUBST1_TAC >>
        irule concat_zero_single_ghost >> conj_tac
        >- (rpt strip_tac >>
            qpat_assum `!name b n. local_region ce es.scopes t3 name b n ==> _ /\ _`
              (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
        conj_tac >- (qexists `func` >> first_assum ACCEPT_TAC) >>
        qexistsl [`lo`,`tn`] >> simp[]) >>
     `immutable_frame_mods func ce cx es t4 /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn4 t4` by
       (irule ecrecover_write_frame_mods >> conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl [`G`,`w2n ow`,`32`,`es`,`t3`,`s3`,`tn`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC
        >- (rpt strip_tac >> simp[])
        >- (rpt gen_tac >>
            qpat_assum `!p n. regions_disjoint p n (w2n ow) 32 ==> _` (qspecl_then [`p`,`n`] mp_tac) >>
            simp[NoAsms,regions_disjoint_def,DISJ_COMM])
        >- (rpt strip_tac >> fs[SUBSET_DEF]) >>
        rpt strip_tac >>
        qpat_x_assum `FLOOKUP t3.vs_allocas binst.inst_id = _` kall_tac >>
        drule_all_then ACCEPT_TAC concat_zero_registered) >>
     `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t4` by
       (drule contract_inv_cenv_modules >> strip_tac >>
        qpat_assum `module_body_inv _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [module_body_inv_def]) >>
        qpat_assum `immutable_frame_mods _ _ _ _ t4`
          (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,immutables_rel_mods_def]) >>
        qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ t4`
          (qspecl_then [`src`,`tops`] mp_tac) >> simp[]) >>
     pure_rewrite_tac[concat_horizon_mods_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!H cenv cx es. _ ==> stmt_state_rel H ctx func cenv cx es t4` irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!name b n. local_region ce es.scopes t3 name b n ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  suspend "entry"
QED

Resume concat_zero_entry_mods[entry]:
  qabbrev_tac `scratch = (dv,ov,ow,binst,oinst,B,bsz)` >>
  `concat_live_mods (func,ce,lo) scratch (es,s4,t4,G,tn4) [] /\
   concat_old_frame_mods (func,ce,lo,pure) scratch (es,s4,t4,G,tn4) (es,s4,t4,G,tn4)` by
    (simp_tac bool_ss [Abbr `scratch`] >>
     irule (SIMP_RULE (srw_ss()) [mem_bytes_at_def]
       (Q.INST [`k` |-> `0`] concat_anchor_start_mods)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[]
     >- (qpat_assum `!name b n. local_region ce es.scopes t3 name b n ==> _ /\ _`
           (ACCEPT_TAC o REWRITE_RULE [regions_disjoint_def])) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  qexistsl [`t4`,`tn4`] >> conj_tac
  >- (simp[concat_loop_entry_mods_def,Abbr `scratch`] >> suspend "entry_facts") >>
  suspend "parent"
QED

Resume concat_zero_entry_mods[entry_facts]:
  rpt conj_tac
  >- (qpat_assum `pure ==> ~EXISTS _ _` mp_tac >> simp[EVERY_MEM,EXISTS_MEM])
  >- (rpt gen_tac >> strip_tac >> irule not_fresh_at_mono >> qexists `s3` >> simp[])
  >- (rpt gen_tac >> strip_tac >> irule not_fresh_at_mono >> qexists `s3` >> simp[]) >>
  qpat_assum `t4 = _` (SUBST1_TAC o SYM) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] _`
    (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
  rpt strip_tac >> drule_all_then ACCEPT_TAC concat_zero_reachable
QED

Resume concat_zero_entry_mods[parent]:
  rpt conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`G`,`t3`,`tn`] >> simp[])
  >- (qspecl_then [`s3`,`h3`] mp_tac
        (REWRITE_RULE [gas_shadow_compiles_def]
           (Q.INST [`opc` |-> `MSTORE`,`ops` |-> `[Var ov;Lit 0w]`] gas_shadow_compiles_emit_void)) >>
      simp[])
  >- drule_all_then ACCEPT_TAC ci_mono_trans >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid b n. aid < sa.cs_next_id /\ _ ==> _`
        (qspecl_then [`aid`,`b`,`n`] mp_tac) >> simp[regions_disjoint_def,DISJ_COMM])
  >- suspend "parent_locals" >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[]
QED

Resume concat_zero_entry_mods[parent_locals]:
  `!name b n. local_region ce es.scopes t3 name b n <=> local_region ce es.scopes s0 name b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name b n. local_region ce es.scopes t3 name b n ==> _`
    (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[regions_disjoint_def,DISJ_COMM]
QED

Finalise concat_zero_entry_mods
