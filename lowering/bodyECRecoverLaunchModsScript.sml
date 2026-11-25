(* Linked launch certificate for the two ECRecover scratch buffers. *)
Theory bodyECRecoverLaunchMods
Ancestors
  bodyMakeBufferInitMods bodyECRecoverInputStoresMods bodyECRecoverZeroStoreMods
  bodyECRecoverWriteFrameMods bodyECRecoverCodeCutsMods
  bodyShaRegisteredFrameMods bodyFullPostsMods bodyFullShadowBodyInv
  gasShadowState stateRelProj freshWrites bodyFullHashKeccakFixed
  bodyInvSplit bodyPtrDefs exprLoweringProps loweringPosts loweringStateRelDefs
  bodyMemoryDefs bodyFullAllocaFresh bodyFullUnwrapRun bodyFullUnwrapSlotPost
  exprSimPrecompiles exprSimAlloc exprSimProps ptrDiscipline ghostPcTransportPtr
  fragGasOriginPtr fragGasSeqPtr fragExec venomExecSemantics venomState venomInst
  vyperStorageTrace vyperStorageFootprint compileEnv finite_map pred_set list words
Libs
  monadsyntax

Theorem ecrecover_launch_mods:
  compile_alloc_buffer 128 sf = (ib,sa) /\
  emit_void MSTORE [ib.buf_operand; h] sa = ((),sb) /\
  (do dst <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst; v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst; r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [dst; sig] od) sd = ((),sp) /\
  compile_alloc_buffer 32 sp = (ob,sm) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] sm = ((),sz) /\
  fn_has_code sf sz func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
       not_fresh_at sf x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
       not_fresh_at sf x) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!q. x = Var q ==> not_fresh_at sf q)) [h;v;r;sig] /\
  alloca_history func s /\ return_buf_frame d cenv sf s /\
  ~s.vs_halted /\ s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?t Gf tnf qi qo wi wo.
    ib.buf_operand = Var qi /\ ob.buf_operand = Var qo /\
    not_fresh_at sz qi /\ not_fresh_at sz qo /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sz.cs_current_bb /\
    t.vs_inst_idx = LENGTH sz.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    local_ptrs_reserved cenv sz /\ return_buf_frame d cenv sz t /\
    lookup_var qi t = SOME wi /\ lookup_var qo t = SOME wo /\
    lo <= w2n wi /\ lo <= w2n wo /\
    ptr_covers Gf tnf qi t 128 /\ ptr_covers Gf tnf qo t 32 /\
    FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n wi,128) /\
    FLOOKUP t.vs_allocas sp.cs_next_id = SOME (w2n wo,32) /\
    w2n wi+128 < dimword (:256) /\ w2n wo+32 < dimword (:256) /\
    w2n wi+128 <= t.vs_alloca_next /\ w2n wo+32 <= t.vs_alloca_next /\
    regions_disjoint (w2n wi) 128 (w2n wo) 32 /\
    mem_bytes_at (w2n wi) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T /\
    mem_word_at (w2n wo) t.vs_memory = 0w /\
    (!i. w2n wi <= i /\ i < w2n wi+128 ==> i NOTIN tnf.t_mem) /\
    (!i. w2n wo <= i /\ i < w2n wo+32 ==> i NOTIN tnf.t_mem) /\
    (!x. not_fresh_at sf x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. aid < sf.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
      regions_disjoint (w2n wo) 32 b len) /\
    (!aid b len. aid < sf.cs_next_id /\
      FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n wo) 32 b len) /\
    wb_frame cenv es es sf s t /\ pure_frame cenv func es sf s t /\
    ghost_kept_at lo cenv es sf G tn s Gf tnf /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w] [qi]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]) (fn_insts func) /\
    (cenv.ce_is_ctor ==> !src tops name tv iv off.
       ALOOKUP cenv.ce_modules src = SOME tops /\
       FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n wo) 32 off (type_memory_size tv)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      immutable_frame_mods func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx es Gf tnf t) /\
    (!es0 sk s0 G0 tn0.
      sk.cs_next_var <= sf.cs_next_var /\
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn /\
      (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
        aid < sk.cs_next_id ==> off+len <= s.vs_alloca_next) /\
      (!name b len. local_region cenv es0.scopes s0 name b len ==>
        b+len <= s.vs_alloca_next) ==>
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gf tnf)
Proof
  strip_tac >>
  `(do emit_void MSTORE [ib.buf_operand; h];
       p1 <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [p1; v];
       p2 <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [p2; r];
       p3 <- emit_op ADD [ib.buf_operand; Lit 96w]; emit_void MSTORE [p3; sig] od) sa = ((),sp)` by
    (simp[comp_bind_def,comp_ignore_bind_def] >>
     map_every Cases_on [`emit_op ADD [ib.buf_operand; Lit 32w] sb`,
                         `emit_op ADD [ib.buf_operand; Lit 64w] sc`,
                         `emit_op ADD [ib.buf_operand; Lit 96w] sd`] >>
     fs[comp_bind_def,comp_ignore_bind_def]) >>
  drule_then strip_assume_tac ecrecover_input_stores_shape >>
  `ci_mono sf sa` by (qspecl_then [`128`,`sf`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sp sm` by (qspecl_then [`32`,`sp`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sz` by (qspecl_then [`MSTORE`,`[ob.buf_operand;Lit 0w]`,`sm`] mp_tac ci_mono_emit_void >> simp[]) >>
  `cs_extends sa sp` by (fs[cs_extends_def,same_blocks_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends sf sa /\ cs_extends sp sm /\ cs_extends sm sz` by fs[ci_mono_def] >>
  `fn_has_code sf sa func /\ fn_has_code sa sp func /\
   fn_has_code sp sm func /\ fn_has_code sm sz func` by
    (rpt conj_tac >> irule fn_has_code_mid >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`sz`,`sf`] >> simp[cs_extends_refl] >> metis_tac[cs_extends_trans]) >>
  `128 < dimword (:256) /\ 32 < dimword (:256)` by simp[dimword_def] >>
  `gas_shadow_state sf sf` by simp[gas_shadow_state_refl] >>
  drule_all (Q.INST [`cap` |-> `128`, `sha` |-> `sf`] make_buffer_init_frame_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`qi`,`ai`,`si`,`Gi`,`ti`] strip_assume_tac)) >>
  suspend "input_alloc_post"
QED

Resume ecrecover_launch_mods[input_alloc_post]:
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es si /\
   immutable_frame_mods func cenv cx es si` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ si /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es si /\ ghost_inv_at_mods (DF H) lo d cenv cx es Gi ti si` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ si /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp si` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ si`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `si.vs_current_bb = sa.cs_current_bb /\ si.vs_inst_idx = LENGTH sa.cs_current_insts /\
   alloca_history func si /\ s.vs_alloca_next <= si.vs_alloca_next` by
    fs[exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >>
  `sf.cs_next_var <= sa.cs_next_var /\ sp.cs_next_var <= sm.cs_next_var /\
   sm.cs_next_var <= sz.cs_next_var /\ sp.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `!x. not_fresh_at sf x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x` by simp[] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x` by simp[] >>
  `!a. MEM a [h;v;r;sig] ==>
    eval_operand a si = eval_operand a s /\ op_taint ti a = {} /\
    (!l. a <> Label l) /\ (!q. a = Var q ==> not_fresh_at sa q)` by
    (qx_gen_tac `a` >> disch_tac >>
     qpat_assum `EVERY _ [h;v;r;sig]`
       (drule_then strip_assume_tac o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `a` >> fs[eval_operand_def,op_taint_def]) >>
  `eval_operand h si = SOME wh /\ eval_operand v si = SOME wv /\
   eval_operand r si = SOME wr /\ eval_operand sig si = SOME ws /\
   EVERY (\a. op_taint ti a = {} /\ (!l. a <> Label l) /\
     (!q. a = Var q ==> not_fresh_at sa q)) [h;v;r;sig]` by simp[] >>
  `w2n (n2w ai:bytes32) = ai` by (simp[w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `!aid b n. aid < sf.cs_next_id /\ FLOOKUP si.vs_allocas aid = SOME (b,n) ==>
              regions_disjoint ai 128 b n` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ si`
       (mp_then Any mp_tac state_allocations_disjoint) >>
     disch_then irule >> qexistsl_tac [`sf.cs_next_id`,`aid`] >> simp[] >> decide_tac) >>
  suspend "input_store"
QED

Resume ecrecover_launch_mods[input_store]:
  `(cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint ai 128 off (type_memory_size tv))` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ si`
       (mp_then Any mp_tac precompile_alloca_immutable_disjoint) >>
     disch_then (qspecl_then [`128`,`mk_inst sf.cs_next_id ALLOCA [Lit 128w] [qi]`,`ai`] mp_tac) >>
     qpat_x_assum `si = raw with vs_inst_idx := _` kall_tac >> simp[mk_inst_def] >>
     disch_then (mk_asm "active_sep") >> rpt strip_tac >>
     asm "active_sep" (qspecl_then [`name`,`tv`,`iv`,`off`] mp_tac) >> simp[]) >>
  qpat_assum `ib.buf_operand = Var qi`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  mp_tac (Q.INST [`s` |-> `si`, `G` |-> `Gi`, `tn` |-> `ti`, `root` |-> `qi`,
                  `old` |-> `sf`, `site` |-> `sf.cs_next_id`, `wi` |-> `n2w ai`]
                   ecrecover_input_stores_physical_mods) >>
  (impl_tac >-
    (qpat_x_assum `si = raw with vs_inst_idx := _` kall_tac >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`sfill`,`Gfill`,`tfill`] strip_assume_tac) >>
  qpat_x_assum `si = raw with vs_inst_idx := _` kall_tac >>
  `!p n. regions_disjoint ai 128 p n ==>
          mem_bytes_at p n sfill.vs_memory = mem_bytes_at p n si.vs_memory` by simp[] >>
  `!nm p n. local_region cenv es.scopes s nm p n <=>
              local_region cenv es.scopes si nm p n` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     rename1 `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var x) _)` >>
     `not_fresh_at sf x` by
       (qpat_assum `local_ptrs_reserved cenv sf`
          (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
        qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP cenv.ce_vars n1 =
            SOME (PtrVar (Var p) sz1) ==> not_fresh_at sf p /\ _`
          (qspecl_then [`name`,`name`,`x`,`sz'`,`sz'`] mp_tac) >> simp[]) >> simp[]) >>
  `pure_frame cenv func es sf si sfill` by
    (irule pure_frame_fresh_alloca >>
     conj_tac >-
       (rpt strip_tac >> qpat_assum `!p n. regions_disjoint ai 128 p n ==> _` irule >>
        qpat_assum `!name b n. local_region cenv es.scopes si name b n ==> _`
          (drule_then ACCEPT_TAC)) >>
     qexistsl_tac [`ai`,`sf.cs_next_id`,`[Lit 128w]`,`[qi]`,`128`] >>
     conj_tac >-
       (rpt strip_tac >> qpat_assum `!p n. regions_disjoint ai 128 p n ==> _` irule >>
        fs[regions_disjoint_def] >> decide_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es sfill /\ immutable_frame_mods func cenv cx es sfill /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es Gfill tfill sfill`
    by suspend "input_linked" >>
  suspend "output_alloc"
QED

Resume ecrecover_launch_mods[input_linked]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ si /\ _ /\ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ sfill /\ _`
    (drule_then strip_assume_tac) >>
  `!x. not_fresh_at sf x ==>
       lookup_var x sfill = lookup_var x si /\ FLOOKUP Gfill x = FLOOKUP Gi x /\
       op_taint tfill (Var x) = op_taint ti (Var x)` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `mid` |-> `es`, `sm` |-> `sf`,
       `D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`,
       `s` |-> `si`, `z` |-> `sfill`,
       `G` |-> `Gi`, `tn` |-> `ti`, `Gf` |-> `Gfill`, `tf` |-> `tfill`]
       sha_registered_frame_mods) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> simp[]
QED

Resume ecrecover_launch_mods[output_alloc]:
  `gas_shadow_state sp sp` by simp[gas_shadow_state_refl] >>
  `sf.cs_next_var <= sp.cs_next_var` by decide_tac >>
  `sf.cs_next_id < sp.cs_next_id` by decide_tac >>
  `!x. not_fresh_at sf x ==> not_fresh_at sp x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sp x` by simp[] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sp x` by simp[] >>
  mp_tac (Q.INST [`cap` |-> `32`, `sa` |-> `sp`, `sha` |-> `sp`,
    `buf` |-> `ob`, `shbuf` |-> `ob`, `shm` |-> `sm`, `ce` |-> `cenv`,
    `s` |-> `sfill`, `G0` |-> `Gfill`, `tn0` |-> `tfill`]
    make_buffer_init_frame_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`qo`,`ao`,`smem`,`Gmem`,`tmem`] strip_assume_tac) >>
  `smem.vs_current_bb = sm.cs_current_bb /\ smem.vs_inst_idx = LENGTH sm.cs_current_insts /\
   alloca_history func smem /\ sfill.vs_alloca_next <= smem.vs_alloca_next` by
    fs[exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >>
  `w2n (n2w ao : bytes32) = ao` by simp[w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `!x. not_fresh_at sp x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sp` >> simp[]) >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by simp[] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by simp[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es smem /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es Gmem tmem smem` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ smem /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  suspend "zero_store"
QED

Resume ecrecover_launch_mods[zero_store]:
  qpat_x_assum `smem = _ with vs_inst_idx := _` kall_tac >>
  `emit_void MSTORE [Var qo; Lit 0w] sm = ((),sz)` by
    (qpat_assum `ob.buf_operand = Var qo` (fn eq =>
       qpat_assum `emit_void MSTORE [ob.buf_operand; _] sm = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  mp_tac (Q.INST [`cm` |-> `sm`, `cz` |-> `sz`, `ce` |-> `cenv`,
    `s` |-> `smem`, `G` |-> `Gmem`, `tn` |-> `tmem`, `wo` |-> `(n2w ao : bytes32)`,
    `site` |-> `mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]`]
    ecrecover_zero_store_physical_mods) >>
  (impl_tac >-
    (qpat_assum `w2n (n2w ao : bytes32) = ao` (fn th => simp[NoAsms,mk_inst_def,th]) >>
     rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `MEM (mk_inst sp.cs_next_id ALLOCA _ _) _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [mk_inst_def]))))) >>
  disch_then (qx_choosel_then [`tout`,`Gout`,`tnout`] strip_assume_tac) >>
  `wb_frame cenv es es sp smem tout /\ pure_frame cenv func es sp smem tout` by
    (qpat_assum `!sk. sk.cs_next_id <= _ ==> wb_frame _ _ _ _ smem tout /\ _`
       (qspec_then `sp` mp_tac) >> simp[mk_inst_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es tout /\ immutable_frame_mods func cenv cx es tout /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx es Gout tnout tout`
    by suspend "output_linked" >>
  suspend "assembly"
QED

Resume ecrecover_launch_mods[output_linked]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ smem /\ _ /\ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ tout /\ _`
    (drule_then strip_assume_tac) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `mid` |-> `es`, `sm` |-> `sp`,
       `D` |-> `DF (H : (bool # bytes32 # type_value) list # num list)`,
       `s` |-> `smem`, `z` |-> `tout`,
       `G` |-> `Gmem`, `tn` |-> `tmem`, `Gf` |-> `Gout`, `tf` |-> `tnout`]
       sha_registered_frame_mods) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> simp[]
QED

Resume ecrecover_launch_mods[assembly]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK tout,Gout,tnout)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gi`,`si`,`ti`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gfill`,`sfill`,`tfill`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gmem`,`smem`,`tmem`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `local_ptrs_reserved cenv sz` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `not_fresh_at sm qi` by simp[] >>
  `not_fresh_at sz qi /\ not_fresh_at sz qo` by
    (conj_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es tout /\
   immutable_frame_mods func cenv cx es tout` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ tout /\ _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `FLOOKUP tout.vs_allocas sf.cs_next_id = SOME (ai,128)` by
    (qpat_assum `!aid b. FLOOKUP sfill.vs_allocas aid = SOME b ==> _`
       (qspec_then `sf.cs_next_id` mp_tac) >> simp[]) >>
  qpat_x_assum `sp.cs_next_id = sa.cs_next_id + 7` kall_tac >>
  `FLOOKUP tout.vs_allocas sp.cs_next_id = SOME (ao,32)` by simp[] >>
  `regions_disjoint ai 128 ao 32` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ tout`
       (mp_then Any irule state_allocations_disjoint) >>
     qexistsl_tac [`sf.cs_next_id`,`sp.cs_next_id`] >> simp[] >> decide_tac) >>
  suspend "retained_input"
QED

Resume ecrecover_launch_mods[retained_input]:
  `lookup_var qi smem = SOME (n2w ai) /\ ptr_covers Gmem tmem qi smem 128` by
    (conj_tac >- simp[] >> qpat_assum `ptr_covers Gfill tfill qi sfill 128`
       (mp_then Any irule decoderGhostFramePtrTheory.ptr_covers_frame) >> simp[]) >>
  `ptr_covers Gout tnout qi tout 128 /\ ptr_covers Gout tnout qo tout 32` by simp[] >>
  `regions_disjoint ao 32 ai 128` by (fs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at ai 128 tout.vs_memory = mem_bytes_at ai 128 sfill.vs_memory` by
    (qpat_assum `!b n. regions_disjoint (w2n (n2w ao)) 32 b n ==> _`
       (qspecl_then [`ai`,`128`] mp_tac) >> simp[]) >>
  `mem_bytes_at ai 128 tout.vs_memory =
     word_to_bytes wh T ++ word_to_bytes wv T ++ word_to_bytes wr T ++ word_to_bytes ws T` by
    (qpat_assum `mem_bytes_at (w2n (n2w ai : bytes32)) 128 sfill.vs_memory = _`
       (fn th => qpat_assum `w2n (n2w ai : bytes32) = ai` (assume_tac o (fn eq => PURE_REWRITE_RULE [eq] th))) >>
     simp[]) >>
  `ai + 128 <= sfill.vs_alloca_next` by simp[] >>
  `!i. ai <= i /\ i < ai + 128 ==> i NOTIN tnout.t_mem` by
    (rpt strip_tac >>
     `i < sfill.vs_alloca_next` by decide_tac >>
     `i NOTIN tfill.t_mem` by simp[] >>
     `i IN tmem.t_mem` by
       (qpat_assum `tnout.t_mem SUBSET tmem.t_mem` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
        disch_then (drule_then ACCEPT_TAC)) >>
     qpat_assum `!i. i IN tmem.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `!name b n. local_region cenv es.scopes tout name b n ==>
     regions_disjoint ao 32 b n` by
    (rpt strip_tac >>
     `local_region cenv es.scopes tout name b n <=> local_region cenv es.scopes smem name b n`
       by (irule local_region_lookup_cong >> simp[]) >>
     qpat_assum `!name b n. local_region cenv es.scopes smem name b n ==> _` irule >>
     qexists_tac `name` >> fs[]) >>
  `!aid b n. aid < sf.cs_next_id /\ FLOOKUP tout.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint ao 32 b n` by
    (rpt strip_tac >> qpat_assum `stmt_state_rel _ _ _ _ _ _ tout`
       (mp_then Any irule state_allocations_disjoint) >>
     qexistsl_tac [`sp.cs_next_id`,`aid`] >> asm_rewrite_tac[] >> decide_tac) >>
  suspend "old_frames"
QED

Resume ecrecover_launch_mods[old_frames]:
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sf si sfill` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ sfill /\ wb_frame _ _ _ _ si sfill /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sf s sfill` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s` (mp_then Any irule exprSimWordArgsTheory.wb_frame_trans) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`es`,`sf`,`si`] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es sfill` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ sfill /\ immutable_frame_mods _ _ _ _ sfill /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sp sfill tout` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ sfill` (mp_then Any irule exprSimWordArgsTheory.wb_frame_trans) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`es`,`sp`,`smem`] >> simp[]) >>
  `wb_frame cenv es es sf s tout` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s` (mp_then Any irule exprSimWordArgsTheory.wb_frame_trans) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`es`,`sp`,`sfill`] >> simp[] >> decide_tac) >>
  `!x. not_fresh_at sf x ==>
     lookup_var x sfill = lookup_var x s /\ FLOOKUP Gfill x = FLOOKUP G x /\
     op_taint tfill (Var x) = op_taint tn (Var x)` by simp[] >>
  `!x. not_fresh_at sf x ==>
     lookup_var x tout = lookup_var x s /\ FLOOKUP Gout x = FLOOKUP G x /\
     op_taint tnout (Var x) = op_taint tn (Var x)` by simp[] >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP tout.vs_allocas aid = SOME entry` by
    (rpt strip_tac >>
     `FLOOKUP si.vs_allocas aid = SOME entry` by simp[] >>
     `FLOOKUP sfill.vs_allocas aid = SOME entry` by simp[] >>
     qpat_assum `!a b. FLOOKUP sfill.vs_allocas a = SOME b ==> _`
       (drule_then mp_tac) >> simp[]) >>
  suspend "pure_and_immutable"
QED

Resume ecrecover_launch_mods[pure_and_immutable]:
  `pure_frame cenv func es sf s si` by simp[pure_frame_mem_eq] >>
  `pure_frame cenv func es sf s sfill` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`es`,`sf`,`si`] >> simp[]) >>
  `pure_frame cenv func es sf s smem` by
    (irule pure_frame_mem_tail >> qexists_tac `sfill` >> simp[]) >>
  `pure_frame cenv func es sf s tout` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`es`,`sp`,`smem`] >> simp[] >> decide_tac) >>
  `!aid off len. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
     mem_bytes_at off len tout.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint ai 128 off len` by
       (qpat_assum `!a b n. a < sf.cs_next_id /\ FLOOKUP s.vs_allocas a = SOME (b,n) ==> _`
          irule >> qexists_tac `aid` >> asm_rewrite_tac[]) >>
     `FLOOKUP tout.vs_allocas aid = SOME (off,len)` by
       (qpat_assum `!a entry. FLOOKUP s.vs_allocas a = SOME entry ==> FLOOKUP tout.vs_allocas a = SOME entry`
          (drule_then ACCEPT_TAC)) >>
     `regions_disjoint ao 32 off len` by
       (qpat_assum `!a b n. a < sf.cs_next_id /\ _ ==> regions_disjoint ao 32 b n`
          irule >> qexists_tac `aid` >> asm_rewrite_tac[]) >>
     qpat_assum `!b n. regions_disjoint (w2n (n2w ao)) 32 b n ==> _`
       (qspecl_then [`off`,`len`] mp_tac) >>
     qpat_assum `!b n. regions_disjoint ai 128 b n ==> _`
       (qspecl_then [`off`,`len`] mp_tac) >> simp[]) >>
  suspend "ghost_finish"
QED

Resume ecrecover_launch_mods[ghost_finish]:
  `lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `ghost_inv_at_mods _ lo _ _ _ _ G tn s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> first_assum ACCEPT_TAC) >>
  `lo <= sfill.vs_alloca_next` by fs[] >>
  `!es0 sk s0 G0 tn0.
      sk.cs_next_var <= sf.cs_next_var /\ ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn /\
      (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
        aid < sk.cs_next_id ==> off + len <= s.vs_alloca_next) /\
      (!name b len. local_region cenv es0.scopes s0 name b len ==> b + len <= s.vs_alloca_next) ==>
      ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gout tnout`
    by suspend "kept_chain" >>
  `ghost_kept_at lo cenv es sf G tn s Gout tnout` by suspend "kept_entry" >>
  `s.vs_alloca_next <= tout.vs_alloca_next /\ ai + 128 <= tout.vs_alloca_next` by (fs[] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !src tops name tv iv off. ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
     regions_disjoint ao 32 off (type_memory_size tv)` by suspend "constructor" >>
  qexistsl_tac [`tout`,`Gout`,`tnout`,`qi`,`qo`,`n2w ai`,`n2w ao`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `w2n (n2w ai : bytes32) = ai` (fn hi =>
    qpat_assum `w2n (n2w ao : bytes32) = ao` (fn ho => pure_rewrite_tac[hi,ho])) >>
  (first_assum ACCEPT_TAC ORELSE simp[])
QED

Resume ecrecover_launch_mods[kept_chain]:
  rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sk x ==> not_fresh_at sf x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sk` >> simp[]) >>
  `ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gi ti` by
    (irule alloc_buffer_ghost_kept_at >> qexistsl_tac [`G`,`ai+128`,`s`,`tn`] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gfill tfill` by
    (qpat_assum `!es0 sk s0 G0 tn0. _ /\ ghost_kept_at _ _ _ _ _ _ _ Gi ti ==> _`
       irule >> simp[] >> decide_tac) >>
  `ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gmem tmem` by
    (irule alloc_buffer_ghost_kept_at >> qexistsl_tac [`Gfill`,`ao+32`,`sfill`,`tfill`] >>
     simp[] >> rpt conj_tac >> rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  qpat_assum `!es0 sk s0 G0 tn0. ghost_kept_at _ _ _ _ _ _ _ Gmem tmem ==> _` irule >>
  first_assum ACCEPT_TAC
QED

Resume ecrecover_launch_mods[kept_entry]:
  first_assum irule >> pure_rewrite_tac[wordArgsPtrTheory.ghost_kept_at_refl, arithmeticTheory.LE_REFL] >>
  simp[NoAsms] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
       (mp_then Any irule body_local_region_frontier) >> qexists_tac `name` >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `alloca_inv s`
    (strip_assume_tac o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def]) >>
  rpt strip_tac >>
  qpat_assum `!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) ==> _`
    (drule_then assume_tac) >> decide_tac
QED

Resume ecrecover_launch_mods[constructor]:
  disch_tac >> rpt gen_tac >> strip_tac >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx es tout` by
    (qpat_assum `immutable_frame_mods func cenv cx es tout`
       (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def, immutable_alloca_sep_mods_def]) >>
     qpat_assum `!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==> _`
       (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def]) >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` (drule_then assume_tac) >>
  qpat_x_assum `!name tv v off. FLOOKUP _ _ = SOME (ImmutableLoc _) /\ _ ==> _`
    (qspecl_then [`name`,`tv`,`iv`,`off`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) ao 32` by
    (qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
       (qspec_then `mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]` mp_tac) >>
     qpat_assum `MEM (mk_inst sp.cs_next_id ALLOCA _ _) _`
       (fn th => simp[SIMP_RULE (srw_ss()) [mk_inst_def] th,mk_inst_def])) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Finalise ecrecover_launch_mods
