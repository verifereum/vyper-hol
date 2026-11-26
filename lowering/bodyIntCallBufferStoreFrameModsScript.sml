(* The physical suffix does not change the source endpoint or its horizon. *)
Theory bodyIntCallBufferStoreFrameMods
Ancestors
  bodyIntCallStagePacketMods bodyPtrMakeArrayCopyStateFrame
  bodyIfExpTypedImmFrameMods bodyPtrMakeArrayMemoryFrame
  bodyMemoryDefs assignTuplePtrCopyLen exprSimStorageCopy stateRelProj
  exprSimProps exprLoweringProps freshWrites typedMemoryCopy loweringStateRelDefs
  loweringPosts bodyPtrDefs ptrDiscipline venomMemDefs venomState
  bodyFullShadowBodyInv venomInst pred_set arithmetic

Theorem intcall_store_window[local]:
  typed_copy_frame dst nw z.vs_memory t.vs_memory /\ nw <= cap /\
  (!i. ~(dst <= i /\ i < dst+nw) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  !b n. b+n <= dst \/ dst+cap <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n z.vs_memory /\
    (!i. b <= i /\ i < b+n ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  simp[typed_copy_frame_def] >> strip_tac >> rpt gen_tac >> disch_tac >>
  conj_tac
  >- (first_assum irule >> decide_tac) >>
  gen_tac >> strip_tac >> first_assum irule >> decide_tac
QED

Theorem intcall_store_origin[local]:
  wb_frame cenv es0 mid sa s0 z /\ ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  t.vs_allocas = z.vs_allocas /\
  (!n b k. local_region cenv es0.scopes s0 n b k ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k z.vs_memory /\
    (!i. b <= i /\ i < b+k ==> (i IN tf.t_mem <=> i IN tn.t_mem))) /\
  (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,k) ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k z.vs_memory /\
    (!i. b <= i /\ i < b+k ==> (i IN tf.t_mem <=> i IN tn.t_mem))) ==>
  wb_frame cenv es0 mid sa s0 t /\ ghost_kept_at lo cenv es0 sa G0 tn0 s0 Gf tf
Proof
  strip_tac >>
  qpat_x_assum `wb_frame _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[wb_frame_def,ghost_kept_at_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid b k. aid < _ /\ _ ==> _ /\ _` drule_all >> simp[] >> metis_tac[])
  >- (irule locals_kept_regions_tail >> qexists_tac `z` >> simp[] >>
      rpt strip_tac >> qpat_assum `!n b k. local_region _ _ _ _ _ _ ==> _ /\ _` drule >> simp[])
  >- (rpt strip_tac >>
      rename1 `FLOOKUP s0.vs_allocas old = SOME (off,sz)` >>
      qpat_assum `!aid b k. aid < _ /\ _ ==> _ /\ _`
        (drule_all_then strip_assume_tac) >>
      `i IN tn.t_mem` by (first_assum (qspecl_then [`i`] mp_tac) >> simp[]) >>
      qpat_assum `!aid off sz j. _ ==> j IN tn0.t_mem`
        (qspecl_then [`old`,`off`,`sz`,`i`] mp_tac) >> simp[] >>
      disch_then irule >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!n b k. local_region _ _ _ _ _ _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  `i IN tn.t_mem` by metis_tac[] >>
  qpat_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` (drule_all_then ACCEPT_TAC)
QED

Theorem intcall_store_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx mid G tn z /\
  local_ptrs_rel func cenv mid.scopes z /\ local_ptrs_reserved cenv cu /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x. not_fresh_at cu x ==> lookup_var x t = lookup_var x z /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!n b k. local_region cenv mid.scopes z n b k ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k z.vs_memory /\
    (!i. b <= i /\ i < b+k ==> (i IN tf.t_mem <=> i IN tn.t_mem))) /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo z.vs_memory /\
  (!i. i < lo ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
  t.vs_accounts = z.vs_accounts /\ t.vs_call_ctx = z.vs_call_ctx /\
  t.vs_transient = z.vs_transient /\ t.vs_immutables = z.vs_immutables ==>
  ghost_inv_at_mods D lo d cenv cx mid Gf tf t
Proof
  strip_tac >>
  `!p sz. not_fresh_at cu p /\ ptr_covers G tn p z sz ==> ptr_covers Gf tf p t sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`z`,`tn`] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  simp[ghost_inv_at_mods_def,allocas_from_def] >> rpt conj_tac
  >- suspend "locals"
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      fs[return_buf_ptr_def] >> metis_tac[])
  >- fs[stor_taint_ok_at_def]
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> `not_fresh_at cu x` by metis_tac[local_ptrs_reserved_imm_base] >> metis_tac[])
  >> fs[allocas_from_def]
QED

Resume intcall_store_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at cu p` by metis_tac[local_ptrs_reserved_def] >>
  qpat_assum `!x. not_fresh_at cu x ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p z = SOME w` by fs[] >>
  `local_region cenv mid.scopes z name (w2n w) sz` by simp[local_region_def] >>
  qpat_assum `!n b k. local_region _ _ _ _ _ _ ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     qpat_assum `!n e p sz. _ ==> ?w. _` (drule_all_then strip_assume_tac) >> gvs[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> simp[]) >>
  irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`z.vs_memory`,`t.vs_memory`,`sz`] >>
  simp[Once ADD_COMM] >> metis_tac[ADD_COMM]
QED
Finalise intcall_store_ghost[local]

Theorem intcall_buffer_store_frame_mods:
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cu,mid,z,G,tn) pin /\
  typed_copy_state_frame cu dst nw z t /\ nw <= cap /\ lo <= dst /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [p]) (fn_insts func) /\
  FLOOKUP z.vs_allocas aid = SOME (dst,cap) /\ sa.cs_next_id <= aid /\ alloca_inv z /\
  (!n b k. local_region cenv mid.scopes z n b k ==> b+k <= dst \/ dst+cap <= b) /\
  local_ptrs_reserved cenv cu /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x. not_fresh_at cu x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!i. ~(dst <= i /\ i < dst+nw) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  cu.cs_next_id <= cs.cs_next_id /\ cu.cs_next_var <= cs.cs_next_var /\
  alloca_history func t /\ t.vs_current_bb = cs.cs_current_bb /\
  t.vs_inst_idx = LENGTH cs.cs_current_insts /\
  (case pin of NONE => T | SOME (rb,b,k) =>
    FLOOKUP Gf rb = SOME (b,k) /\ op_taint tf (Var rb) = {} /\
    lookup_var rb t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
    sa.cs_next_id < cs.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
    not_fresh_at cs rb /\
    (!n lb sz. local_region cenv mid.scopes t n lb sz ==> b+k <= lb \/ lb+sz <= b)) ==>
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cs,mid,t,Gf,tf) pin /\
  (!b n. b+n <= dst \/ dst+cap <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n z.vs_memory /\
    (!i. b <= i /\ i < b+n ==> (i IN tf.t_mem <=> i IN tn.t_mem)))
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `!b n. b+n <= dst \/ dst+cap <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n z.vs_memory /\
    (!i. b <= i /\ i < b+n ==> (i IN tf.t_mem <=> i IN tn.t_mem))` by
    (qpat_assum `typed_copy_frame dst nw _ _`
       (mp_then (Pat `typed_copy_frame _ _ _ _`) mp_tac intcall_store_window) >>
     disch_then (fn th => rpt gen_tac >> disch_tac >>
       mp_tac (Q.SPECL [`tn`,`tf`,`cap`,`b`,`n`] th)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `intcall_stage_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_frame_mods_def]) >>
  `copy_static t = copy_static z` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                         vs_current_bb := _; vs_inst_idx := _|> = z`
       (mp_tac o Q.AP_TERM `copy_static`) >> simp[copy_static_def]) >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   t.vs_accounts = z.vs_accounts /\ t.vs_call_ctx = z.vs_call_ctx /\
   t.vs_transient = z.vs_transient /\ t.vs_immutables = z.vs_immutables /\
   t.vs_halted = z.vs_halted` by
    (qpat_assum `copy_static t = copy_static z` mp_tac >>
     simp[NoAsms,copy_static_def,venom_state_component_equality] >> strip_tac >> simp[]) >>
  `!n b k. local_region cenv mid.scopes t n b k <=> local_region cenv mid.scopes z n b k` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >> first_assum irule >> metis_tac[local_ptrs_reserved_def]) >>
  `wb_frame cenv es0 mid sa s0 t /\ ghost_kept_at lo cenv es0 sa G0 tn0 s0 Gf tf` by
    suspend "origin" >>
  `sa.cs_next_id <= cs.cs_next_id /\ sa.cs_next_var <= cs.cs_next_var` by decide_tac >>
  simp[intcall_stage_frame_mods_def] >> conj_tac
  >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`z`,`cu`] >> simp[]) >>
  suspend "horizon"
QED

Resume intcall_buffer_store_frame_mods[origin]:
  irule intcall_store_origin >> qexistsl_tac [`G`,`tn`,`z`] >> simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `local_region cenv mid.scopes z n b k` by fs[] >>
      qpat_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _ /\ _`
        (qspecl_then [`b`,`k`] mp_tac) >>
      qpat_assum `!n b k. local_region _ _ z n b k ==> _ \/ _`
        (drule_then assume_tac) >> simp[])
  >- (rpt strip_tac >> `not_fresh_at cu x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP s0.vs_allocas old = SOME (b,k)` >>
  `FLOOKUP z.vs_allocas old = SOME (b,k)` by fs[wb_frame_def] >>
  `old <> aid` by decide_tac >>
  qpat_x_assum `alloca_inv z`
    (strip_assume_tac o REWRITE_RULE [alloca_inv_def,allocas_non_overlapping_def]) >>
  qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ ==> _ \/ _`
    (qspecl_then [`old`,`aid`,`b`,`k`,`dst`,`cap`] mp_tac) >> simp[] >> disch_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _ /\ _`
    (qspecl_then [`b`,`k`] mp_tac) >> simp[ADD_COMM]
QED

Resume intcall_buffer_store_frame_mods[horizon]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `typed_copy_state_frame cu dst cap z t` by
    (irule typed_copy_state_frame_subinterval >> qexistsl_tac [`dst`,`nw`] >> simp[]) >>
  `LENGTH z.vs_memory <= LENGTH t.vs_memory` by fs[typed_copy_frame_def] >>
  simp[] >> conj_tac >- suspend "state" >>
  conj_tac
  >- (irule ifexp_typed_immutable_frame_mods >>
      qexistsl_tac [`dst`,`mk_inst aid ALLOCA [Lit (n2w cap)] [p]`,`cu`,`cap`,`z`] >>
      simp[mk_inst_def]) >>
  suspend "ghost"
QED

Resume intcall_buffer_store_frame_mods[state]:
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`aid`,`dst`,`cap`,`p`,`cu`,`cu`,`z`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!n b k. local_region _ _ z n b k ==> _ \/ _` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _ /\ _`
    (qspecl_then [`a`,`len`] mp_tac) >> simp[]
QED

Resume intcall_buffer_store_frame_mods[ghost]:
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  irule intcall_store_ghost >> qexistsl_tac [`G`,`cu`,`func`,`tn`,`z`] >> simp[] >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo z.vs_memory /\
   (!i. i < lo ==> (i IN tf.t_mem <=> i IN tn.t_mem))` by
    (qpat_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _ /\ _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _ /\ _`
    (qspecl_then [`b`,`k`] mp_tac) >>
  qpat_assum `!n b k. local_region _ _ z n b k ==> _ \/ _`
    (drule_then assume_tac) >> simp[]
QED
Finalise intcall_buffer_store_frame_mods
