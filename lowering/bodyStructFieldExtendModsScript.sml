(* Extend an initialized prefix at the actual, already executed store. *)
Theory bodyStructFieldExtendMods
Ancestors
  bodyStructFieldCutsMods bodyFullStructLitFrames bodyPtrMakeArrayMemoryFrame
  bodyIfExpTypedGhostMods bodyIfExpTypedImmFrameMods
  exprSimCopy exprSimProps exprLoweringProps exprSimFullBundleProps
  typedMemoryCopy stateRelProj assignTuplePtrCopyLen freshWrites
  bodyPtrDefs loweringPosts loweringStateRelDefs venomState venomInst list pair

Triviality field_store_anchor_frame:
  wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
  fr.cs_next_var <= sa.cs_next_var /\ t.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!b k. b+k <= B \/ B+N <= b ==>
     mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
  (!i. ~(B <= i /\ i < B+N) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!name b k. local_region ce ees.scopes sf name b k ==> b+k <= B \/ B+N <= b) /\
  (!aid b k. FLOOKUP sf.vs_allocas aid = SOME (b,k) /\ aid < fr.cs_next_id ==>
     b+k <= B \/ B+N <= b) ==>
  wb_frame ce ees ee fr sf t /\ ghost_kept_at lo ce ees fr Gf tnf sf G' tn'
Proof
  strip_tac >>
  `!x. not_fresh_at fr x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >> simp[]) >>
  conj_tac >- suspend "writeback" >> suspend "ghost"
QED

Resume field_store_anchor_frame[writeback]:
  qpat_x_assum `wb_frame _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >> rename1 `FLOOKUP sf.vs_allocas aid = SOME (b,k)` >>
      `mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by metis_tac[] >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >> simp[] >> metis_tac[]
QED

Resume field_store_anchor_frame[ghost]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[ghost_kept_at_def] >> conj_tac
  >- (rpt strip_tac >> rename1 `FLOOKUP sf.vs_allocas aid = SOME (b,k)` >>
      `b+k <= B \/ B+N <= b` by metis_tac[] >>
      `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> rename1 `local_region ce ees.scopes sf name b k` >>
  `b+k <= B \/ B+N <= b` by metis_tac[] >>
  `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]
QED

Finalise field_store_anchor_frame

Theorem struct_field_store_extends_prefix_mods:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (H,D,ee,sa,G,tn,s) cells off /\
  struct_store_effects func (sa,G,tn,s) (sb,G',tn',t) (addr+off,tv,v) /\
  off+type_memory_size tv <= capacity /\ ci_mono sa sb /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (H,D,ee,sb,G',tn',t)
    (cells ++ [(tv,v,addr+off,type_memory_size tv)]) (off+type_memory_size tv)
Proof
  simp_tac bool_ss [struct_prefix_mods_def, struct_store_effects_def] >> strip_tac >>
  qabbrev_tac `n = type_memory_size tv` >>
  `typed_copy_state_frame sa addr capacity s t` by
    (irule typed_copy_state_frame_subinterval >> goal_assum (drule_at Any) >> decide_tac) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame sa addr capacity s t`
       (strip_assume_tac o SRULE [typed_copy_state_frame_def, venom_state_component_equality]) >>
     simp[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s` by
    (qpat_assum `typed_copy_state_frame sa addr capacity s t`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `!p k. p+k <= addr+off \/ addr+off+n <= p ==>
     mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory` by
    (qpat_assum `typed_copy_state_frame sa (addr+off) n s t`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def, typed_copy_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `!name p k. local_region ce ee.scopes t name p k <=>
               local_region ce ee.scopes s name p k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> metis_tac[]) >>
  `stmt_state_rel H ctx func ce cx ee t /\ literal_prefix_ok cells tn' t` by
    suspend "state" >>
  `immutable_frame_mods func ce cx ee t` by suspend "immutable" >>
  `ghost_inv_at_mods D lo d ce cx ee G' tn' t` by suspend "linked_ghost" >>
  `wb_frame ce ees ee fr sf t /\ ghost_kept_at lo ce ees fr Gf tnf sf G' tn'` by
    suspend "anchor" >>
  `(pure ==> pure_frame ce func ees fr sf t)` by suspend "pure" >>
  `ptr_covers G' tn' root t capacity` by
    (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "finish"
QED

Resume struct_field_store_extends_prefix_mods[state]:
  irule structlit_store_state_prefix_frame >>
  qexistsl_tac [`addr`,`aid`,`capacity`,`n`,`off`,`root`,`s`,`sa`,`tn`] >>
  fs[regions_disjoint_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name p k. local_region ce ee.scopes s name p k ==> _`
        drule >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `EVERY _ cells` mp_tac >>
  simp[EVERY_MEM, FORALL_PROD] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume struct_field_store_extends_prefix_mods[immutable]:
  irule ifexp_typed_immutable_frame_mods >>
  qexistsl_tac [`addr`,`mk_inst aid ALLOCA [Lit (n2w capacity)] [root]`,
                `sa`,`capacity`,`s`] >> simp[mk_inst_def]
QED

Resume struct_field_store_extends_prefix_mods[linked_ghost]:
  irule ifexp_typed_copy_ghost_mods >>
  qexistsl_tac [`G`,`addr+off`,`func`,`sa`,`n`,`s`,`tn`] >>
  `local_ptrs_rel func ce ee.scopes s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `lo <= addr+off` by decide_tac >> fs[] >>
  rpt strip_tac >> simp[regions_disjoint_def] >>
  qpat_assum `!name p k. local_region ce ee.scopes s name p k ==> _` drule >> decide_tac
QED

Resume struct_field_store_extends_prefix_mods[anchor]:
  irule field_store_anchor_frame >>
  qexistsl_tac [`addr+off`,`G`,`n`,`s`,`sa`,`tn`] >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `addr+capacity <= b \/ b+k <= addr` by metis_tac[] >> decide_tac)
  >- (rpt strip_tac >>
      `addr+capacity <= b \/ b+k <= addr` by metis_tac[] >> decide_tac) >>
  rpt strip_tac >> fs[]
QED

Resume struct_field_store_extends_prefix_mods[pure]:
  strip_tac >> irule pure_frame_buffer_tail >>
  qexistsl_tac [`addr`,`capacity`,`mk_inst aid ALLOCA [Lit (n2w capacity)] [root]`,`s`] >>
  simp[mk_inst_def] >> conj_tac
  >- (rewrite_tac[regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >>
  fs[regions_disjoint_def] >> decide_tac
QED

Resume struct_field_store_extends_prefix_mods[finish]:
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `not_fresh_at sb root` by metis_tac[not_fresh_at_mono] >>
  `expr_sim_full_endpoint func sb sf t` by
    fs[expr_sim_full_endpoint_def] >>
  `EVERY (\(r,w,p,k). addr <= p /\ p+k <= addr+off+n) cells` by
    (qpat_x_assum `EVERY _ cells` mp_tac >> simp[EVERY_MEM, FORALL_PROD] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `literal_prefix_ok [(tv,v,addr+off,n)] tn' t` by
    (simp[literal_prefix_cell, Abbr `n`] >> simp[val_footprint_le]) >>
  fs[literal_prefix_ok_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise struct_field_store_extends_prefix_mods
