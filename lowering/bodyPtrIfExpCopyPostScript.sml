Theory bodyPtrIfExpCopyPost
Ancestors exprSimCopy loweringPosts exprLoweringProps freshWrites
  exprSimStorageCopy immutableCopyExecution localPtrsProps
  compileEnv venomState venomInst finite_map words arithmetic

(* Only the frame clauses of vv_post are transported here. The raw result
   remains arbitrary: reading a place does not make it a Value constructor. *)
Theorem ifexp_copy_buffer_post_transport:
  !ctx func cenv cx e es sa sm mid sb s0 es' raw v vv s u z tv op w sz inst.
    post_value_type cenv e = expr_type e /\
    vv_post ctx func cenv cx e es sa sm s0 es' raw vv s /\
    read_result cx raw es' = (INL v,es') /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
    stmt_state_rel ctx func cenv cx es' u /\
    u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es'.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + sz <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= sz /\ eval_operand op z = SOME w ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[not_fresh_at_mono]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `!name b len. local_region cenv es'.scopes s name b len ==>
     w2n w + sz <= b \/ b + len <= w2n w` by
    (rpt strip_tac >>
     `local_region cenv es'.scopes u name b len` by
       metis_tac[copy_buffer_local_region_frame] >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
     w2n w + sz <= b \/ b + len <= w2n w` by
    (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) copy_buffer_original_local_separation >>
     disch_then (qspecl_then [`w2n w`, `sz`] mp_tac) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `local_ptrs_reserved cenv mid` by
    metis_tac[local_ptrs_reserved_next_var, LESS_EQ_TRANS] >>
  `stmt_state_rel ctx func cenv cx es' z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`, `inst`, `u`, `mid`, `sz`] >>
     simp[] >> gvs[regions_disjoint_def] >> metis_tac[]) >>
  `locals_kept cenv es s0 z` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl_tac [`w2n w`, `u`, `sz`] >>
     gvs[vv_post_def, locals_kept_def, regions_disjoint_def] >> metis_tac[]) >>
  suspend "post"
QED

Resume ifexp_copy_buffer_post_transport[post]:
  drule copy_static_fields >> strip_tac >>
  irule copy_buffer_expr_post >>
  simp[] >> conj_tac
  >- (gvs[vv_post_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[vv_post_def] >> rpt strip_tac >>
      `id < sm.cs_next_id` by decide_tac >>
      `FLOOKUP s.vs_allocas id = SOME (off,len)` by metis_tac[] >>
      `regions_disjoint (w2n w) sz off len` by metis_tac[] >>
      `mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory` by
        (qpat_x_assum `!aid off sz. _` irule >>
         conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!name b k. _` drule >> decide_tac) >>
         qexists_tac `id` >> simp[]) >>
      `mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
        (qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >>
         gvs[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  conj_tac >- (gvs[vv_post_def] >> metis_tac[]) >>
  qexistsl_tac [`sm.cs_next_id`, `sz`] >> simp[] >>
  rpt strip_tac >>
  `local_region cenv es'.scopes u name b len` by
    metis_tac[copy_buffer_local_region_frame] >>
  gvs[regions_disjoint_def] >> metis_tac[]
QED

Finalise ifexp_copy_buffer_post_transport
