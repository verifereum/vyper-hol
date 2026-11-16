(* Private exterior frame and fresh loop-binding installation. *)
Theory bodyFullForArrayLocalInstall
Ancestors
  bodyFullMemoryFrames forPtrScope bodyPtrDefs exprLoweringProps
  loweringStateRelDefs exprSimProps abiDecodeStaticProps ptrDiscipline
  vyperState vyperLookup loweringPosts finite_map words pred_set

Theorem for_array_local_copy_outer_ghost:
  !D lo d cenv cx es G tn s H ctx func sa dst sz Gf tf t.
  ghost_inv_at D lo d cenv cx es G tn s /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!nm b len. local_region cenv es.scopes s nm b len ==>
    regions_disjoint (w2n dst) sz b len) /\
  lo <= w2n dst /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n dst <= i /\ i < w2n dst + sz) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  ghost_inv_at D lo d cenv cx es Gf tf t
Proof
  rpt gen_tac >> strip_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ghost_inv_at_def,allocas_from_def] >> metis_tac[]) >>
  irule body_full_memory_ghost_frame >> simp[] >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`, `{i | w2n dst <= i /\ i < w2n dst + sz}`] >>
  simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `local_ptrs_rel func cenv es.scopes s` by
        fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >>
      fs[local_ptrs_rel_def] >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >> gvs[] >>
      drule val_footprint_le >> strip_tac >>
      `local_region cenv es.scopes s name (w2n w) sz'` by
        (simp[local_region_def] >> metis_tac[]) >>
      qpat_x_assum `!nm b len. _` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `~(w2n dst <= i /\ i < w2n dst + sz)` by decide_tac >>
      metis_tac[]) >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  `~(w2n dst <= i /\ i < w2n dst + sz)` by decide_tac >>
  metis_tac[]
QED

Theorem for_array_local_install_ghost:
  !D lo d cenv cx es Gf tf t id bc p sz dst tv v.
  ghost_inv_at D lo d cenv cx es Gf tf t /\
  lookup_scopes id es.scopes = NONE /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  bc.ce_return_buf = cenv.ce_return_buf /\
  bc.ce_return_pc = cenv.ce_return_pc /\
  bc.ce_imm_alloca = cenv.ce_imm_alloca /\
  ptr_covers Gf tf p t sz /\ lookup_var p t = SOME dst /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n dst) mem) ==>
  ghost_inv_at D lo d bc cx
    (es with <|scopes := (FEMPTY |+ (id,
       <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes;
       gas_obs := []|>) Gf tf t
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `name = id`
      >- (gvs[lookup_scopes_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
      `lookup_scopes name es.scopes = SOME entry` by
        gvs[lookup_scopes_def,FLOOKUP_UPDATE] >>
      drule_all cenv_top_ext_outer_lookup >> strip_tac >>
      fs[ghost_inv_at_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def] >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME rb) _ _ _ _` >> PairCases_on `rb` >>
  gvs[return_buf_ptr_def]
QED
