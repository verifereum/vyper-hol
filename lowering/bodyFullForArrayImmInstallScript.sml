(* Scope installation at the selected immutable word-copy endpoint. *)
Theory bodyFullForArrayImmInstall
Ancestors
  bodyFullUnwrapSlotPost bodySim forPtrScope exprSimProps
  loweringPosts bodyPtrDefs compileEnv venomState venomMemProofs vyperState
  finite_map list arithmetic pred_set words valueEncodingProofs

Theorem for_array_immutable_install_ghost_full:
  ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func cenv ee.scopes s /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n dst+32 <= b \/ b+len <= w2n dst) /\
  (!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!a k. a+k <= w2n dst \/ w2n dst+32 <= a ==>
    mem_bytes_at a k sf.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < w2n dst \/ w2n dst+32 <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  lo <= w2n dst /\ stor_taint_ok_at D tf sf /\
  allocas_from lo sf /\ lo <= sf.vs_alloca_next /\
  cenv_top_ext cenv bc (FEMPTY::ee.scopes) /\ same_frame cenv bc /\
  lookup_scopes id ee.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p sf = SOME dst /\ ptr_covers Gf tf p sf sz /\
  val_wf tv v /\ val_in_memory tv v (w2n dst) sf.vs_memory /\
  val_footprint tv v <= 32 /\
  (!i. w2n dst <= i /\ i < w2n dst+32 ==> i NOTIN tf.t_mem) ==>
  ghost_inv_at D lo d bc cx
    (ee with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tv;
      value := v; popped := []|>))::ee.scopes; gas_obs := []|>) Gf tf sf
Proof
  strip_tac >>
  `ghost_inv_at D lo d cenv cx ee Gf tf sf` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     simp[] >> qexistsl_tac [`G`,`func`,`32`,`s`,`sa`,`w2n dst`,`tn`] >> simp[ADD_COMM] >> metis_tac[]) >>
  `!mem. mem_agree_outside tf.t_mem sf.vs_memory mem ==>
    val_in_memory tv v (w2n dst) mem` by
    (rpt strip_tac >> irule val_in_memory_footprint_agree >>
     conj_tac >- simp[] >> qexists_tac `sf.vs_memory` >> simp[] >>
     irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     rename1 `i < val_footprint tv v` >>
     `w2n dst+i NOTIN tf.t_mem` by (first_x_assum irule >> decide_tac) >>
     `mem_bytes_at (w2n dst+i) 1 sf.vs_memory =
      mem_bytes_at (w2n dst+i) 1 mem` by metis_tac[mem_agree_outside_def] >>
     pop_assum mp_tac >> simp[LIST_EQ_REWRITE,EL_mem_bytes_at]) >>
  qpat_x_assum `ghost_inv_at D lo d cenv cx ee Gf tf sf` mp_tac >>
  simp[ghost_inv_at_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `name = id`
      >- (gvs[lookup_scopes_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
      gvs[lookup_scopes_def,FLOOKUP_UPDATE] >>
      `FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
        (irule cenv_top_ext_outer_lookup >> metis_tac[]) >> metis_tac[]) >>
  `bc.ce_return_buf = cenv.ce_return_buf /\ bc.ce_return_pc = cenv.ce_return_pc /\
   bc.ce_imm_alloca = cenv.ce_imm_alloca` by
    (qpat_x_assum `same_frame _ _` mp_tac >> simp[same_frame_def] >>
     strip_tac >> pop_assum kall_tac >>
     pop_assum (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  simp[] >> Cases_on `d` >- gvs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair) bc _ _ _` >>
  PairCases_on `pair` >> gvs[return_buf_ptr_def]
QED
