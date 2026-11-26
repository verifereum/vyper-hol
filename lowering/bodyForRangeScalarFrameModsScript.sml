(* Exterior frames for linked scalar loop edges that do not write memory. *)
Theory bodyForRangeScalarFrameMods
Ancestors
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit bodyPtrDefs
  exprLoweringProps loweringStateRelDefs compileEnv ptrDiscipline venomState

Theorem ghost_inv_at_mods_exterior_frame:
  !D lo d cenv cx es es' G G' tn tn' s s' sa.
    ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x s' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    es'.scopes = es.scopes /\ s'.vs_memory = s.vs_memory /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_immutables = s.vs_immutables ==>
    ghost_inv_at_mods D lo d cenv cx es' G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers G' tn' p s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem immutable_frame_mods_exterior_frame:
  immutable_frame_mods func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x s' = lookup_var x s) /\
  es'.immutables = es.immutables /\ es'.scopes = es.scopes /\
  s'.vs_memory = s.vs_memory /\ s'.vs_data_section = s.vs_data_section /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next ==>
  immutable_frame_mods func cenv cx es' s'
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >>
      first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  `local_region (cenv with ce_module := src) es.scopes s' id b sz <=>
   local_region (cenv with ce_module := src) es.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >>
     metis_tac[local_ptrs_reserved_def]) >>
  gs[]
QED
