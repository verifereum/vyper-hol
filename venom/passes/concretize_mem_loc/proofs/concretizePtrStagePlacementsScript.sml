Theory concretizePtrStagePlacements
Ancestors concretizePtrSourceOwnership concretizePtrExecutedCoverage
  concretizePtrImportCoverage concretizePtrImportOrigins
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrChronologicalHistory concretizePtrOwnerPath ptrDiscipline
  o1ScheduleDecompHelpers o1PassContract venomWf venomInst
  finite_map list pred_set pair arithmetic

Definition ptr_stage_placements_def:
  ptr_stage_placements C' positions <=>
    !key p sz. FLOOKUP positions key = SOME (p,sz) <=>
      ?g. MEM g C'.ctx_functions /\ MEM (key,p,sz) g.fn_mems_used
End

Theorem ptr_functional_list_map[local]:
  !xs:('a # 'b) list.
  (!k x y. MEM (k,x) xs /\ MEM (k,y) xs ==> x = y) ==>
  ?m. !k v. FLOOKUP m k = SOME v <=> MEM (k,v) xs
Proof
  Induct >- (strip_tac >> qexists_tac `FEMPTY` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> strip_tac >>
  `?m. !k v. FLOOKUP m k = SOME v <=> MEM (k,v) xs` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  qexists_tac `m |+ (h0,h1)` >> simp[FLOOKUP_UPDATE] >>
  rpt gen_tac >> Cases_on `h0 = k` >> gvs[] >> metis_tac[MEM]
QED

Theorem ptr_stage_placements_exists:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions ==>
  ?positions. ptr_stage_placements C' positions
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C'.ctx_functions)` by
    (drule ptr_stage_names >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
     metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `ptr_stage_placements Ct` >>
  `!k x y.
    MEM (k,x) (FLAT (MAP (\f. f.fn_mems_used) Ct.ctx_functions)) /\
    MEM (k,y) (FLAT (MAP (\f. f.fn_mems_used) Ct.ctx_functions)) ==> x = y` by
    (simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
     PairCases_on `x` >> PairCases_on `y` >>
     gvs[Abbr `Ct`] >>
     `lookup_function f.fn_name C'.ctx_functions = SOME f` by
       metis_tac[lookup_function_member_iff] >>
     `lookup_function f'.fn_name C'.ctx_functions = SOME f'` by
       metis_tac[lookup_function_member_iff] >>
     irule ptr_stage_mems_coherent >>
     qpat_assum `MEM (k,x0,x1) _` (irule_at Any) >>
     qpat_assum `MEM (k,y0,y1) _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule ptr_functional_list_map >> strip_tac >> qexists_tac `m` >>
  simp[ptr_stage_placements_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem ptr_stage_placements_live_owner:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP a.po_prov v = SOME (b,sz) ==>
  ?d owner output p.
    d <= LENGTH a.po_stack /\
    EL (LENGTH a.po_stack-d) tokens = token /\
    FLOOKUP registry token = SOME owner /\
    owner = (ptr_owner_view d a).cf_fn /\
    FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
    lookup_function owner.fn_name C'.ctx_functions = SOME output /\
    MEM (Allocation aid,p,sz) output.fn_mems_used /\
    FLOOKUP positions (Allocation aid) = SOME (p,sz)
Proof
  strip_tac >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_live_cache >> strip_tac >>
  `ptr_ledger_source_activations vs C h a tokens registry` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations] >>
  `FLOOKUP registry token = SOME (ptr_owner_view d a).cf_fn` by
    metis_tac[ptr_source_activations_owner_lookup] >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    metis_tac[ptr_source_activations_sound, ptr_chrono_history_reachable,
      ptr_observation_reachable_def] >>
  `?output p.
    lookup_function (ptr_owner_view d a).cf_fn.fn_name C'.ctx_functions = SOME output /\
    MEM (Allocation aid,p,sz) output.fn_mems_used` by
    (Cases_on `d = LENGTH a.po_stack`
     >- (gvs[ptr_owner_view_def] >> drule_all ptr_frame_current_mems >> simp[]) >>
     `MEM (ptr_owner_view d a) a.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >> decide_tac) >>
     drule_all ptr_frame_saved_mems >> simp[]) >>
  qexistsl [`d`,`(ptr_owner_view d a).cf_fn`,`output`,`p`] >> simp[] >>
  gvs[ptr_stage_placements_def] >>
  metis_tac[lookup_function_MEM]
QED
