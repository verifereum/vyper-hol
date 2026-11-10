(* Natural allocation intervals and ordered saved-frame cuts.
   No machine-word representability is required by this geometry. *)
Theory occurrenceGeometry
Ancestors
  o1LowerDloadOccurrence venomExecSemantics finite_map list pred_set arithmetic
  ptrSafeRun opcodeClass venomMemProofs

Definition occurrence_natural_geometry_def:
  occurrence_natural_geometry lo a U B stk s <=>
    (!id b z. FLOOKUP B id = SOME (b,z) ==>
       lo <= b /\ b + z <= s.vs_alloca_next) /\
    (!id jd b z c w.
       FLOOKUP B id = SOME (b,z) /\ FLOOKUP B jd = SOME (c,w) /\
       id <> jd /\ 0 < z /\ 0 < w ==> b + z <= c \/ c + w <= b) /\
    LENGTH U = LENGTH stk /\
    (!j. j < LENGTH stk ==>
       (EL j stk).cf_state.vs_alloca_next <= s.vs_alloca_next /\
       (!id b z. FLOOKUP B id = SOME (b,z) /\
          MEM (FST id) (MAP (\u. u.of_owner) (DROP j U)) ==>
          b + z <= (EL j stk).cf_state.vs_alloca_next) /\
       (!id b z. FLOOKUP B id = SOME (b,z) /\
          (FST id = a \/ MEM (FST id) (MAP (\u. u.of_owner) (TAKE j U))) ==>
          (EL j stk).cf_state.vs_alloca_next <= b)) /\
    (!i j. i < j /\ j < LENGTH stk ==>
       (EL j stk).cf_state.vs_alloca_next <= (EL i stk).cf_state.vs_alloca_next)
End

Theorem occurrence_natural_geometry_empty:
  occurrence_natural_geometry lo a [] FEMPTY [] s
Proof
  simp[occurrence_natural_geometry_def]
QED

Theorem occurrence_natural_geometry_same_frontier:
  occurrence_natural_geometry lo a U B stk s /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  occurrence_natural_geometry lo a U B stk t
Proof
  strip_tac >> gvs[occurrence_natural_geometry_def] >> metis_tac[]
QED

Theorem occurrence_natural_geometry_grow_frontier:
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  occurrence_natural_geometry lo a U B stk t
Proof
  rw[occurrence_natural_geometry_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem occurrence_natural_geometry_extend:
  occurrence_natural_geometry lo a U B stk s /\
  ~MEM a (MAP (\u. u.of_owner) U) /\
  (a,aid) NOTIN FDOM B /\ lo <= s.vs_alloca_next /\
  t.vs_alloca_next = s.vs_alloca_next + z ==>
  occurrence_natural_geometry lo a U
    (B |+ ((a,aid),(s.vs_alloca_next,z))) stk t
Proof
  strip_tac >> fs[occurrence_natural_geometry_def] >>
  simp[occurrence_natural_geometry_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `id = (a,aid)` >> gvs[FLOOKUP_UPDATE] >>
      qpat_x_assum `!id b z. FLOOKUP B id = SOME (b,z) ==> _` drule >>
      strip_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `id = (a,aid)`
      >- (gvs[FLOOKUP_UPDATE] >>
          qpat_x_assum `!id b z. FLOOKUP B id = SOME (b,z) ==> _` drule >> simp[]) >>
      Cases_on `jd = (a,aid)`
      >- (gvs[FLOOKUP_UPDATE] >>
          qpat_x_assum `!id b z. FLOOKUP B id = SOME (b,z) ==> _` drule >> simp[]) >>
      gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` drule >> strip_tac >>
  conj_tac >- simp[] >>
  `~MEM a (MAP (\u. u.of_owner) (DROP j U))` by
    (simp[MAP_DROP] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `id = (a,aid)` >> gvs[FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  rpt strip_tac >> Cases_on `id = (a,aid)` >> gvs[FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem occurrence_natural_geometry_push:
  occurrence_natural_geometry lo a U B stk s /\
  (!id. id IN FDOM B ==> MEM (FST id) (a::MAP (\u. u.of_owner) U)) /\
  ~MEM c (a::MAP (\u. u.of_owner) U) /\
  u.of_owner = a /\ f.cf_state.vs_alloca_next = s.vs_alloca_next /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  occurrence_natural_geometry lo c (u::U) B (f::stk) t
Proof
  strip_tac >>
  `!id b z. FLOOKUP B id = SOME (b,z) ==> FST id <> c` by
    (rpt strip_tac >> `id IN FDOM B` by fs[FLOOKUP_DEF] >> metis_tac[]) >>
  fs[occurrence_natural_geometry_def] >>
  simp[occurrence_natural_geometry_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (Cases >> simp[]
      >- (rpt strip_tac >> metis_tac[FLOOKUP_DEF]) >>
      rpt strip_tac >>
      qpat_x_assum `!j. j < LENGTH stk ==> _` drule >>
      strip_tac >> simp[] >> rpt strip_tac >>
      metis_tac[FLOOKUP_DEF]) >>
  Cases >> Cases >> simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem occurrence_natural_geometry_pop:
  occurrence_natural_geometry lo a (u::U) B (f::stk) s /\
  (!id. id IN FDOM B ==> MEM (FST id) (a::MAP (\u. u.of_owner) (u::U))) /\
  t.vs_alloca_next = f.cf_state.vs_alloca_next ==>
  occurrence_natural_geometry lo u.of_owner U
    (DRESTRICT B {id | FST id <> a}) stk t
Proof
  strip_tac >> fs[occurrence_natural_geometry_def] >>
  `!id b z. FLOOKUP (DRESTRICT B {id | FST id <> a}) id = SOME (b,z) ==>
     FLOOKUP B id = SOME (b,z) /\
     MEM (FST id) (MAP (\u. u.of_owner) (u::U))` by
    (simp[FLOOKUP_DRESTRICT] >> rpt strip_tac >>
     `id IN FDOM B` by fs[FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_assum `!j. j < SUC (LENGTH stk) ==> _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  simp[occurrence_natural_geometry_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!id b z. FLOOKUP (DRESTRICT _ _) id = _ ==> _` drule >>
      simp[] >> strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> metis_tac[]) >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!j. j < SUC (LENGTH stk) ==> _`
        (qspec_then `SUC j` mp_tac) >> simp[] >> strip_tac >>
      conj_tac >- (qpat_x_assum `!i j. _` (qspecl_then [`0`,`SUC j`] mp_tac) >> simp[]) >>
      conj_tac >- (rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
      rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i j. _` (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[]
QED

(* Definition probes: zero-size sites and natural bases beyond word256. *)
Theorem occurrence_natural_geometry_zero_wrap_probe[local]:
  occurrence_natural_geometry 0 0 []
    (FEMPTY |+ ((0,0),(2 ** 256,0))) []
    (s with vs_alloca_next := 2 ** 256) /\
  occurrence_natural_geometry 0 0 []
    (FEMPTY |+ ((0,0),(2 ** 256,1))) []
    (s with vs_alloca_next := 2 ** 256 + 1)
Proof
  simp[occurrence_natural_geometry_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem occurrence_geometry_entry:
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s ==>
  occurrence_natural_geometry lo 0 [] FEMPTY [] s
Proof
  simp[occurrence_natural_geometry_empty]
QED

Theorem occurrence_geometry_block:
  occurrence_natural_geometry lo a U B stk s /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK s' /\
  enters_block fn s' s1 ==>
  occurrence_natural_geometry lo a U B stk s1
Proof
  strip_tac >> irule occurrence_natural_geometry_same_frontier >>
  qexists_tac `s` >> simp[] >>
  drule o1LowerDloadStackFrontierTheory.ld_enters_block_frontier >>
  strip_tac >> simp[] >>
  irule mem2varBlockSimHelpersTheory.step_inst_result_preserves_alloca_next >>
  metis_tac[venomInstTheory.is_terminator_def]
QED

Theorem occurrence_geometry_alloca:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_allocas_ok B a s /\ ~MEM a (MAP (\u. u.of_owner) U) /\
  lo <= s.vs_alloca_next /\ inst.inst_opcode = ALLOCA /\
  exec_alloca inst s amount = OK s' ==>
  occurrence_natural_geometry lo a U (occurrence_sites_step a B inst s') stk s'
Proof
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (gvs[exec_alloca_def, AllCaseEqs(), venomStateTheory.update_var_def] >>
      simp[occurrence_sites_step_def, FLOOKUP_UPDATE] >>
      irule occurrence_natural_geometry_extend >> simp[] >>
      fs[occurrence_allocas_ok_def] >>
      qpat_x_assum `!aid. _` (qspec_then `inst.inst_id` mp_tac) >>
      simp[FLOOKUP_DEF] >> metis_tac[]) >>
  PairCases_on `x` >>
  gvs[exec_alloca_def, AllCaseEqs(), venomStateTheory.update_var_def] >>
  `FLOOKUP B (a,inst.inst_id) = SOME (x0,x1)` by fs[occurrence_allocas_ok_def] >>
  simp[occurrence_sites_step_def] >>
  `B |+ ((a,inst.inst_id),(x0,x1)) = B` by
    (simp[fmap_eq_flookup, FLOOKUP_UPDATE] >>
     gen_tac >> IF_CASES_TAC >> gvs[]) >>
  simp[] >> irule occurrence_natural_geometry_same_frontier >>
  qexists_tac `s` >> simp[]
QED

Theorem occurrence_geometry_next:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  lo <= s.vs_alloca_next /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK s' ==>
  occurrence_natural_geometry lo a U (occurrence_sites_step a B inst s') stk
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule occurrence_natural_geometry_same_frontier >>
  qexists_tac `s'` >> simp[] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule (INST_TYPE [alpha |-> ``:256``] occurrence_geometry_alloca) >>
      fs[occurrence_annotation_ok_def] >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[venomExecSemanticsTheory.step_inst_non_invoke,
           venomExecSemanticsTheory.step_inst_base_opcode_eqs,
           AllCaseEqs()] >> strip_tac >>
      qexistsl_tac [`alloc_size`, `s`] >> simp[]) >>
  simp[occurrence_sites_step_def] >>
  irule occurrence_natural_geometry_same_frontier >>
  qexists_tac `s` >> simp[] >>
  irule mem2varBlockSimHelpersTheory.step_inst_result_preserves_alloca_next >>
  metis_tac[]
QED

Theorem occurrence_geometry_call:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  setup_callee callee args s = SOME cs /\ enters_block callee cs s1 ==>
  occurrence_natural_geometry lo n
    (<|of_owner := a; of_prov := H; of_params := HP |> :: U) B
    (<|cf_fn := caller; cf_inst := call_inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk) s1
Proof
  strip_tac >> irule occurrence_natural_geometry_push >>
  qexistsl_tac [`a`, `s`] >> simp[] >>
  drule o1LowerDloadStackFrontierTheory.ld_setup_callee_frontier >>
  drule o1LowerDloadStackFrontierTheory.ld_enters_block_frontier >>
  rpt strip_tac >> simp[] >>
  fs[occurrence_annotation_ok_def] >>
  fs[EVERY_MEM] >> metis_tac[LESS_ANTISYM]
QED

Theorem occurrence_geometry_return:
  occurrence_natural_geometry lo a (u::U) B (f::stk) s /\
  occurrence_annotation_ok n a (u::U) B HP H (f::stk) PG G s /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' ==>
  occurrence_natural_geometry lo u.of_owner U
    (DRESTRICT B {id | FST id <> a}) stk
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> irule occurrence_natural_geometry_pop >>
  conj_tac >- fs[occurrence_annotation_ok_def] >>
  qexistsl_tac [`f`, `s`] >> simp[] >>
  drule o1LowerDloadStackFrontierTheory.ld_return_frontier >>
  strip_tac >> simp[] >> fs[occurrence_annotation_ok_def]
QED

Theorem occ_frame_reachable_geometry:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
    lo <= vs.vs_alloca_next ==>
    occurrence_natural_geometry lo a U B stk s
Proof
  ho_match_mp_tac occ_frame_reachable_strongind >> rpt conj_tac
  >- (rpt strip_tac >> simp[occurrence_natural_geometry_empty])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume occ_frame_reachable_geometry[next]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `lo <= s.vs_alloca_next` by
    (drule occ_frame_reachable_projection >> strip_tac >>
     drule o1LowerDloadStackFrontierTheory.ld_frame_reachable_current_initial_frontier >>
     decide_tac) >>
  gvs[] >> drule_all occurrence_geometry_next >> simp[]
QED

Resume occ_frame_reachable_geometry[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule occurrence_geometry_block >> metis_tac[]
QED

Resume occ_frame_reachable_geometry[call]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  drule occ_frame_reachable_annotation >> simp[] >> strip_tac >>
  gvs[] >> drule_all occurrence_geometry_call >> simp[]
QED

Resume occ_frame_reachable_geometry[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  `occurrence_annotation_ok n a (u::U) B HP H (f::stk) PG G s` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  gvs[] >> drule_all occurrence_geometry_return >> simp[]
QED

Finalise occ_frame_reachable_geometry

Theorem frame_reachable_occurrence_geometry:
  vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\
  ~ctx_has_dalloca C /\ frame_reachable vs C stk PG G tn fn inst s ==>
  ?n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
    occurrence_annotation_ok n a U B HP H stk PG G s /\
    occurrence_natural_geometry lo a U B stk s
Proof
  strip_tac >> drule_all frame_reachable_occurrence_annotation >> strip_tac >>
  drule occ_frame_reachable_geometry >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem occurrence_geometry_site_bounds:
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (b,z) ==>
  lo <= b /\ b + z <= s.vs_alloca_next
Proof
  simp[occurrence_natural_geometry_def] >> metis_tac[]
QED

Theorem occurrence_geometry_sites_disjoint:
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (b,z) /\ FLOOKUP B jd = SOME (c,w) /\
  id <> jd /\ 0 < z /\ 0 < w ==> b + z <= c \/ c + w <= b
Proof
  simp[occurrence_natural_geometry_def] >> metis_tac[]
QED

Theorem occurrence_geometry_positive_site_unique:
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (b,z) /\ FLOOKUP B jd = SOME (b,w) /\
  0 < z /\ 0 < w ==> id = jd
Proof
  strip_tac >> Cases_on `id = jd` >> simp[] >>
  drule_all occurrence_geometry_sites_disjoint >> decide_tac
QED

Theorem occurrence_geometry_saved_site_bound:
  occurrence_natural_geometry lo a U B stk s /\
  j < LENGTH stk /\ FLOOKUP B id = SOME (b,z) /\
  MEM (FST id) (MAP (\u. u.of_owner) (DROP j U)) ==>
  b + z <= (EL j stk).cf_state.vs_alloca_next
Proof
  simp[occurrence_natural_geometry_def] >> metis_tac[]
QED

Theorem occurrence_env_var_site_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\ FLOOKUP H v <> SOME id /\
  FLOOKUP B id = SOME (b,z) /\ FLOOKUP G v = SOME (c,w) /\
  0 < z /\ 0 < w ==> b + z <= c \/ c + w <= b
Proof
  strip_tac >>
  `v IN FDOM H` by
    (fs[occurrence_env_ok_def] >> gvs[FLOOKUP_DEF]) >>
  `?jd. FLOOKUP H v = SOME jd` by metis_tac[FLOOKUP_DEF] >>
  `FLOOKUP B jd = SOME (c,w)` by
    (fs[occurrence_env_ok_def] >> metis_tac[]) >>
  irule occurrence_geometry_sites_disjoint >> metis_tac[]
QED

Theorem occurrence_env_site_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\
  (!v. FLOOKUP H v <> SOME id) /\
  FLOOKUP B id = SOME (b,z) /\ FLOOKUP G v = SOME (c,w) /\
  0 < z /\ 0 < w ==> b + z <= c \/ c + w <= b
Proof
  metis_tac[occurrence_env_var_site_exclusion]
QED

Theorem frame_reachable_saved_frontier:
  frame_reachable vs C (f::stk) PG G tn fn ri sr /\
  vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\ ~ctx_has_dalloca C ==>
  f.cf_state.vs_alloca_next <= sr.vs_alloca_next /\
  (!aid b z. FLOOKUP sr.vs_allocas aid = SOME (b,z) ==>
             f.cf_state.vs_alloca_next <= b)
Proof
  strip_tac >> drule_all frame_reachable_occurrence_geometry >> strip_tac >>
  `occurrence_allocas_ok B a sr` by gvs[occurrence_annotation_ok_def] >>
  qpat_x_assum `occurrence_natural_geometry _ _ _ _ _ _` mp_tac >>
  simp[occurrence_natural_geometry_def] >> strip_tac >>
  qpat_x_assum `!j. j < SUC (LENGTH stk) ==> _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `FLOOKUP B (a,aid) = SOME (b,z)` by gvs[occurrence_allocas_ok_def] >>
  metis_tac[pairTheory.FST]
QED

Theorem frame_reachable_intret_saved_frontier:
  frame_reachable vs C (f::stk) PG G tn fn ri sr /\
  vs.vs_allocas = FEMPTY /\ lo <= vs.vs_alloca_next /\ ~ctx_has_dalloca C /\
  active_inst fn ri sr /\ step_inst j C ri sr = IntRet ret se ==>
  f.cf_state.vs_alloca_next <= se.vs_alloca_next /\
  (!aid b z. FLOOKUP se.vs_allocas aid = SOME (b,z) ==>
             f.cf_state.vs_alloca_next <= b)
Proof
  strip_tac >>
  `ri.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `step_inst_base ri sr = IntRet ret se` by metis_tac[step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  `se.vs_allocas = sr.vs_allocas /\ se.vs_alloca_next = sr.vs_alloca_next` by
    (irule step_inst_base_preserves_alloca_fields >> qexists_tac `ri` >> simp[] >>
     metis_tac[]) >>
  drule_all frame_reachable_saved_frontier >> strip_tac >> simp[] >> metis_tac[]
QED
