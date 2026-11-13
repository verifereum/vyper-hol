Theory readonlyInvokeCopyFwdOperationalAllocation
Ancestors
  readonlyInvokeCopyFwdStepsAllocation readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdGlobalSupport
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdStepsCore ptrDiscipline taintAgree
  occurrenceGeometry o1LowerDloadOccurrence finite_map list pred_set arithmetic

Theorem ricf_alloca_support_fresh:
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  occurrence_allocas_ok B a s /\ FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  (a,inst.inst_id) NOTIN E
Proof
  rw[ricf_global_support_origins_def, occurrence_allocas_ok_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ricf_phase_allocation_bounds:
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  occurrence_natural_geometry lo a U B stk s /\
  (db,sb,sz) IN ricf_phase_ranges depth ledger /\ k < sz ==>
  db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next
Proof
  rw[ricf_heterogeneous_source_ledger_def, ricf_phase_ranges_def] >>
  fs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  fs[ricf_phase_entry_def, occurrence_natural_geometry_def] >>
  `p.rpe_db+p.rpe_size <= s.vs_alloca_next /\ p.rpe_sb+p.rpe_size <= s.vs_alloca_next` by metis_tac[] >>
  decide_tac
QED

Theorem ricf_translation_allocation_bounds:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key (db,sb,sz) /\
  occurrence_natural_geometry lo a U B stack state /\ k < sz ==>
  db+k < state.vs_alloca_next /\ sb+k < state.vs_alloca_next
Proof
  rw[ricf_translation_origin_def] >>
  fs[occurrence_natural_geometry_def] >>
  `p.rpe_db+p.rpe_size <= state.vs_alloca_next /\
   p.rpe_sb+p.rpe_size <= state.vs_alloca_next` by metis_tac[] >>
  decide_tac
QED

Theorem ricf_translation_positive:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key (db,sb,sz) ==>
  0 < sz
Proof
  rw[ricf_translation_origin_def,
     readonlyInvokeCopyFwdHistorySelectedTheory.ricf_history_inherited_def] >>
  metis_tac[readonlyInvokeCopyFwdReadonlyReachTheory.readonly_call_reachable_projection]
QED

Theorem ricf_alloca_map_fresh:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  occurrence_natural_geometry lo a U B stk s ==>
  (s.vs_alloca_next,z) NOTIN FDOM sites
Proof
  strip_tac >> simp[GSYM FLOOKUP_DEF] >> strip_tac >>
  `?tr. FLOOKUP sites (s.vs_alloca_next,z) = SOME tr` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B
    (s.vs_alloca_next,z) tr` by fs[ricf_map_origins_def] >>
  qpat_assum `ricf_translation_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_translation_origin_def]) >>
  `0 < p.rpe_size` by metis_tac[ricf_translation_positive] >>
  `p.rpe_db+p.rpe_size <= s.vs_alloca_next` by
    metis_tac[occurrence_natural_geometry_def] >>
  fs[]
QED

Theorem ricf_allocation_certificate_bounds:
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  cur = ricf_phase_ranges 0 ledger /\ curs = ricf_phase_stack_ranges stk ledger ==>
  !gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
    (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next
Proof
  strip_tac >> gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[ricf_phase_allocation_bounds]
  >- (gvs[ricf_phase_stack_ranges_def, MEM_GENLIST] >>
      drule_all ricf_phase_allocation_bounds >> simp[ADD_COMM])
  >- (gvs[ricf_site_triples_def] >>
      fs[ricf_map_origins_def] >> first_x_assum drule >> strip_tac >>
      drule_all ricf_translation_allocation_bounds >> simp[ADD_COMM]) >>
  gvs[ricf_site_triples_def] >>
  drule_all ricf_saved_map_origins_lookup >> strip_tac >>
  fs[ricf_translation_origin_def, occurrence_natural_geometry_def] >>
  `p.rpe_db+p.rpe_size <= s.vs_alloca_next /\
   p.rpe_sb+p.rpe_size <= s.vs_alloca_next` by metis_tac[] >> decide_tac
QED

(* All allocation guards are produced from history and live occurrences. *)
Theorem ricf_history_guarded_fresh_alloca:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  cur = ricf_phase_ranges 0 ledger /\ curs = ricf_phase_stack_ranges stk ledger /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  u = s with <|vs_allocas := s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,w2n amount));
                vs_alloca_next := s.vs_alloca_next+w2n amount|> /\
  v = t with <|vs_allocas := t.vs_allocas |+ (inst.inst_id,(t.vs_alloca_next,w2n amount));
                vs_alloca_next := t.vs_alloca_next+w2n amount|> /\
  un = tn0 with t_mem := tn0.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount} ==>
  (a,inst.inst_id) NOTIN E /\
  step_inst_base inst s = OK (update_var out (n2w s.vs_alloca_next) u) /\
  step_inst_base inst t = OK (update_var out (n2w s.vs_alloca_next) v) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (n2w s.vs_alloca_next) u)
      (set_prov G0 [out] (SOME (s.vs_alloca_next,w2n amount))))
    (ricf_effective_taint fn (update_var out (n2w s.vs_alloca_next) u)
      (un with t_var := set_var_taint un.t_var [out] {})) fn
    sites maps targets (set_prov G0 [out] (SOME (s.vs_alloca_next,w2n amount)))
    (un with t_var := set_var_taint un.t_var [out] {}) cur curs
    (update_var out (n2w s.vs_alloca_next) u)
    (update_var out (n2w s.vs_alloca_next) v)
Proof
  strip_tac >>
  `occurrence_allocas_ok B a s` by
    (fs[ricf_heterogeneous_source_ledger_def] >>
     drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  conj_tac >- metis_tac[ricf_alloca_support_fresh] >>
  `(s.vs_alloca_next,w2n amount) NOTIN FDOM sites` by
    metis_tac[ricf_alloca_map_fresh] >>
  irule ricf_cert_alloca_fresh >> reverse conj_tac
  >- (simp[] >> qexistsl_tac [`G`,`tn`,`tn0`] >> simp[] >> metis_tac[]) >>
  match_mp_tac ricf_allocation_certificate_bounds >> metis_tac[]
QED
