Theory readonlyInvokeCopyFwdOperationalAllocation
Ancestors
  readonlyInvokeCopyFwdStepsAllocation readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdGlobalSupport
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdStepsCore ptrDiscipline taintAgree
  occurrenceGeometry o1LowerDloadOccurrence ptrPhiUpdate ptrFreshAllocaPath
  finite_map list pred_set arithmetic

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

Theorem ricf_actual_fresh_alloca_annotations:
  (!f. MEM f C.ctx_functions ==> wf_function f /\ fn_inst_wf f /\ wf_ssa f) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  G = ricf_effective_prov fn s G0 /\ tn = ricf_effective_taint fn s tn0 /\
  u = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,w2n amount));
              vs_alloca_next := s.vs_alloca_next+w2n amount|>) /\
  H = set_prov G0 [out] (SOME (s.vs_alloca_next,w2n amount)) /\
  un = (tn0 with t_mem := tn0.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount})
    with t_var := set_var_taint tn0.t_var [out] {} ==>
  ricf_effective_prov fn u H = step_prov PG G inst u /\
  ricf_effective_taint fn u un = step_taint inst s u tn /\
  ricf_effective_prov fn (u with vs_inst_idx := SUC s.vs_inst_idx) H =
    ricf_effective_prov fn u H /\
  ricf_effective_taint fn (u with vs_inst_idx := SUC s.vs_inst_idx) un =
    ricf_effective_taint fn u un
Proof
  strip_tac >>
  `!xs prev t1 t2. t1.t_var = t2.t_var ==>
    phis_taint prev t1 xs = phis_taint prev t2 xs` by
    (Induct >> simp[phis_taint_def] >> rpt strip_tac >>
     `!prev. phis_taint prev t1 xs = phis_taint prev t2 xs` by metis_tac[] >>
     Cases_on `h.inst_opcode = PHI` >> simp[] >>
     Cases_on `prev` >> simp[phi_taint_def] >>
     Cases_on `resolve_phi x h.inst_operands` >> simp[] >>
     Cases_on `x'` >> simp[op_taint_def]) >>
  `!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
    EVERY (\i. ~MEM out i.inst_outputs /\
      (!lbl. s.vs_prev_bb = SOME lbl ==>
        resolve_phi lbl i.inst_operands <> SOME (Var out)))
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (rpt strip_tac >> `MEM out inst.inst_outputs` by simp[] >>
     drule_all frame_reachable_fresh_alloca_phi_prefix_independent >> simp[]) >>
  `new_site_bytes s u =
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount}` by
    (gvs[new_site_bytes_def, venomStateTheory.update_var_def] >>
     simp[EXTENSION, FLOOKUP_UPDATE] >> gen_tac >> eq_tac
     >- (strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[FLOOKUP_DEF]) >>
     strip_tac >> qexistsl_tac [`inst.inst_id`,`s.vs_alloca_next`,`w2n amount`] >>
     fs[FLOOKUP_DEF]) >>
  gvs[ricf_effective_prov_def, ricf_effective_taint_def,
      entry_prov_def, entry_taint_vars_def, venomStateTheory.update_var_def,
      step_prov_def, out_prov_def, step_taint_def, out_taint_def,
      mem_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, set_prov_def,
      set_var_taint_def, FLOOKUP_UPDATE, venomStateTheory.eval_operand_def,
      codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
  Cases_on `s.vs_prev_bb = NONE` >> gvs[taint_component_equality] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  gvs[taint_component_equality] >>
  conj_tac
  >- (once_rewrite_tac[phis_prov_prefix] >>
      irule phis_prov_update_commute >> simp[]) >>
  qmatch_goalsub_abbrev_tac `phis_taint prev post xs` >>
  `phis_taint prev post xs = phis_taint prev (tn0 with t_var := tn0.t_var |+ (out,{})) xs` by
    (first_x_assum irule >> simp[Abbr `post`]) >>
  pop_assum SUBST1_TAC >>
  once_rewrite_tac[phis_taint_prefix] >>
  irule phis_taint_update_commute >> simp[Abbr `prev`, Abbr `xs`]
QED
