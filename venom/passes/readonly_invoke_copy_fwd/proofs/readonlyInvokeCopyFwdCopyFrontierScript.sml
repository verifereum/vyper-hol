(* A saved observer sees memory only below its own allocation frontier. *)
Theory readonlyInvokeCopyFwdCopyFrontier
Ancestors
  readonlyInvokeCopyFwdCopySteps readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdRel occurrenceGeometry regularCallEmitSim
  o1LowerDloadJointMemoryRead o1LowerDloadRangeTransport codegenRel
  taintAgree venomExecSemantics venomState
  finite_map list pred_set ptrDiscipline internalReturnCopyFwdSim words

Theorem ricf_frame_source_mcopy_frontier:
  ricf_frame_agree D X sites PG G tn s t /\
  {i | db <= i /\ i < db+len /\ i < s.vs_alloca_next} SUBSET X /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!b c z k. (b,c,z) IN ricf_site_triples sites /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_frame_agree D X sites PG G tn' (mcopy db sb len s) t
Proof
  strip_tac >>
  `ircf_cross tn' (ricf_site_triples sites) (mcopy db sb len s) t` by
    (irule ricf_cross_source_mcopy_frame >>
     fs[ricf_frame_agree_def] >> metis_tac[]) >>
  `taint_agree D X tn' (mcopy db sb len s)
     (t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>)` by
    (qpat_x_assum `tn' = _` SUBST1_TAC >>
     `mcopy db sb len s = s with vs_memory := (mcopy db sb len s).vs_memory` by
       simp[mcopy_def, write_memory_with_expansion_def] >>
     pop_assum SUBST1_TAC >>
     `taint_agree D X
       (tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
                         {db+q | q < len /\ sb+q IN tn.t_mem})
       (s with vs_memory := (mcopy db sb len s).vs_memory)
       ((t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>)
          with vs_memory := t.vs_memory)` suffices_by
       (simp[taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_def] >>
        metis_tac[]) >>
     irule taint_agree_memory_update >>
     reverse conj_tac >- fs[ricf_frame_agree_def] >>
     rpt strip_tac >>
     `~(db <= i /\ i < db+len)` by
       (fs[SUBSET_DEF] >> metis_tac[]) >>
     `i NOTIN tn.t_mem` by gvs[] >>
     simp[mcopy_def, regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
          GSYM read_memory_def, ld_read_memory_length] >>
     fs[ricf_frame_agree_def, taint_agree_def] >> metis_tac[]) >>
  qpat_x_assum `tn' = _` SUBST_ALL_TAC >>
  fs[ricf_frame_agree_def, mcopy_def, write_memory_with_expansion_def,
     op_taint_def]
QED

Theorem ricf_live_stack_source_mcopy_frontier:
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!j b c z k. j < LENGTH stk /\
    (b,c,z) IN ricf_site_triples (EL j maps) /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_live_stack_agree D ids tn' maps stk targets (mcopy db sb len s) t
Proof
  pure_rewrite_tac [ricf_live_stack_agree_def, ricf_mcopy_merge] >>
  strip_tac >> asm_rewrite_tac[] >> gen_tac >> strip_tac >>
  match_mp_tac (ricf_frame_source_mcopy_frontier |> Q.INST
    [`tn` |-> `tn with t_var := (EL j stk).cf_tvar`]) >>
  asm_simp_tac (srw_ss()) [GSYM merge_callee_state_def,
    merge_callee_state_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ricf_cert_activate_copy_frontier:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  {i | db <= i /\ i < db+len} SUBSET ircf_dead ids s stk /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn0.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  un = tn0 with t_mem :=
    (tn0.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn0.t_mem} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !b c z k. (b,c,z) IN gam /\ k < z ==>
      ~(db <= b+k /\ b+k < db+len) /\
      ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_cert_core D ids stk PG G
    (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
    fn sites maps targets G0 un (cur UNION {(db,sb,len)}) curs
    (mcopy db sb len s) t
Proof
  strip_tac >>
  `ircf_cross un (cur UNION {(db,sb,len)}) (mcopy db sb len s) t` by
    (irule ricf_cross_activate_copy >>
     fs[ricf_cert_core_def] >> metis_tac[]) >>
  `ricf_cert_crosses un curs stk (mcopy db sb len s) t` by
    (fs[ricf_cert_core_def, ricf_cert_crosses_def, EVERY_MEM] >>
     rpt strip_tac >>
     match_mp_tac (ricf_cross_source_mcopy_frame |> Q.INST [`tn` |-> `tn0`]) >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `ricf_frame_agree D (ircf_dead ids s stk) sites
     (ricf_complete_params PG s.vs_params) G0 un (mcopy db sb len s) t` by
    (match_mp_tac (ricf_frame_source_mcopy |> Q.INST [`tn` |-> `tn0`]) >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def] >> metis_tac[]) >>
  `ricf_live_stack_agree D ids un maps stk targets (mcopy db sb len s) t` by
    (match_mp_tac (ricf_live_stack_source_mcopy_frontier |> Q.INST [`tn` |-> `tn0`]) >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def] >> metis_tac[]) >>
  qpat_x_assum `un = _` SUBST_ALL_TAC >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def,
     ircf_dead_def, entry_prov_def, entry_taint_vars_def,
     mcopy_def, write_memory_with_expansion_def]
QED

Theorem ricf_cert_forwarded_copy_step_frontier:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [op_dst; op_src; op_size] /\
  inst.inst_outputs = [] /\ nop.inst_opcode = NOP /\
  nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  eval_operand op_dst s = SOME dst /\
  eval_operand op_src s = SOME src /\
  eval_operand op_size s = SOME sz /\
  db = w2n dst /\ sb = w2n src /\ len = w2n sz /\
  db+len <= dimword (:256) /\ sb+len <= dimword (:256) /\
  {i | db <= i /\ i < db+len} SUBSET ircf_dead ids s stk /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn0.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  un = tn0 with t_mem :=
    (tn0.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn0.t_mem} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !b c z k. (b,c,z) IN gam /\ k < z ==>
      ~(db <= b+k /\ b+k < db+len) /\
      ~(db <= c+k /\ c+k < db+len)) ==>
  step_inst_base inst s = OK (mcopy db sb len s) /\
  step_inst_base nop t = OK t /\
  ricf_cert_core D ids stk PG G
    (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
    fn sites maps targets G0 un (cur UNION {(db,sb,len)}) curs
    (mcopy db sb len s) t
Proof
  strip_tac >>
  `ricf_cert_core D ids stk PG G
     (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
     fn sites maps targets G0 un (cur UNION {(db,sb,len)}) curs
     (mcopy db sb len s) t` by
    (irule ricf_cert_activate_copy_frontier >> metis_tac[]) >>
  simp[step_inst_base_opcode_eqs]
QED

(* A current-activation occurrence lies above every suspended observer cut. *)
Theorem ricf_copy_saved_observer_geometry:
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B id = SOME (db,z) /\ FST id = a ==>
  !j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)
Proof
  rw[occurrence_natural_geometry_def] >>
  `(EL j stk).cf_state.vs_alloca_next <= db` by metis_tac[] >>
  decide_tac
QED

(* The caller has no allocations; the callee owns the destination.  Its
   nonidentity copy is invisible to the caller even though it is not dead
   in that caller.  In particular full saved-dead containment is false. *)
Theorem ricf_nested_copy_frontier_probe:
  !s a D.
  let current = ricf_copy_probe_state s;
      saved = a with <| vs_allocas := FEMPTY; vs_alloca_next := 0;
                        vs_vars := FEMPTY; vs_params := [] |> in
  ricf_frame_agree D (ircf_dead {7} saved []) FEMPTY [] FEMPTY entry_taint
    (mcopy 0 1 1 (merge_callee_state saved current))
    (merge_callee_state saved current) /\
  ~({i | 0 <= i /\ i < 0+1} SUBSET ircf_dead {7} saved []) /\
  FLOOKUP current.vs_allocas 7 = SOME (0,1) /\
  read_byte 0 (mcopy 0 1 1 current).vs_memory = 9w /\
  read_byte 0 current.vs_memory = 7w
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `merge_callee_state saved current` >>
  `ricf_frame_agree D (ircf_dead {7} saved []) FEMPTY [] FEMPTY entry_taint
     (merge_callee_state saved current) (merge_callee_state saved current)` by
    (irule ricf_frame_agree_identity >>
     simp[taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_refl,
       word_agree_except_def, merge_callee_state_def,
       Abbr `saved`]) >>
  conj_tac
  >- (match_mp_tac (ricf_frame_source_mcopy_frontier |>
        Q.INST [`tn` |-> `entry_taint`]) >>
      simp[Abbr `saved`, merge_callee_state_def, SUBSET_DEF,
           entry_taint_def, ricf_site_triples_def] >>
      fs[merge_callee_state_def]) >>
  simp[Abbr `saved`, Abbr `current`, ricf_copy_probe_state_def,
       ircf_dead_def, site_bytes_def, SUBSET_DEF, FLOOKUP_UPDATE,
       mcopy_def, write_memory_with_expansion_def, read_byte_def]
QED
