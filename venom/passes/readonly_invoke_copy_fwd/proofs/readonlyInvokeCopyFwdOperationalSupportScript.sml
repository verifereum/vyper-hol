(* Disagreement support outlives the current cross-certificate ledger. *)
Theory readonlyInvokeCopyFwdOperationalSupport
Ancestors
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdHistoryPhaseAllocation
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdProtectionLifetime readonlyInvokeCopyFwdMemory
  regularCallEmitSim o1LowerDloadJointMemoryRead o1LowerDloadRangeTransport occurrenceGeometry
  o1LowerDloadOccurrence
  taintAgree internalReturnCopyFwdSim venomExecSemantics venomState finite_map list pred_set words

Definition ricf_support_bytes_def:
  ricf_support_bytes B E =
    {i | ?id b z. id IN E /\ FLOOKUP B id = SOME (b,z) /\ b <= i /\ i < b+z}
End

Definition ricf_support_agree_def:
  ricf_support_agree B E tn s t <=>
    !i. i < s.vs_alloca_next /\ i NOTIN tn.t_mem /\
        i NOTIN ricf_support_bytes B E ==>
        read_byte i s.vs_memory = read_byte i t.vs_memory
End

(* Origins retain actual source execution, not merely static destination ids.
   They deliberately do not require the current phase ledger to retain p. *)
Definition ricf_support_origins_def:
  ricf_support_origins vs C ctx0 log B E <=>
    !id. id IN E ==> ?p stk PG G tn.
      ricf_history_origin vs C ctx0 log p stk PG G tn /\
      p.rpe_dst = id /\ FLOOKUP B id = SOME (p.rpe_db,p.rpe_size)
End

Theorem ricf_support_empty_identity:
  ricf_support_agree B {} tn s s /\
  ricf_support_origins vs C ctx0 log B {}
Proof
  simp[ricf_support_agree_def, ricf_support_origins_def]
QED

Theorem ricf_support_bytes_extend:
  E SUBSET E' /\ (!id. id IN E ==> FLOOKUP B' id = FLOOKUP B id) ==>
  ricf_support_bytes B E SUBSET ricf_support_bytes B' E'
Proof
  rw[ricf_support_bytes_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ricf_support_source_mcopy:
  ricf_support_agree B E tn s t /\ FLOOKUP B id = SOME (db,len) ==>
  ricf_support_agree B (E UNION {id})
    (tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
      {db+q | q < len /\ sb+q IN tn.t_mem})
    (mcopy db sb len s) t
Proof
  rw[ricf_support_agree_def] >>
  `~(db <= i /\ i < db+len)` by
    (fs[ricf_support_bytes_def] >> metis_tac[]) >>
  `i NOTIN ricf_support_bytes B E /\ i NOTIN tn.t_mem` by
    (fs[ricf_support_bytes_def] >> metis_tac[]) >>
  fs[mcopy_def, regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
     GSYM read_memory_def, ld_read_memory_length]
QED

(* Fresh allocation exposes only tainted bytes.  No equality of previously
   unobserved memory above the old frontier is assumed. *)
Theorem ricf_support_fresh_alloca:
  ricf_support_agree B E tn s t /\ id NOTIN E ==>
  ricf_support_agree (B |+ (id,(s.vs_alloca_next,z))) E
    (tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z})
    (s with <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,z));
              vs_alloca_next := s.vs_alloca_next+z|>)
    (t with <|vs_allocas := t.vs_allocas |+ (aid,(t.vs_alloca_next,z));
              vs_alloca_next := t.vs_alloca_next+z|>)
Proof
  rw[ricf_support_agree_def] >>
  `i < s.vs_alloca_next` by fs[] >>
  first_x_assum irule >> simp[] >>
  fs[ricf_support_bytes_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ricf_support_repeat_after_reset:
  ricf_support_bytes B ((E UNION {id}) UNION {id}) =
    ricf_support_bytes B (E UNION {id}) /\
  ricf_phase_ranges depth [] = {}
Proof
  simp[ricf_support_bytes_def, EXTENSION] >> metis_tac[]
QED

(* A translation names its installation call and owner, rather than inverting
   a numeric base.  The anchor is an actual saved original-source call. *)
Definition ricf_translation_origin_def:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key triple <=>
    ?p pre anchor tail atn.
      triple = (p.rpe_db,p.rpe_sb,p.rpe_size) /\
      key = (p.rpe_db,p.rpe_size) /\
      FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
      FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
      stk = pre ++ anchor::tail /\ LENGTH pre < LENGTH U /\
      (EL (LENGTH pre) U).of_owner = p.rpe_owner /\
      FST p.rpe_dst = p.rpe_owner /\ FST p.rpe_src = p.rpe_owner /\
      anchor.cf_state.vs_current_bb = p.rpe_block.bb_label /\
      ricf_selected_position p.rpe_event p.rpe_block anchor.cf_state.vs_inst_idx /\
      anchor.cf_inst.inst_opcode = INVOKE /\
      anchor.cf_inst = EL anchor.cf_state.vs_inst_idx p.rpe_block.bb_instructions /\
      atn.t_var = anchor.cf_tvar /\
      ricf_history_cursor vs C ctx0 log p [] anchor.cf_params anchor.cf_prov
        atn anchor.cf_fn anchor.cf_state /\
      ricf_history_inherited vs C ctx0 log p stk PG G tn fn inst s
End

Definition ricf_map_origins_def:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites <=>
    !key triple. FLOOKUP sites key = SOME triple ==>
      ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key triple
End

Theorem ricf_map_origins_empty:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B FEMPTY
Proof
  simp[ricf_map_origins_def]
QED

Definition ricf_operational_support_def:
  ricf_operational_support vs C ctx0 log stk PG G tn fn inst s n a U B HP H
    ledger E sites t <=>
    ricf_source_ledger vs C ctx0 log stk PG G tn fn inst s n a U B HP H ledger /\
    ricf_support_origins vs C ctx0 log B E /\
    ricf_support_agree B E tn s t /\
    ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites
End

Theorem ricf_operational_support_initial:
  occ_frame_reachable vs C [] PG G tn fn inst s n a [] B HP H ==>
  ricf_operational_support vs C ctx0 log [] PG G tn fn inst s n a [] B HP H
    [] {} FEMPTY s /\ ricf_phase_stack_ranges [] [] = []
Proof
  simp[ricf_operational_support_def, ricf_source_ledger_empty,
       ricf_support_empty_identity, ricf_map_origins_empty,
       ricf_phase_stack_ranges_def]
QED

Theorem ricf_support_origins_activate:
  ricf_support_origins vs C ctx0 log B E /\
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) ==>
  ricf_support_origins vs C ctx0 log B (E UNION {p.rpe_dst})
Proof
  rw[ricf_support_origins_def] >> metis_tac[]
QED

(* A first copy establishes the relational byte certificate from identity.
   There is no post-copy agreement hypothesis and no source-byte hypothesis. *)
Theorem ricf_support_first_copy:
  FLOOKUP B id = SOME (db,len) /\
  (db+len <= sb \/ sb+len <= db) ==>
  ricf_support_agree B {id}
    (tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
      {db+q | q < len /\ sb+q IN tn.t_mem})
    (mcopy db sb len s) s /\
  ircf_cross
    (tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
      {db+q | q < len /\ sb+q IN tn.t_mem})
    {(db,sb,len)} (mcopy db sb len s) s
Proof
  strip_tac >> (conj_tac
  >- (match_mp_tac (ricf_support_source_mcopy |> Q.INST [`E` |-> `{}`] |> SRULE []) >>
      simp[ricf_support_agree_def]) >>
  irule (ricf_cross_activate_copy |> Q.INST [`gam` |-> `{}`] |> SRULE []) >>
  simp[ircf_cross_def] >> metis_tac[])
QED

(* Operand production and actual stepping are supplied by Availability.  The
   extra dynamic premises describe distinct live endpoint occurrences and
   ordinary representable allocation geometry, not activation guards. *)
Theorem ricf_located_first_copy_support:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  FLOOKUP H dst <> FLOOKUP H sv /\ 0 < w2n z /\
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) ==>
  ?da sa db sb u un.
    FLOOKUP H dst = SOME (a,da) /\ FLOOKUP H sv = SOME (a,sa) /\
    FLOOKUP B (a,da) = SOME (db,w2n z) /\
    FLOOKUP B (a,sa) = SOME (sb,w2n z) /\
    (!fuel. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u) /\
    u = mcopy db sb (w2n z) s /\
    un = tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
      {db+q | q < w2n z /\ sb+q IN tn.t_mem} /\
    ricf_support_agree B {(a,da)} un u s /\
    ircf_cross un {(db,sb,w2n z)} u s /\
    ricf_map_origins vs C ctx0 log stk PG G tn fn
      (ricf_event_copy e (EL b fn.fn_blocks)) s U B FEMPTY
Proof
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  gvs[] >>
  `db + w2n z <= s.vs_alloca_next /\ sb + w2n z <= s.vs_alloca_next /\
   (db + w2n z <= sb \/ sb + w2n z <= db)` by
    (fs[occurrence_natural_geometry_def] >> metis_tac[pairTheory.PAIR_EQ]) >>
  `db < dimword (:256) /\ sb < dimword (:256)` by decide_tac >>
  `w2n (n2w db : bytes32) = db /\ w2n (n2w sb : bytes32) = sb` by
    simp[] >>
  qpat_assum `FLOOKUP B (a,da.inst_id) = _`
    (mp_then Any mp_tac ricf_support_first_copy) >>
  disch_then (qspecl_then [`tn`,`sb`,`s`] mp_tac) >>
  simp[ricf_map_origins_empty]
QED

Theorem ricf_support_zero_copy:
  ricf_support_agree B E tn s t ==>
  ricf_support_agree B E tn (mcopy db sb 0 s) t
Proof
  rw[ricf_support_agree_def] >>
  fs[mcopy_def, regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
     GSYM read_memory_def, ld_read_memory_length]
QED

Theorem ricf_located_zero_copy_support:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit 0w] /\
  ricf_support_agree B E tn s t ==>
  ?u. (!fuel. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u) /\
    ricf_support_agree B E tn u t /\
    (!i. read_byte i u.vs_memory = read_byte i s.vs_memory)
Proof
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  gvs[] >> conj_tac
  >- (irule ricf_support_zero_copy >> simp[]) >>
  simp[mcopy_def, regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
       GSYM read_memory_def, ld_read_memory_length]
QED

(* Test the actual fresh ALLOCA branch; memory outside the old cut may differ.
   Both runs have the same allocation metadata, but no memory equality is
   imposed above their frontier. *)
Theorem ricf_support_actual_fresh_alloca:
  ricf_support_agree B E tn s t /\
  s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit z] /\
  inst.inst_outputs = [out] /\ (a,inst.inst_id) NOTIN E ==>
  ?u v.
    step_inst_base inst s = OK u /\ step_inst_base inst t = OK v /\
    FLOOKUP (occurrence_sites_step a B inst u) (a,inst.inst_id) =
      SOME (s.vs_alloca_next,w2n z) /\
    ricf_support_agree (occurrence_sites_step a B inst u) E
      (tn with t_mem := tn.t_mem UNION
        {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n z}) u v
Proof
  strip_tac >>
  qpat_assum `ricf_support_agree B E tn s t`
    (mp_then Any mp_tac ricf_support_fresh_alloca) >>
  disch_then (qspecl_then [`w2n z`,`(a,inst.inst_id)`,`inst.inst_id`] mp_tac) >>
  `FLOOKUP t.vs_allocas inst.inst_id = NONE` by metis_tac[] >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def, occurrence_sites_step_def,
       update_var_def, FLOOKUP_UPDATE, ricf_support_agree_def]
QED

(* Existing disagreement support is retained, including after ledger reset. *)
Theorem ricf_located_copy_support_update:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\ ricf_support_agree B E tn s t ==>
  ?da sa db sb u un.
    FLOOKUP H dst = SOME (a,da) /\ FLOOKUP H sv = SOME (a,sa) /\
    FLOOKUP B (a,da) = SOME (db,w2n z) /\
    FLOOKUP B (a,sa) = SOME (sb,w2n z) /\
    (!fuel. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u) /\
    u = mcopy db sb (w2n z) s /\
    un = tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
      {db+q | q < w2n z /\ sb+q IN tn.t_mem} /\
    ricf_support_agree B (E UNION {(a,da)}) un u t
Proof
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  gvs[] >>
  `db + w2n z <= s.vs_alloca_next /\ sb + w2n z <= s.vs_alloca_next` by
    (fs[occurrence_natural_geometry_def] >> metis_tac[]) >>
  `db < dimword (:256) /\ sb < dimword (:256)` by decide_tac >>
  `w2n (n2w db : bytes32) = db /\ w2n (n2w sb : bytes32) = sb` by simp[] >>
  qpat_assum `ricf_support_agree B E tn s t`
    (mp_then Any mp_tac ricf_support_source_mcopy) >>
  simp[]
QED
