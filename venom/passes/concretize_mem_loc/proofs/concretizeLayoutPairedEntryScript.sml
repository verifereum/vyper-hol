Theory concretizeLayoutPairedEntry
Ancestors concretizeStepStructure concretizeLayoutBlockPairing concretizeLayoutSelectedBaseInterface
  concretizeLayoutPhaseCompose concretizeLayoutPhaseNop frameFiniteExecution
  concretizeLayoutPhaseOrigin concretizeLayoutAlignedControl frameControlAgreement
  concretizeLayoutPhaseAllocation concretizeMemLocDefs passSharedDefs finite_map
  frameRelocationLocal frameRelocationValues frameRelocationEnvironment
  concretizeLayoutSupplement concretizeLayoutReaderContext ptrDiscipline
  venomState venomInst venomExecSemantics frameSelectedSimulation arithmetic list

(* Ordinary entries can be paired without requiring a target lookup for a
   source instruction which was removed.  Terminal corridors are deliberately
   not hidden in this wrapper: their equal-index interface needs validation. *)
Definition layout_paired_ordinary_def:
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe positions q n bb s bb' t a <=>
    ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
    a.lop_origin.lbo_source = bb /\ a.lop_origin.lbo_target = bb' /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qe a s t /\
    layout_block_pair positions bb bb' s.vs_inst_idx t.vs_inst_idx
End

Definition layout_paired_step_def:
  layout_paired_step D lo vs0 C C' q0 path es qs qe positions q n i s j t <=>
    layout_base_lookahead C q0 path q n i s /\
    ?bb bb' a. layout_paired_ordinary D lo vs0 C C' q0 es qs qe
      positions q n bb s bb' t a /\
      get_instruction bb s.vs_inst_idx = SOME i /\
      ((i.inst_opcode = NOP /\ j = i) \/
       ((concretize_inst_with_positions positions i).inst_opcode <> NOP /\
        j = concretize_inst_with_positions positions i))
End

Theorem layout_paired_ordinary_initialize:
  MEM bb fn.fn_blocks /\ bb_well_formed bb /\
  bb' = clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb) /\
  s.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  t.vs_inst_idx = phi_prefix_length bb'.bb_instructions /\
  ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
  a.lop_origin.lbo_source = bb /\ a.lop_origin.lbo_target = bb' /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qe a s t ==>
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe
    positions q n bb s bb' t a
Proof
  strip_tac >> simp[layout_paired_ordinary_def] >>
  irule layout_block_pair_phi_entry >> simp[]
QED

Theorem layout_paired_step_produce:
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe
    positions q n bb s bb' t a /\
  layout_base_lookahead C q0 path q n i s /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (i.inst_opcode = NOP \/
   (concretize_inst_with_positions positions i).inst_opcode <> NOP) ==>
  ?j. layout_paired_step D lo vs0 C C' q0 path es qs qe positions q n i s j t
Proof
  simp[layout_paired_step_def] >> metis_tac[]
QED

(* A real retained lookup recovers the existing semantic base witness. *)
Theorem layout_paired_retained_witness:
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe
    positions q n bb s bb' t a /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (concretize_inst_with_positions positions i).inst_opcode <> NOP ==>
  layout_base_witness D lo vs0 C C' q0 es qs qe q n i s
    (concretize_inst_with_positions positions i) t (INL a)
Proof
  simp[layout_paired_ordinary_def, layout_base_witness_def] >> strip_tac >>
  gvs[] >> drule_all layout_block_pair_lookup >> simp[]
QED

(* Target indices are not part of the ordinary semantic relation.  This is
   the asymmetric administrative operation needed after a removed source NOP. *)
Theorem layout_ordinary_state_target_index:
  layout_ordinary_state D lo C' q0 es qs a s t ==>
  layout_ordinary_state D lo C' q0 es qs a s (t with vs_inst_idx := k)
Proof
  Cases_on `a.lop_config` >>
  simp[layout_ordinary_state_def] >> rpt strip_tac >>
  gvs[local_rel_def, variable_domains_def, variables_agree_on_def,
    local_values_def, lookup_var_def, concretize_supplement_def,
    relocation_env_def, relocation_reader_context_def,
    concretize_local_obs_def, dead_result_rel_def] >> metis_tac[]
QED

Theorem layout_ordinary_stutter_administrative:
  a.lop_pending /\ layout_aligned_entry D lo vs0 C C' q0 es qs qe a s t ==>
  layout_aligned_entry D lo vs0 C C' q0 es qs qe
    (a with lop_pending := F) (s with vs_inst_idx := SUC s.vs_inst_idx) t
Proof
  simp[layout_aligned_entry_def] >> strip_tac >>
  drule layout_ordinary_administrative >> simp[] >> strip_tac >>
  simp[layout_aligned_entry_def, control_agree_def] >>
  fs[layout_ordinary_entry_def] >>
  drule layout_ordinary_state_target_index >>
  disch_then (qspec_then `t.vs_inst_idx` mp_tac) >> fs[control_agree_def]
QED

(* Bounded next-certificate fragment: the target block is executed from t,
   not from the successor of t, and no lookup of the virtual NOP is needed. *)
Theorem layout_selected_stutter_continuation:
  EB qn (n+LENGTH ws+1) bb
    (post with vs_inst_idx := SUC s.vs_inst_idx) bb' t ==>
  ?tb. EB qn (n+LENGTH ws+1) bb
    (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
    (!rb'. finite_block C' bb' tb rb' /\ R qe (n+LENGTH ws+1+LENGTH wb) r rb' ==>
      selected_block_match C'
        (\q n qe ne bb s bb' t r r'. R qe ne r r')
        q n (ws++[(ev,qn)]++wb) qe bb s bb' t r)
Proof
  strip_tac >> qexists `t` >> simp[selected_block_match_def] >>
  rpt strip_tac >> qexists `rb'` >> simp[ADD_ASSOC]
QED

(* The virtual step exists independently of any target block lookup. *)
Theorem layout_selected_virtual_nop:
  i.inst_opcode = NOP /\ OS q n q n i s i t (OK s) (OK t) ==>
  selected_step_match C' OS q n [] q i s i t (OK s)
Proof
  strip_tac >> simp[selected_step_match_def] >> qexists `OK t` >> simp[] >>
  irule finite_step_base >> simp[step_inst_base_def]
QED

Theorem layout_paired_nop_next:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe
    positions q n bb s bb' t a /\
  q = JointConfig stk PG G tn fn inst s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  n < LENGTH es /\ EL n es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = NOP /\ o1_fn_shape C fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k. k.lop_cursor = SUC n /\ ~k.lop_pending /\
    k.lop_origin = a.lop_origin /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qe k
      (post with vs_inst_idx := SUC s.vs_inst_idx) t /\
    layout_block_pair positions bb bb' (SUC s.vs_inst_idx) t.vs_inst_idx
Proof
  strip_tac >>
  `post = s` by gvs[step_inst_base_def] >>
  qpat_x_assum `post = s` SUBST_ALL_TAC >>
  `layout_block_pair positions bb bb' (SUC s.vs_inst_idx) t.vs_inst_idx` by
    (fs[layout_paired_ordinary_def] >>
     drule_all layout_block_pair_advance >> simp[concretize_positions_nop]) >>
  gvs[layout_paired_ordinary_def, layout_aligned_entry_def] >>
  drule_all layout_nop_trace_step >> strip_tac >>
  fs[layout_phase_ok_abort_def, layout_phase_entry_def, layout_phase_origin_def] >>
  `layout_aligned_entry D lo vs0 C C' q0 es qs qe k s t` by
    simp[layout_aligned_entry_def] >>
  drule_all layout_ordinary_stutter_administrative >> strip_tac >>
  qexists `k with lop_pending := F` >> fs[layout_aligned_entry_def]
QED

Theorem layout_paired_unchanged_step:
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe
    positions q n bb s bb' t a /\
  layout_base_lookahead C q0 path q n i s /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> ALLOCA /\ i.inst_opcode <> NOP ==>
  layout_selected_base_entry D lo vs0 C C' q0 path es qs qe q n i s i t /\
  layout_block_pair positions bb bb' (SUC s.vs_inst_idx) (SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `(concretize_inst_with_positions positions i).inst_opcode <> NOP` by
    simp[concretize_positions_unchanged] >> conj_tac
  >- (simp[layout_selected_base_entry_def] >> qexists `INL a` >>
      drule_all layout_paired_retained_witness >>
      simp[concretize_positions_unchanged]) >>
  fs[layout_paired_ordinary_def] >> drule_all layout_block_pair_advance >>
  simp[concretize_positions_unchanged, ADD1]
QED

(* With the checked producer's position premise the ALLOCA is retained.
   This theorem intentionally does not assert that reachability supplies that
   premise: that is a layout-row coverage obligation, not a step fact. *)
Theorem layout_paired_alloca_step:
  vs0.vs_allocas = FEMPTY /\
  layout_paired_ordinary D lo vs0 C C' q0 es qs qe
    positions q n bb s bb' t a /\
  q = JointConfig stk PG G tn fn inst s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  n < LENGTH es /\ EL n es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [v] /\
  FLOOKUP positions (Allocation inst.inst_id) =
    SOME (concretize_positions C' fn inst.inst_id) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  get_instruction bb' t.vs_inst_idx =
    SOME (concretize_inst_with_positions positions inst) /\
  layout_block_pair positions bb bb' (SUC s.vs_inst_idx) (SUC t.vs_inst_idx) /\
  ?k tpost. step_inst_base (concretize_inst_with_positions positions inst) t = OK tpost /\
    k.lop_pending /\ k.lop_cursor = SUC n /\
    k.lop_origin = a.lop_origin /\ k.lop_ids = a.lop_ids /\
    k.lop_config = EL (SUC n) (q0::qs) /\
    resolved_annotation_update a.lop_config (EL n es)
      a.lop_ids a.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs qe
      (INL a) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `(concretize_inst_with_positions positions inst).inst_opcode <> NOP` by
    simp[concretize_inst_with_positions_def, mk_assign_inst_def] >>
  conj_tac
  >- (fs[layout_paired_ordinary_def] >> drule_all layout_block_pair_lookup >> simp[]) >>
  conj_tac
  >- (fs[layout_paired_ordinary_def] >> drule_all layout_block_pair_advance >>
      simp[ADD1]) >>
  gvs[layout_paired_ordinary_def, layout_aligned_entry_def] >>
  drule_all layout_alloca_trace_step >> simp[]
QED

val _ = export_theory();
