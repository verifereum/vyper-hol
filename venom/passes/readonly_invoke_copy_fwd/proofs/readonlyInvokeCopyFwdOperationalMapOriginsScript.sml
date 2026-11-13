(* Saved maps are observed at their own suspended call, not at the callee PC.
   These witnesses establish origins only, not relational byte preservation.
   In particular, pop below restores the suspended observation; advancing it
   past a return needs paired readonly_call_reachable exit witnesses for each
   origin.  The explicit selected anchor and the existential inherited-history
   anchor must not be identified without proof. *)
Theory readonlyInvokeCopyFwdOperationalMapOrigins
Ancestors
  readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdHistorySelected readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdHistoryInheritedLifecycle
  readonlyInvokeCopyFwdHistoryStackAlignment
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim o1LowerDloadOccurrence
  finite_map list rich_list pred_set

Definition ricf_saved_map_origins_def:
  ricf_saved_map_origins vs C ctx0 log stk U B maps <=>
    LENGTH maps = LENGTH stk /\ LENGTH U = LENGTH stk /\
    (!j. j < LENGTH stk ==> ?sn.
      sn.t_var = (EL j stk).cf_tvar /\
      ricf_map_origins vs C ctx0 log (DROP (SUC j) stk)
        (EL j stk).cf_params (EL j stk).cf_prov sn
        (EL j stk).cf_fn (EL j stk).cf_inst (EL j stk).cf_state
        (DROP (SUC j) U) B (EL j maps))
End

Theorem ricf_saved_map_origins_nil[simp]:
  ricf_saved_map_origins vs C ctx0 log [] [] B []
Proof
  simp[ricf_saved_map_origins_def]
QED

Theorem ricf_saved_map_origins_cons:
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  tn.t_var = f.cf_tvar /\
  ricf_map_origins vs C ctx0 log stk f.cf_params f.cf_prov tn
    f.cf_fn f.cf_inst f.cf_state U B sites ==>
  ricf_saved_map_origins vs C ctx0 log (f::stk) (u::U) B (sites::maps)
Proof
  rw[ricf_saved_map_origins_def] >> Cases_on `j` >> gvs[] >> metis_tac[]
QED

Theorem ricf_saved_map_origins_tail:
  ricf_saved_map_origins vs C ctx0 log (f::stk) (u::U) B (sites::maps) ==>
  ricf_saved_map_origins vs C ctx0 log stk U B maps
Proof
  rw[ricf_saved_map_origins_def] >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

(* Allocation preserves every endpoint already recorded by an origin,
   including origins observed at suspended caller states. *)
Theorem ricf_translation_origin_sites_step:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) key tr
Proof
  rw[ricf_translation_origin_def] >>
  qexistsl_tac [`p`, `pre`, `anchor`, `tail`, `atn`] >>
  simp[] >> metis_tac[occurrence_sites_step_preserves]
QED

Theorem ricf_map_origins_sites_step:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) sites
Proof
  rw[ricf_map_origins_def] >>
  irule ricf_translation_origin_sites_step >> metis_tac[]
QED

Theorem ricf_saved_map_origins_sites_step:
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_saved_map_origins vs C ctx0 log stk U
    (occurrence_sites_step a B alloc_inst u) maps
Proof
  rw[ricf_saved_map_origins_def] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `sn` >> simp[] >>
  irule ricf_map_origins_sites_step >> metis_tac[]
QED

Theorem ricf_translation_origin_selected:
  ricf_history_cursor vs C ctx0 log p [] PG G tn caller s /\
  frame_reachable vs C stk PG G tn caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  FLOOKUP s.vs_allocas (SND p.rpe_dst) = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP s.vs_allocas (SND p.rpe_src) = SOME (p.rpe_sb,p.rpe_size) /\
  0 < p.rpe_size /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  a = p.rpe_owner /\
  s.vs_current_bb = p.rpe_block.bb_label /\
  ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx /\
  callinst = EL s.vs_inst_idx p.rpe_block.bb_instructions ==>
  ricf_translation_origin vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (p.rpe_db,p.rpe_size) (p.rpe_db,p.rpe_sb,p.rpe_size)
Proof
  strip_tac >>
  drule_all ricf_history_inherited_start >> strip_tac >>
  drule ricf_history_cursor_endpoint_owners >> strip_tac >>
  simp[ricf_translation_origin_def] >>
  qexistsl_tac [`p`, `[]`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>`, `stk`, `tn`] >>
  gvs[]
QED

Theorem ricf_translation_origin_nested_call:
  ricf_translation_origin vs C ctx0 log stk PG G tn caller callinst s U B key tr /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_translation_origin vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (u::U) B key tr
Proof
  simp[ricf_translation_origin_def] >> rpt strip_tac >>
  qexistsl_tac [`p`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
    `anchor`, `tail`, `atn`] >> simp[] >>
  irule ricf_history_inherited_call >> metis_tac[]
QED

(* Functional-map overwrite handles collisions: only the new binding survives. *)
Theorem ricf_map_origins_update:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr ==>
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B (sites |+ (key,tr))
Proof
  rw[ricf_map_origins_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ricf_map_origins_nested_call:
  ricf_map_origins vs C ctx0 log stk PG G tn caller callinst s U B sites /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_map_origins vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (u::U) B sites
Proof
  rw[ricf_map_origins_def] >> irule ricf_translation_origin_nested_call >>
  metis_tac[]
QED

Theorem ricf_translation_origin_endpoints:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr ==>
  ?p pre anchor tail atn.
    key = (p.rpe_db,p.rpe_size) /\ tr = (p.rpe_db,p.rpe_sb,p.rpe_size) /\
    FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
    FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
    stk = pre ++ anchor::tail /\ LENGTH pre < LENGTH U /\
    (EL (LENGTH pre) U).of_owner = p.rpe_owner /\
    FST p.rpe_dst = p.rpe_owner /\ FST p.rpe_src = p.rpe_owner /\
    atn.t_var = anchor.cf_tvar /\
    ricf_history_cursor vs C ctx0 log p [] anchor.cf_params anchor.cf_prov
      atn anchor.cf_fn anchor.cf_state
Proof
  rw[ricf_translation_origin_def] >> metis_tac[]
QED

Theorem ricf_translation_origin_restrict_owners:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr /\
  (!u. MEM u U ==> u.of_owner <> a) ==>
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U
    (DRESTRICT B {id | FST id <> a}) key tr
Proof
  rw[ricf_translation_origin_def] >>
  `p.rpe_owner <> a` by metis_tac[MEM_EL] >>
  qexistsl_tac [`p`, `pre`, `anchor`, `tail`, `atn`] >>
  simp[FLOOKUP_DRESTRICT]
QED

Theorem ricf_map_origins_restrict_owners:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  (!u. MEM u U ==> u.of_owner <> a) ==>
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U
    (DRESTRICT B {id | FST id <> a}) sites
Proof
  rw[ricf_map_origins_def] >> irule ricf_translation_origin_restrict_owners >>
  metis_tac[]
QED

Theorem ricf_saved_map_origins_restrict_owners:
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  (!u. MEM u U ==> u.of_owner <> a) ==>
  ricf_saved_map_origins vs C ctx0 log stk U
    (DRESTRICT B {id | FST id <> a}) maps
Proof
  rw[ricf_saved_map_origins_def] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `sn` >> simp[] >> irule ricf_map_origins_restrict_owners >>
  metis_tac[MEM_DROP_IMP]
QED

(* Pop restores the real saved map, not an existential replacement map.
   This is restoration at its suspended observation point only. *)
Theorem ricf_saved_map_origins_pop:
  ricf_saved_map_origins vs C ctx0 log (f::stk) (u::U) B (sites::maps) /\
  (!v. MEM v U ==> v.of_owner <> a) ==>
  (?sn. sn.t_var = f.cf_tvar /\
    ricf_map_origins vs C ctx0 log stk f.cf_params f.cf_prov sn
      f.cf_fn f.cf_inst f.cf_state U (DRESTRICT B {id | FST id <> a}) sites) /\
  ricf_saved_map_origins vs C ctx0 log stk U
    (DRESTRICT B {id | FST id <> a}) maps
Proof
  strip_tac >> conj_tac
  >- (fs[ricf_saved_map_origins_def] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `sn` >> simp[] >> irule ricf_map_origins_restrict_owners >>
      metis_tac[]) >>
  irule ricf_saved_map_origins_restrict_owners >>
  metis_tac[ricf_saved_map_origins_tail]
QED

Theorem ricf_saved_map_origins_lookup:
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  j < LENGTH stk /\ FLOOKUP (EL j maps) key = SOME tr ==>
  ?sn. sn.t_var = (EL j stk).cf_tvar /\
    ricf_translation_origin vs C ctx0 log (DROP (SUC j) stk)
      (EL j stk).cf_params (EL j stk).cf_prov sn
      (EL j stk).cf_fn (EL j stk).cf_inst (EL j stk).cf_state
      (DROP (SUC j) U) B key tr
Proof
  rw[ricf_saved_map_origins_def] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
  metis_tac[ricf_map_origins_def]
QED

Definition ricf_origin_core_def:
  ricf_origin_core vs C ctx0 log D ids stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets G0 tn0 cur curs <=>
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_operational_support vs C ctx0 log stk PG G tn fn inst s
    n a U B HP H ledger E sites t /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps
End

Theorem ricf_origin_core_cert:
  ricf_origin_core vs C ctx0 log D ids stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets G0 tn0 cur curs ==>
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t
Proof
  simp[ricf_origin_core_def]
QED

Theorem ricf_origin_core_support:
  ricf_origin_core vs C ctx0 log D ids stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets G0 tn0 cur curs ==>
  ricf_operational_support vs C ctx0 log stk PG G tn fn inst s
    n a U B HP H ledger E sites t
Proof
  simp[ricf_origin_core_def]
QED

Theorem ricf_origin_core_initial:
  s.vs_prev_bb = NONE /\ taint_agree D (ircf_dead ids s []) tn s s /\
  occ_frame_reachable vs C [] [] FEMPTY tn fn inst s n a [] B HP H ==>
  ricf_origin_core vs C ctx0 log D ids [] [] FEMPTY tn fn inst s s
    n a [] B HP H [] {} FEMPTY [] [] FEMPTY tn {} []
Proof
  strip_tac >>
  simp[ricf_origin_core_def, ricf_cert_core_def, ricf_cert_crosses_def,
    ricf_live_boundary_core_def, ricf_frame_agree_completed_identity,
    ricf_live_stack_agree_def, ircf_cross_def, ricf_saved_map_origins_nil] >>
  metis_tac[ricf_operational_support_initial]
QED
