(* Production-history annotations for source allocation occurrences.
   Identities are (frame serial, instruction id), never inverse site lookups. *)
Theory o1LowerDloadOccurrence
Ancestors
  o1LowerDloadGhost o1LowerDloadAllocation ptrDiscipline finite_map
  venomExecSemantics venomMemProps venomExecProofs pred_set list

Datatype:
  occurrence_frame = <| of_owner : num;
                        of_prov : (string, num # num) fmap;
                        of_params : (num # num) option list |>
End

Definition occurrence_out_def:
  occurrence_out a HP H inst s' =
    if inst.inst_opcode = ALLOCA then
      OPTION_MAP (\site. (a, inst.inst_id))
        (FLOOKUP s'.vs_allocas inst.inst_id)
    else if inst.inst_opcode = DALLOCA then NONE
    else out_prov HP H inst s'
End

Definition occurrence_step_def:
  occurrence_step a HP H inst s' =
    set_prov H inst.inst_outputs (occurrence_out a HP H inst s')
End

Definition occurrence_sites_step_def:
  occurrence_sites_step a B inst s' =
    if inst.inst_opcode = ALLOCA then
      case FLOOKUP s'.vs_allocas inst.inst_id of
        NONE => B
      | SOME site => B |+ ((a, inst.inst_id), site)
    else B
End

Inductive occ_frame_reachable:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     occ_frame_reachable vs0 ctx [] [] FEMPTY entry_taint fn inst s1
       1 0 [] FEMPTY [] FEMPTY)
[~next:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' fuel n a U B HP H.
     occ_frame_reachable vs0 ctx stk PG G tn fn inst s n a U B HP H /\
     active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     occ_frame_reachable vs0 ctx stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx)
       n a U (occurrence_sites_step a B inst s') HP
       (occurrence_step a HP H inst s'))
[~block:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' s1 fuel n a U B HP H.
     occ_frame_reachable vs0 ctx stk PG G tn fn inst s n a U B HP H /\
     active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     occ_frame_reachable vs0 ctx stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1
       n a U B HP (entry_prov fn s' H))
[~call:]
  (!vs0 ctx stk PG G tn caller inv s nm ops callee args cs s1 inst
      n a U B HP H.
     occ_frame_reachable vs0 ctx stk PG G tn caller inv s n a U B HP H /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     occ_frame_reachable vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
       (SUC n) n
       (<| of_owner := a; of_prov := H; of_params := HP |> :: U)
       B (MAP (op_prov H) ops) FEMPTY)
[~ret:]
  (!vs0 ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel
      n a u U B HP H.
     occ_frame_reachable vs0 ctx (f::stk) PG G tn fn rinst s
       n a (u::U) B HP H /\
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
       SOME s' /\
     active_inst f.cf_fn inst'
       (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     occ_frame_reachable vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
       n u.of_owner U (DRESTRICT B {id | FST id <> a}) u.of_params
       (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs))))
End

Theorem occ_frame_reachable_projection:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    frame_reachable vs C stk PG G tn fn inst s
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> rpt strip_tac >>
  metis_tac[frame_reachable_rules]
QED

(* Erasure includes definedness: a dangling identity is not an untracked value. *)
Definition occurrence_env_ok_def:
  occurrence_env_ok B owners H G <=>
    FDOM H = FDOM G /\
    !v id. FLOOKUP H v = SOME id ==>
      MEM (FST id) owners /\
      ?site. FLOOKUP B id = SOME site /\ FLOOKUP G v = SOME site
End

Definition occurrence_param_ok_def:
  occurrence_param_ok B owners p q <=>
    (p = NONE /\ q = NONE) \/
    ?id site. p = SOME id /\ q = SOME site /\
      MEM (FST id) owners /\ FLOOKUP B id = SOME site
End

Definition occurrence_allocas_ok_def:
  occurrence_allocas_ok B a s <=>
    !aid. FLOOKUP B (a,aid) = FLOOKUP s.vs_allocas aid
End

Definition occurrence_saved_ok_def:
  (occurrence_saved_ok B [] stk <=> stk = []) /\
  (occurrence_saved_ok B (u::U) stk <=>
    ?f fs. stk = f::fs /\
      occurrence_allocas_ok B u.of_owner f.cf_state /\
      occurrence_env_ok B (MAP (\u. u.of_owner) (u::U)) u.of_prov f.cf_prov /\
      LIST_REL (occurrence_param_ok B (MAP (\u. u.of_owner) (u::U)))
        u.of_params f.cf_params /\
      occurrence_saved_ok B U fs)
End

Definition occurrence_annotation_ok_def:
  occurrence_annotation_ok n a U B HP H stk PG G s <=>
    ALL_DISTINCT (a::MAP (\u. u.of_owner) U) /\
    EVERY (\owner. owner < n) (a::MAP (\u. u.of_owner) U) /\
    (!id. id IN FDOM B ==> MEM (FST id) (a::MAP (\u. u.of_owner) U)) /\
    occurrence_allocas_ok B a s /\
    occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\
    LIST_REL (occurrence_param_ok B (a::MAP (\u. u.of_owner) U)) HP PG /\
    occurrence_saved_ok B U stk
End

Theorem occ_frame_reachable_stack_length:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    LENGTH U = LENGTH stk
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> simp[]
QED

Theorem occ_frame_reachable_owner_fresh:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    ALL_DISTINCT (a::MAP (\u. u.of_owner) U) /\
    EVERY (\owner. owner < n) (a::MAP (\u. u.of_owner) U)
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> simp[] >>
  rpt strip_tac >> gvs[EVERY_MEM]
  >- (qpat_x_assum `!owner. _ ==> owner < _` (qspec_then `a` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!owner. _ ==> owner < _` (qspec_then `owner` mp_tac) >> simp[]
QED

Theorem occurrence_op_erasure:
  occurrence_env_ok B owners H G ==>
  occurrence_param_ok B owners (op_prov H op) (op_prov G op)
Proof
  strip_tac >> Cases_on `op` >>
  simp[op_prov_def, occurrence_param_ok_def] >>
  rename1 `FLOOKUP H v` >>
  Cases_on `FLOOKUP H v` >>
  gvs[occurrence_env_ok_def, occurrence_param_ok_def]
  >- gvs[FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem occurrence_first_erasure:
  !ops. occurrence_env_ok B owners H G ==>
    occurrence_param_ok B owners (first_prov H ops) (first_prov G ops)
Proof
  Induct >> simp[first_prov_def, occurrence_param_ok_def] >>
  rpt strip_tac >>
  drule occurrence_op_erasure >> disch_then (qspec_then `h` mp_tac) >>
  simp[occurrence_param_ok_def] >> rpt strip_tac >>
  gvs[occurrence_param_ok_def]
QED

Theorem occurrence_set_erasure:
  occurrence_env_ok B owners H G /\ occurrence_param_ok B owners p q ==>
  occurrence_env_ok B owners (set_prov H outs p) (set_prov G outs q)
Proof
  rpt strip_tac >>
  Cases_on `outs`
  >- (gvs[occurrence_param_ok_def, set_prov_def, occurrence_env_ok_def,
          FDOM_DRESTRICT, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `t` >>
  gvs[occurrence_param_ok_def, set_prov_def, occurrence_env_ok_def,
      FDOM_DRESTRICT, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP H key = SOME ident` >>
  qpat_x_assum `!v id. _` (qspecl_then [`key`, `ident`] mp_tac) >> simp[]
QED

(* The annotation records a history for every derivation, independent of
   whether its erasure satisfies the well-formedness interface. *)
Theorem frame_reachable_occurrence_lift:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    ?n a U B HP H.
      occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac
  >- (irule_at Any occ_frame_reachable_entry >> metis_tac[])
  >- (irule_at Any occ_frame_reachable_next >> metis_tac[])
  >- (irule_at Any occ_frame_reachable_block >> metis_tac[])
  >- (irule_at Any occ_frame_reachable_call >> metis_tac[])
  >> drule occ_frame_reachable_stack_length >>
  Cases_on `U` >> simp[] >> strip_tac >>
  irule_at Any occ_frame_reachable_ret >> metis_tac[]
QED

Theorem occurrence_phi_erasure:
  occurrence_env_ok B owners H G ==>
  occurrence_param_ok B owners (phi_prov prev H inst) (phi_prov prev G inst)
Proof
  strip_tac >> Cases_on `prev`
  >- simp[phi_prov_def, occurrence_param_ok_def] >>
  simp[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands`
  >- simp[occurrence_param_ok_def] >>
  simp[] >> irule occurrence_op_erasure >> simp[]
QED

Theorem occurrence_phis_erasure:
  !insts. occurrence_env_ok B owners H G ==>
    occurrence_env_ok B owners (phis_prov prev H insts) (phis_prov prev G insts)
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  irule occurrence_set_erasure >> simp[occurrence_phi_erasure]
QED

Theorem occurrence_entry_erasure:
  occurrence_env_ok B owners H G ==>
    occurrence_env_ok B owners (entry_prov fn s H) (entry_prov fn s G)
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[occurrence_phis_erasure]
QED

Theorem occurrence_out_nonalloca_erasure:
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  occurrence_env_ok B owners H G /\
  LIST_REL (occurrence_param_ok B owners) HP PG ==>
  occurrence_param_ok B owners
    (occurrence_out a HP H inst s') (out_prov PG G inst s')
Proof
  rpt strip_tac >>
  simp[occurrence_out_def, out_prov_def] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (simp[] >> Cases_on `inst.inst_operands`
      >- simp[occurrence_param_ok_def] >>
      Cases_on `h` >> simp[occurrence_param_ok_def] >>
      Cases_on `t` >> simp[occurrence_param_ok_def] >>
      gvs[LIST_REL_EL_EQN] >>
      rename1 `inst.inst_operands = [Lit idx]` >>
      IF_CASES_TAC
      >- (qpat_x_assum `!n. _` (qspec_then `w2n idx` mp_tac) >>
          simp[occurrence_param_ok_def]) >>
      simp[occurrence_param_ok_def]) >>
  simp[] >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN` >>
  simp[]
  >- (irule occurrence_first_erasure >> simp[]) >>
  simp[occurrence_param_ok_def]
QED

Theorem occurrence_param_transport:
  occurrence_param_ok B owners p q /\
  (!id site. MEM (FST id) owners /\ FLOOKUP B id = SOME site ==>
     MEM (FST id) owners' /\ FLOOKUP B' id = SOME site) ==>
  occurrence_param_ok B' owners' p q
Proof
  simp[occurrence_param_ok_def] >> metis_tac[]
QED

Theorem occurrence_env_transport:
  occurrence_env_ok B owners H G /\
  (!id site. MEM (FST id) owners /\ FLOOKUP B id = SOME site ==>
     MEM (FST id) owners' /\ FLOOKUP B' id = SOME site) ==>
  occurrence_env_ok B' owners' H G
Proof
  simp[occurrence_env_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!v id. _` (qspecl_then [`v`, `id`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem occurrence_params_transport:
  !HP PG. LIST_REL (occurrence_param_ok B owners) HP PG /\
  (!id site. MEM (FST id) owners /\ FLOOKUP B id = SOME site ==>
     MEM (FST id) owners' /\ FLOOKUP B' id = SOME site) ==>
  LIST_REL (occurrence_param_ok B' owners') HP PG
Proof
  Induct >> Cases_on `PG` >> simp[] >> rpt strip_tac >>
  metis_tac[occurrence_param_transport]
QED

Theorem occurrence_step_nonalloca_erasure:
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  occurrence_env_ok B owners H G /\
  LIST_REL (occurrence_param_ok B owners) HP PG ==>
  occurrence_env_ok B owners
    (occurrence_step a HP H inst s') (step_prov PG G inst s')
Proof
  strip_tac >> simp[occurrence_step_def, step_prov_def] >>
  irule occurrence_set_erasure >>
  simp[occurrence_out_nonalloca_erasure]
QED

Theorem occurrence_alloca_metadata:
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' ==>
  ?site. FLOOKUP s'.vs_allocas inst.inst_id = SOME site /\
    (!aid. FLOOKUP s'.vs_allocas aid =
      if aid = inst.inst_id then SOME site else FLOOKUP s.vs_allocas aid) /\
    (!old. FLOOKUP s.vs_allocas inst.inst_id = SOME old ==> site = old)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def,
      AllCaseEqs(), venomStateTheory.update_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `aid = inst.inst_id` >> simp[]
QED

Theorem occurrence_sites_step_preserves:
  occurrence_allocas_ok B a s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s' /\ FLOOKUP B id = SOME site ==>
  FLOOKUP (occurrence_sites_step a B inst s') id = SOME site
Proof
  strip_tac >> drule_all occurrence_alloca_metadata >> strip_tac >>
  simp[occurrence_sites_step_def, FLOOKUP_UPDATE] >>
  Cases_on `id = (a,inst.inst_id)` >> simp[] >> gvs[] >>
  gvs[occurrence_allocas_ok_def] >>
  qpat_x_assum `!aid. FLOOKUP B _ = _` (qspec_then `inst.inst_id` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem occurrence_sites_step_allocas:
  occurrence_allocas_ok B a s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s' ==>
  occurrence_allocas_ok (occurrence_sites_step a B inst s') a s'
Proof
  strip_tac >> drule_all occurrence_alloca_metadata >> strip_tac >>
  simp[occurrence_allocas_ok_def, occurrence_sites_step_def, FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `aid = inst.inst_id` >>
  gvs[occurrence_allocas_ok_def]
QED

Theorem occurrence_sites_step_other_owner:
  owner <> a ==>
  FLOOKUP (occurrence_sites_step a B inst s') (owner,aid) = FLOOKUP B (owner,aid)
Proof
  strip_tac >> simp[occurrence_sites_step_def] >>
  Cases_on `inst.inst_opcode = ALLOCA` >> simp[] >>
  Cases_on `FLOOKUP s'.vs_allocas inst.inst_id` >> simp[FLOOKUP_UPDATE]
QED

Theorem occurrence_step_alloca_erasure:
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  occurrence_allocas_ok B a s /\ occurrence_env_ok B owners H G /\
  MEM a owners ==>
  occurrence_env_ok (occurrence_sites_step a B inst s') owners
    (occurrence_step a HP H inst s') (step_prov PG G inst s')
Proof
  strip_tac >> simp[occurrence_step_def, step_prov_def] >>
  irule occurrence_set_erasure >> conj_tac
  >- (irule occurrence_env_transport >> qexistsl_tac [`B`, `owners`] >>
      simp[] >> rpt strip_tac >> irule occurrence_sites_step_preserves >>
      metis_tac[]) >>
  drule_all occurrence_alloca_metadata >> strip_tac >>
  simp[occurrence_out_def, out_prov_def, occurrence_param_ok_def,
       occurrence_sites_step_def, FLOOKUP_UPDATE]
QED

Theorem occurrence_saved_transport:
  !U stk. occurrence_saved_ok B U stk /\
    (!id. MEM (FST id) (MAP (\u. u.of_owner) U) ==>
      FLOOKUP B' id = FLOOKUP B id) ==>
    occurrence_saved_ok B' U stk
Proof
  Induct >> simp[occurrence_saved_ok_def] >> rpt strip_tac >> gvs[] >>
  simp[occurrence_saved_ok_def] >> rpt conj_tac
  >- (gvs[occurrence_allocas_ok_def] >> gen_tac >>
      qpat_x_assum `!id. _` (qspec_then `(h.of_owner,aid)` mp_tac) >> simp[])
  >- (irule occurrence_env_transport >> qexistsl_tac [`B`, `h.of_owner::MAP (\u. u.of_owner) U`] >>
      simp[] >> metis_tac[])
  >- (irule occurrence_params_transport >> qexistsl_tac [`B`, `h.of_owner::MAP (\u. u.of_owner) U`] >>
      simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem occurrence_annotation_next:
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
  step_inst fuel C inst s = OK s' ==>
  occurrence_annotation_ok n a U (occurrence_sites_step a B inst s') HP
    (occurrence_step a HP H inst s') stk PG (step_prov PG G inst s')
    (s' with vs_inst_idx := idx)
Proof
  strip_tac >>
  `occurrence_allocas_ok B a s` by gvs[occurrence_annotation_ok_def] >>
  `!id site. FLOOKUP B id = SOME site ==>
     FLOOKUP (occurrence_sites_step a B inst s') id = SOME site` by
    (Cases_on `inst.inst_opcode = ALLOCA`
     >- (rpt strip_tac >> irule occurrence_sites_step_preserves >> metis_tac[]) >>
     simp[occurrence_sites_step_def]) >>
  `occurrence_allocas_ok (occurrence_sites_step a B inst s') a s'` by
    (Cases_on `inst.inst_opcode = ALLOCA`
     >- (irule occurrence_sites_step_allocas >> metis_tac[]) >>
     `s'.vs_allocas = s.vs_allocas` by
       (irule step_inst_base_preserves_allocas >> qexists_tac `inst` >>
        gvs[step_inst_non_invoke]) >>
     gvs[occurrence_sites_step_def, occurrence_allocas_ok_def]) >>
  gvs[occurrence_annotation_ok_def] >>
  rpt conj_tac
  >- (simp[occurrence_sites_step_def] >>
      Cases_on `inst.inst_opcode = ALLOCA` >> simp[] >>
      Cases_on `FLOOKUP s'.vs_allocas inst.inst_id` >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >- gvs[occurrence_allocas_ok_def]
  >- (Cases_on `inst.inst_opcode = ALLOCA`
      >- (irule occurrence_step_alloca_erasure >> simp[] >> metis_tac[]) >>
      simp[occurrence_sites_step_def] >>
      irule occurrence_step_nonalloca_erasure >> simp[])
  >- (irule occurrence_params_transport >>
      qexistsl_tac [`B`, `a::MAP (\u. u.of_owner) U`] >> simp[]) >>
  irule occurrence_saved_transport >> qexists_tac `B` >> simp[] >>
  rpt strip_tac >> PairCases_on `id` >>
  irule occurrence_sites_step_other_owner >> gvs[] >> metis_tac[]
QED

Theorem occurrence_enters_block_allocas[local]:
  enters_block fn s s1 ==> s1.vs_allocas = s.vs_allocas
Proof
  rw[contextCodegenRelTheory.enters_block_def] >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem occurrence_annotation_block:
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK s' /\
  enters_block fn s' s1 ==>
  occurrence_annotation_ok n a U B HP (entry_prov fn s' H)
    stk PG (entry_prov fn s' G) s1
Proof
  strip_tac >>
  `inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    (irule step_inst_base_preserves_allocas >> qexists_tac `inst` >>
     gvs[step_inst_non_invoke]) >>
  drule occurrence_enters_block_allocas >> strip_tac >>
  gvs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  irule occurrence_entry_erasure >> simp[]
QED

Theorem occurrence_annotation_call:
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  setup_callee callee args s = SOME cs /\ enters_block callee cs s1 ==>
  occurrence_annotation_ok (SUC n) n
    (<| of_owner := a; of_prov := H; of_params := HP |> :: U)
    B (MAP (op_prov H) ops) FEMPTY
    (<| cf_fn := caller; cf_inst := call_inst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)
    (MAP (op_prov G) ops) FEMPTY s1
Proof
  strip_tac >>
  `cs.vs_allocas = FEMPTY` by gvs[setup_callee_def, AllCaseEqs()] >>
  `s1.vs_allocas = FEMPTY` by metis_tac[occurrence_enters_block_allocas] >>
  `!owner. MEM owner (a::MAP (\u. u.of_owner) U) ==> owner < n` by
    (gvs[occurrence_annotation_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `~MEM n (a::MAP (\u. u.of_owner) U)` by
    (strip_tac >> qpat_x_assum `!owner. _ ==> owner < _` (qspec_then `n` mp_tac) >> simp[]) >>
  `!aid. FLOOKUP B (n,aid) = NONE` by
    (gvs[occurrence_annotation_ok_def, FLOOKUP_DEF] >> rpt strip_tac >>
     CCONTR_TAC >> gvs[] >>
     qpat_x_assum `!id. _` (qspec_then `(n,aid)` mp_tac) >> simp[]) >>
  gvs[occurrence_annotation_ok_def, occurrence_allocas_ok_def,
      occurrence_saved_ok_def, occurrence_env_ok_def] >>
  rpt conj_tac
  >- (qpat_x_assum `!owner. _ ==> owner < _` (qspec_then `a` mp_tac) >> simp[])
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!owner. _ ==> owner < _` (qspec_then `owner` mp_tac) >> simp[])
  >- (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
      irule occurrence_param_transport >>
      qexistsl_tac [`B`, `a::MAP (\u. u.of_owner) U`] >>
      conj_tac >- simp[] >>
      irule occurrence_op_erasure >> simp[occurrence_env_ok_def] >>
      rpt strip_tac >>
      qpat_x_assum `!v id. FLOOKUP H v = SOME id ==> _`
        (qspecl_then [`v`, `id`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!v id. FLOOKUP H v = SOME id ==> _`
    (qspecl_then [`v`, `id`] mp_tac) >> simp[]
QED

Theorem occurrence_annotation_return:
  occurrence_annotation_ok n a (u::U) B HP H (f::stk) PG G s /\
  bind_outputs f.cf_inst.inst_outputs vals
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' ==>
  occurrence_annotation_ok n u.of_owner U (DRESTRICT B {id | FST id <> a})
    u.of_params (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
    stk f.cf_params (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (s' with vs_inst_idx := idx)
Proof
  strip_tac >>
  `s'.vs_allocas = f.cf_state.vs_allocas` by
    (qspec_then `\s. s.vs_allocas` mp_tac
       venomInstProofs1Theory.bind_outputs_preserves >>
     simp[venomStateTheory.update_var_def] >> disch_then drule >>
     simp[merge_callee_state_def]) >>
  `~MEM a (MAP (\u. u.of_owner) (u::U))` by
    gvs[occurrence_annotation_ok_def] >>
  `occurrence_saved_ok (DRESTRICT B {id | FST id <> a}) (u::U) (f::stk)` by
    (irule occurrence_saved_transport >> qexists_tac `B` >>
     conj_tac
     >- (simp[FLOOKUP_DRESTRICT] >> rpt strip_tac >> gvs[] >>
         IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
     gvs[occurrence_annotation_ok_def]) >>
  gvs[occurrence_annotation_ok_def, occurrence_saved_ok_def,
      occurrence_allocas_ok_def, FDOM_DRESTRICT] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id. id IN FDOM B ==> _` (qspec_then `id` mp_tac) >> simp[]) >>
  qpat_x_assum `occurrence_env_ok (DRESTRICT B _) _ u.of_prov f.cf_prov` mp_tac >>
  simp[occurrence_env_ok_def, FDOM_DRESTRICT, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!v id. FLOOKUP u.of_prov v = SOME id ==> _`
    (qspecl_then [`v`, `id`] mp_tac) >> simp[]
QED

Theorem occ_frame_reachable_annotation:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    MEM fn C.ctx_functions /\ EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
    (vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C ==>
     occurrence_annotation_ok n a U B HP H stk PG G s)
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume occ_frame_reachable_annotation[entry]:
  rpt gen_tac >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  simp[] >> strip_tac >>
  drule occurrence_enters_block_allocas >>
  simp[occurrence_annotation_ok_def, occurrence_allocas_ok_def,
       occurrence_env_ok_def, occurrence_saved_ok_def]
QED

Resume occ_frame_reachable_annotation[next]:
  rpt gen_tac >> strip_tac >> gvs[] >> strip_tac >>
  `inst.inst_opcode <> DALLOCA` by
    (gvs[ctx_has_dalloca_def, EXISTS_MEM] >>
     `MEM inst (fn_insts fn)` by
       (qpat_x_assum `active_inst fn inst s` mp_tac >>
        rw[contextCodegenRelTheory.active_inst_def, venomInstTheory.fn_insts_def,
           o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
     metis_tac[]) >>
  irule occurrence_annotation_next >> metis_tac[]
QED

Resume occ_frame_reachable_annotation[block]:
  rpt gen_tac >> strip_tac >> gvs[] >> strip_tac >>
  irule occurrence_annotation_block >> metis_tac[]
QED

Resume occ_frame_reachable_annotation[call]:
  rpt gen_tac >> strip_tac >>
  `MEM fn' C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  simp[] >> strip_tac >>
  irule occurrence_annotation_call >> metis_tac[]
QED

Resume occ_frame_reachable_annotation[ret]:
  rpt gen_tac >> strip_tac >> gvs[] >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:string``] occurrence_annotation_return) >>
  metis_tac[]
QED

Finalise occ_frame_reachable_annotation

Theorem frame_reachable_occurrence_annotation:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  ?n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
    occurrence_annotation_ok n a U B HP H stk PG G s
Proof
  strip_tac >> drule frame_reachable_occurrence_lift >> strip_tac >>
  drule occ_frame_reachable_annotation >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
