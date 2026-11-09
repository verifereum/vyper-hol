(* Syntax origin and identity exclusion at occurrence constructors. *)
Theory occurrenceOrigin
Ancestors
  o1LowerDloadOccurrence o1LowerDloadClosure o1FrameLockstep
  ptrDiscipline o1LowerDloadGhost finite_map list pred_set

Theorem occurrence_out_identity_cases:
  occurrence_out a HP H inst s = SOME id ==>
  (inst.inst_opcode = ALLOCA /\ id = (a,inst.inst_id)) \/
  MEM (SOME id) HP \/ ?v. FLOOKUP H v = SOME id
Proof
  simp[occurrence_out_def, out_prov_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]) >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
      metis_tac[MEM_EL]) >>
  IF_CASES_TAC >> simp[] >> metis_tac[first_prov_origin]
QED

Theorem occurrence_step_identity_absent:
  (!v. FLOOKUP H v <> SOME id) /\ ~MEM (SOME id) HP /\
  (inst.inst_opcode = ALLOCA ==> id <> (a,inst.inst_id)) ==>
  !v. FLOOKUP (occurrence_step a HP H inst s) v <> SOME id
Proof
  strip_tac >> simp[occurrence_step_def, FLOOKUP_set_prov] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[occurrence_out_identity_cases]
QED

Theorem phi_prov_identity_origin:
  phi_prov prev H inst = SOME id ==> ?v. FLOOKUP H v = SOME id
Proof
  Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  Cases_on `x'` >> simp[op_prov_def] >> metis_tac[]
QED

Theorem phis_prov_identity_absent:
  !insts. (!v. FLOOKUP H v <> SOME id) ==>
  !v. FLOOKUP (phis_prov prev H insts) v <> SOME id
Proof
  Induct >> simp[phis_prov_def] >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  simp[FLOOKUP_set_prov] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[phi_prov_identity_origin]
QED

Theorem entry_prov_identity_absent:
  (!v. FLOOKUP H v <> SOME id) ==>
  !v. FLOOKUP (entry_prov fn s H) v <> SOME id
Proof
  simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[phis_prov_identity_absent]
QED

Theorem occurrence_call_identity_absent:
  (!v. FLOOKUP H v <> SOME id) ==>
  ~MEM (SOME id) (MAP (op_prov H) ops)
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  Cases_on `y` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem occurrence_return_identity_absent:
  (!v. FLOOKUP H v <> SOME id) ==>
  !v. FLOOKUP (DRESTRICT H (COMPL (set outs))) v <> SOME id
Proof
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Definition occurrence_syntax_origin_def:
  occurrence_syntax_origin fn a H <=>
    !v aid. FLOOKUP H v = SOME (a,aid) ==>
      ?ai r. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
        ai.inst_id = aid /\ MEM r ai.inst_outputs /\
        v IN pointer_derived_vars fn {r}
End

Theorem occurrence_out_own_source:
  occurrence_out a HP H inst s = SOME (a,aid) /\
  ~MEM (SOME (a,aid)) HP ==>
  (inst.inst_opcode = ALLOCA /\ aid = inst.inst_id) \/
  (is_pointer_preserving_op inst.inst_opcode /\
   ?v. MEM (Var v) inst.inst_operands /\ FLOOKUP H v = SOME (a,aid))
Proof
  simp[occurrence_out_def, out_prov_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]) >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
      metis_tac[MEM_EL]) >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  drule first_prov_origin >> strip_tac >>
  gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem occurrence_step_syntax_origin:
  occurrence_syntax_origin fn a H /\ MEM inst (fn_insts fn) /\
  (!aid. ~MEM (SOME (a,aid)) HP) ==>
  occurrence_syntax_origin fn a (occurrence_step a HP H inst s)
Proof
  simp[occurrence_syntax_origin_def] >> strip_tac >>
  simp[occurrence_step_def, FLOOKUP_set_prov] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      drule occurrence_out_own_source >> simp[] >> strip_tac
      >- (qexistsl_tac [`inst`,`v`] >>
          simp[mem2varBlockSimHelpersTheory.roots_in_pointer_derived_vars] >> gvs[]) >>
      first_x_assum drule >> strip_tac >>
      qexistsl_tac [`ai`,`r`] >> simp[] >>
      irule pointer_derived_vars_forward >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem phi_prov_syntax_origin:
  occurrence_syntax_origin fn a H /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  phi_prov prev H inst = SOME (a,aid) ==>
  ?ai r. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
    ai.inst_id = aid /\ MEM r ai.inst_outputs /\
    v IN pointer_derived_vars fn {r}
Proof
  simp[occurrence_syntax_origin_def, phi_prov_def] >>
  Cases_on `prev` >> simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  Cases_on `x'` >> simp[op_prov_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ai`,`r`] >> simp[] >>
  irule pointer_derived_vars_forward >>
  simp[pointerConfinedDefsTheory.is_pointer_preserving_op_def] >>
  qexistsl_tac [`inst`,`s`] >>
  simp[pointerConfinedDefsTheory.is_pointer_preserving_op_def] >>
  metis_tac[execEquivParamBaseTheory.resolve_phi_MEM]
QED

Theorem phis_prov_syntax_origin:
  !insts. occurrence_syntax_origin fn a H /\
  EVERY (\i. MEM i (fn_insts fn)) insts ==>
  occurrence_syntax_origin fn a (phis_prov prev H insts)
Proof
  Induct >- simp[phis_prov_def] >>
  gen_tac >> strip_tac >> fs[] >>
  simp[Once phis_prov_def] >> IF_CASES_TAC >> simp[] >>
  fs[occurrence_syntax_origin_def] >>
  simp[FLOOKUP_set_prov] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> irule phi_prov_syntax_origin >>
      simp[occurrence_syntax_origin_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem entry_prov_syntax_origin:
  occurrence_syntax_origin fn a H ==>
  occurrence_syntax_origin fn a (entry_prov fn s H)
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule phis_prov_syntax_origin >> simp[EVERY_MEM] >>
  rpt strip_tac >>
  metis_tac[livenessTransferProofsTheory.lookup_block_mem,
            venomInstTheory.fn_insts_def,
            o1PassContractTheory.fn_insts_blocks_MEM]
QED

Theorem occurrence_return_syntax_origin:
  occurrence_syntax_origin fn a H ==>
  occurrence_syntax_origin fn a (DRESTRICT H (COMPL (set outs)))
Proof
  simp[occurrence_syntax_origin_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem occurrence_syntax_origin_empty:
  occurrence_syntax_origin fn a FEMPTY
Proof
  simp[occurrence_syntax_origin_def]
QED

Definition occurrence_origin_certificate_def:
  occurrence_origin_certificate fn a H HP U stk <=>
    occurrence_syntax_origin fn a H /\
    (!aid. ~MEM (SOME (a,aid)) HP) /\
    LENGTH U = LENGTH stk /\
    (!j. j < LENGTH stk ==>
      occurrence_syntax_origin (EL j stk).cf_fn (EL j U).of_owner
        (EL j U).of_prov /\
      (!aid. ~MEM (SOME ((EL j U).of_owner,aid)) (EL j U).of_params))
End

Theorem occurrence_origin_certificate_empty:
  occurrence_origin_certificate fn a FEMPTY [] [] []
Proof
  simp[occurrence_origin_certificate_def, occurrence_syntax_origin_empty]
QED

Theorem occurrence_origin_certificate_next:
  occurrence_origin_certificate fn a H HP U stk /\ MEM inst (fn_insts fn) ==>
  occurrence_origin_certificate fn a (occurrence_step a HP H inst s) HP U stk
Proof
  simp[occurrence_origin_certificate_def] >> rpt strip_tac >>
  irule occurrence_step_syntax_origin >> simp[]
QED

Theorem occurrence_origin_certificate_block:
  occurrence_origin_certificate fn a H HP U stk ==>
  occurrence_origin_certificate fn a (entry_prov fn s H) HP U stk
Proof
  simp[occurrence_origin_certificate_def] >>
  metis_tac[entry_prov_syntax_origin]
QED

Theorem occurrence_origin_certificate_push:
  occurrence_origin_certificate fn a H HP U stk /\
  (!aid. ~MEM (SOME (c,aid)) params) ==>
  occurrence_origin_certificate callee c FEMPTY params
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U)
    (<|cf_fn := fn; cf_inst := call_inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tv|> :: stk)
Proof
  simp[occurrence_origin_certificate_def, occurrence_syntax_origin_empty] >>
  strip_tac >> Cases >> simp[]
QED

Theorem occurrence_origin_certificate_pop:
  occurrence_origin_certificate fn a H HP (u::U) (f::stk) ==>
  occurrence_origin_certificate f.cf_fn u.of_owner
    (DRESTRICT u.of_prov (COMPL (set outs))) u.of_params U stk
Proof
  rewrite_tac[occurrence_origin_certificate_def] >> strip_tac >>
  fs[] >>
  qpat_assum `!j. j < SUC (LENGTH stk) ==> _` (qspec_then `0` assume_tac) >>
  fs[] >>
  conj_tac >- (irule occurrence_return_syntax_origin >> simp[]) >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < SUC (LENGTH stk) ==> _` (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem occurrence_annotation_fresh_arguments:
  occurrence_annotation_ok n a U B HP H stk PG G s ==>
  !aid. ~MEM (SOME (n,aid)) (MAP (op_prov H) ops)
Proof
  simp[occurrence_annotation_ok_def] >> strip_tac >> gen_tac >>
  `!v. FLOOKUP H v <> SOME (n,aid)` by
    (fs[occurrence_env_ok_def, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> metis_tac[arithmeticTheory.LESS_ANTISYM]) >>
  irule occurrence_call_identity_absent >> simp[]
QED

Theorem occ_frame_reachable_origin_certificate:
  !vs C stk PG G tn fn inst s n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
    vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C ==>
    occurrence_origin_certificate fn a H HP U stk
Proof
  ho_match_mp_tac occ_frame_reachable_strongind >> rpt conj_tac
  >- (rpt strip_tac >> simp[occurrence_origin_certificate_empty])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume occ_frame_reachable_origin_certificate[next]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  irule occurrence_origin_certificate_next >> simp[] >>
  irule allocaFrontierBoundTheory.active_inst_mem_fn_insts >>
  qexists_tac `s` >> simp[]
QED

Resume occ_frame_reachable_origin_certificate[block]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule occurrence_origin_certificate_block >> simp[]
QED

Resume occ_frame_reachable_origin_certificate[call]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule occ_frame_reachable_annotation >> simp[] >> strip_tac >>
  drule occurrence_annotation_fresh_arguments >> strip_tac >>
  simp[occurrence_origin_certificate_push]
QED

Resume occ_frame_reachable_origin_certificate[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule occurrence_origin_certificate_pop >> simp[]
QED

Finalise occ_frame_reachable_origin_certificate

Theorem occurrence_origin_certificate_current:
  occurrence_origin_certificate fn a H HP U stk ==>
  occurrence_syntax_origin fn a H
Proof
  simp[occurrence_origin_certificate_def]
QED

Theorem occurrence_origin_certificate_params:
  occurrence_origin_certificate fn a H HP U stk ==>
  !aid. ~MEM (SOME (a,aid)) HP
Proof
  simp[occurrence_origin_certificate_def]
QED

Theorem occurrence_origin_certificate_saved:
  occurrence_origin_certificate fn a H HP U stk /\ j < LENGTH stk ==>
  occurrence_syntax_origin (EL j stk).cf_fn (EL j U).of_owner (EL j U).of_prov /\
  (!aid. ~MEM (SOME ((EL j U).of_owner,aid)) (EL j U).of_params)
Proof
  simp[occurrence_origin_certificate_def]
QED

Theorem occurrence_origin_certificate_length:
  occurrence_origin_certificate fn a H HP U stk ==> LENGTH U = LENGTH stk
Proof
  simp[occurrence_origin_certificate_def]
QED

(* j selects the owning suspended frame. Only its strictly younger frames
   must exclude id; the selected owner's environment is intentionally free. *)
Definition occurrence_suffix_absent_def:
  occurrence_suffix_absent id j H HP U <=>
    j < LENGTH U /\
    (!v. FLOOKUP H v <> SOME id) /\ ~MEM (SOME id) HP /\
    (!i. i < j ==>
      (!v. FLOOKUP (EL i U).of_prov v <> SOME id) /\
      ~MEM (SOME id) (EL i U).of_params)
End

Theorem occurrence_suffix_absent_start:
  ~MEM (SOME id) params ==>
  occurrence_suffix_absent id 0 FEMPTY params (u::U)
Proof
  simp[occurrence_suffix_absent_def]
QED

Theorem occurrence_suffix_absent_next:
  occurrence_suffix_absent id j H HP U /\
  (inst.inst_opcode = ALLOCA ==> id <> (a,inst.inst_id)) ==>
  occurrence_suffix_absent id j (occurrence_step a HP H inst s) HP U
Proof
  simp[occurrence_suffix_absent_def] >>
  metis_tac[occurrence_step_identity_absent]
QED

Theorem occurrence_suffix_absent_block:
  occurrence_suffix_absent id j H HP U ==>
  occurrence_suffix_absent id j (entry_prov fn s H) HP U
Proof
  simp[occurrence_suffix_absent_def] >>
  metis_tac[entry_prov_identity_absent]
QED

Theorem occurrence_suffix_absent_push:
  occurrence_suffix_absent id j H HP U ==>
  occurrence_suffix_absent id (SUC j) FEMPTY (MAP (op_prov H) ops)
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U)
Proof
  simp[occurrence_suffix_absent_def] >> strip_tac >>
  conj_tac >- (irule occurrence_call_identity_absent >> simp[]) >>
  Cases >> simp[]
QED

Theorem occurrence_suffix_absent_pop:
  occurrence_suffix_absent id (SUC j) H HP (u::U) ==>
  occurrence_suffix_absent id j
    (DRESTRICT u.of_prov (COMPL (set outs))) u.of_params U
Proof
  simp[occurrence_suffix_absent_def] >> strip_tac >>
  first_assum (qspec_then `0` assume_tac) >> fs[] >>
  conj_tac >- (irule occurrence_return_identity_absent >> simp[]) >>
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem occurrence_syntax_origin_planned_root:
  occurrence_syntax_origin fn a H /\ fn_inst_ids_distinct fn /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\ FLOOKUP H v = SOME (a,ai.inst_id) ==>
  v IN pointer_derived_vars fn {root}
Proof
  simp[occurrence_syntax_origin_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all venomWfPropsTheory.fn_inst_ids_distinct_inj >>
  strip_tac >> gvs[]
QED
