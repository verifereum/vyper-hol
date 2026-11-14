(* Source-only event histories.  In particular no clause below is a memory
   exclusion, a read equality, or a target-state reachability assumption. *)
Theory readonlyInvokeCopyFwdProtection
Ancestors
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdReadonlyReach
  readonlyInvokeCopyFwdRel occurrenceGeometry list finite_map pred_set

Datatype:
  ricf_protection_event = <|
    rpe_event : ricf_forward_event;
    rpe_block : basic_block;
    rpe_fn : ir_function;
    rpe_before : venom_state;
    rpe_after : venom_state;
    rpe_owner : num;
    rpe_dst : num # num;
    rpe_src : num # num;
    rpe_db : num;
    rpe_sb : num;
    rpe_size : num
  |>
End

(* A visit is an execution prefix, not a block label.  Inner activations may
   cross blocks, but the owning activation may not cross its terminator.
   Consequently an old suffix witness cannot survive an owner backedge. *)
Inductive ricf_visit_prefix:
[~start:]
  (!C fn PG G tn s.
    ricf_visit_prefix C fn PG G tn s [] PG G tn fn s)
[~next:]
  (!C root RPG RG RT rs pre PG G tn fn s inst s' fuel.
    ricf_visit_prefix C root RPG RG RT rs pre PG G tn fn s /\
    active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' ==>
    ricf_visit_prefix C root RPG RG RT rs pre PG
      (step_prov PG G inst s') (step_taint inst s s' tn) fn
      (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!C root RPG RG RT rs f pre PG G tn fn s inst s' s1 fuel.
    ricf_visit_prefix C root RPG RG RT rs (f::pre) PG G tn fn s /\
    active_inst fn inst s /\ is_terminator inst.inst_opcode /\
    step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
    enters_block fn s' s1 ==>
    ricf_visit_prefix C root RPG RG RT rs (f::pre) PG
      (entry_prov fn s' G) (entry_taint_vars fn s' tn) fn s1)
[~call:]
  (!C root RPG RG RT rs pre PG G tn caller s inv nm ops callee args cs s1.
    ricf_visit_prefix C root RPG RG RT rs pre PG G tn caller s /\
    active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 ==>
    ricf_visit_prefix C root RPG RG RT rs
      (<| cf_fn := caller; cf_inst := inv; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: pre)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1)
[~ret:]
  (!C root RPG RG RT rs f pre PG G tn fn s inst ret se s' fuel.
    ricf_visit_prefix C root RPG RG RT rs (f::pre) PG G tn fn s /\
    active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' ==>
    ricf_visit_prefix C root RPG RG RT rs pre f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

Definition ricf_protection_triple_def:
  ricf_protection_triple p = (p.rpe_db,p.rpe_sb,p.rpe_size)
End

(* The original pre-transform block and static roots remain in the event.
   Occurrence provenance at the executed source copy supplies the endpoint
   keys; numeric equality of addresses is deliberately not an inverse lookup. *)
Definition ricf_protection_origin_def:
  ricf_protection_origin vs C p stk PG G tn <=>
    ricf_event_ok p.rpe_event p.rpe_block /\
    p.rpe_block.bb_label = p.rpe_before.vs_current_bb /\
    FST p.rpe_dst = p.rpe_owner /\ FST p.rpe_src = p.rpe_owner /\
    ?n U B HP H inst dst src szop dr sr.
      inst = ricf_event_copy p.rpe_event p.rpe_block /\
      ricf_event_roots p.rpe_event p.rpe_block = SOME (dr,sr,szop) /\
      inst.inst_operands = [Var dst;src;szop] /\
      occ_frame_reachable vs C stk PG G tn p.rpe_fn inst p.rpe_before
        n p.rpe_owner U B HP H /\
      op_prov H (Var dst) = SOME p.rpe_dst /\
      op_prov H src = SOME p.rpe_src /\
      op_prov H (Var dr) = SOME p.rpe_dst /\
      op_prov H sr = SOME p.rpe_src /\
      FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
      FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
      eval_operands inst.inst_operands p.rpe_before =
        SOME [n2w p.rpe_db;n2w p.rpe_sb;n2w p.rpe_size] /\
      p.rpe_before.vs_inst_idx = p.rpe_event.rfe_index /\
      ?fuel. step_inst fuel C inst p.rpe_before = OK p.rpe_after
End

Definition ricf_protection_cursor_def:
  ricf_protection_cursor vs C p pre PG G tn fn s <=>
    ?stk RPG RG RT.
      ricf_protection_origin vs C p stk RPG RG RT /\
      ricf_visit_prefix C p.rpe_fn RPG
        (step_prov RPG RG (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
        (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
          p.rpe_before p.rpe_after RT)
        (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
        pre PG G tn fn s
End

(* Both endpoints have the SAME activation anchor and tail.  This matters:
   protecting just the forwarded destination does not protect its source. *)
Definition ricf_protection_inherited_def:
  ricf_protection_inherited vs C RO p stk PG G tn fn inst s <=>
    ?anchor tail pre atn.
      stk = pre ++ anchor::tail /\ atn.t_var = anchor.cf_tvar /\
      ricf_protection_cursor vs C p [] anchor.cf_params anchor.cf_prov
        atn anchor.cf_fn anchor.cf_state /\
      readonly_call_reachable vs C RO anchor tail (SND p.rpe_dst)
        p.rpe_db p.rpe_size pre PG G tn fn inst s /\
      readonly_call_reachable vs C RO anchor tail (SND p.rpe_src)
        p.rpe_sb p.rpe_size pre PG G tn fn inst s
End

Datatype:
  ricf_protection_phase = RPE_Current | RPE_SuspendedCurrent num |
    RPE_Inherited | RPE_SuspendedInherited num
End

Definition ricf_protection_record_def:
  ricf_protection_record vs C RO a U B stk PG G tn fn inst s rec <=>
    let (p,phase) = rec in
      FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
      FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
      0 < p.rpe_size /\
      case phase of
        RPE_Current => a = p.rpe_owner /\
          ricf_protection_cursor vs C p [] PG G tn fn s
      | RPE_SuspendedCurrent j => j < LENGTH stk /\ j < LENGTH U /\
          (EL j U).of_owner = p.rpe_owner /\
          (?saved_tn. saved_tn.t_var = (EL j stk).cf_tvar /\
            ricf_protection_cursor vs C p [] (EL j stk).cf_params
              (EL j stk).cf_prov saved_tn (EL j stk).cf_fn (EL j stk).cf_state)
      | RPE_Inherited => ricf_protection_inherited vs C RO p stk PG G tn fn inst s
      | RPE_SuspendedInherited j => j < LENGTH stk /\
          (?saved_tn. saved_tn.t_var = (EL j stk).cf_tvar /\
            ricf_protection_inherited vs C RO p (DROP (SUC j) stk)
              (EL j stk).cf_params (EL j stk).cf_prov saved_tn
              (EL j stk).cf_fn (EL j stk).cf_inst (EL j stk).cf_state)
End

Definition ricf_source_protection_def:
  ricf_source_protection vs C RO lo n a U B HP H stk PG G tn fn inst s records <=>
    occurrence_annotation_ok n a U B HP H stk PG G s /\
    occurrence_natural_geometry lo a U B stk s /\
    EVERY (ricf_protection_record vs C RO a U B stk PG G tn fn inst s) records
End

(* Alignment is exact and separate from validity.  Zero ranges need no
   history.  Frame lists retain their lengths even when records retire. *)
Definition ricf_protection_ranges_def:
  ricf_protection_ranges phase records =
    {tr | ?p. MEM (p,phase) records /\ tr = ricf_protection_triple p}
End

Definition ricf_protection_alignment_def:
  ricf_protection_alignment sites maps stk cur curs records <=>
    LENGTH maps = LENGTH stk /\ LENGTH curs = LENGTH stk /\
    { (d,b,z) | (d,b,z) IN cur /\ 0 < z } =
      ricf_protection_ranges RPE_Current records /\
    { (d,b,z) | (d,b,z) IN ricf_site_triples sites /\ 0 < z } =
      ricf_protection_ranges RPE_Inherited records /\
    (!j. j < LENGTH stk ==>
      { (d,b,z) | (d,b,z) IN EL j curs /\ 0 < z } =
        ricf_protection_ranges (RPE_SuspendedCurrent j) records /\
      { (d,b,z) | (d,b,z) IN ricf_site_triples (EL j maps) /\ 0 < z } =
        ricf_protection_ranges (RPE_SuspendedInherited j) records)
End

Theorem ricf_source_protection_empty_entry:
  occurrence_annotation_ok n a [] FEMPTY [] FEMPTY [] PG G s ==>
  ricf_source_protection vs C RO lo n a [] FEMPTY [] FEMPTY
    [] PG G tn fn inst s [] /\
  ricf_protection_alignment FEMPTY [] [] {} [] []
Proof
  simp[ricf_source_protection_def, occurrence_natural_geometry_empty,
       ricf_protection_alignment_def, ricf_site_triples_def,
       ricf_protection_ranges_def, EXTENSION]
QED

Theorem ricf_source_protection_retire:
  ricf_source_protection vs C RO lo n a U B HP H stk PG G tn fn inst s records ==>
  ricf_source_protection vs C RO lo n a U B HP H stk PG G tn fn inst s
    (FILTER keep records)
Proof
  simp[ricf_source_protection_def, EVERY_FILTER, EVERY_MEM] >> metis_tac[]
QED

Theorem ricf_protection_retire_ranges:
  ricf_protection_ranges phase (FILTER keep records) =
    {tr | ?p. MEM (p,phase) records /\ keep (p,phase) /\
               tr = ricf_protection_triple p}
Proof
  simp[ricf_protection_ranges_def, MEM_FILTER, EXTENSION] >> metis_tac[]
QED

(* Restriction acts on lookup VALUES, not just the numeric provenance key. *)
Definition ricf_protection_prune_sites_def:
  ricf_protection_prune_sites allowed sites =
    DRESTRICT sites {id | ?tr. FLOOKUP sites id = SOME tr /\ tr IN allowed}
End

Theorem ricf_protection_alignment_retire:
  ricf_protection_alignment sites maps stk cur curs records ==> ricf_protection_alignment
  (ricf_protection_prune_sites (ricf_protection_ranges RPE_Inherited (FILTER keep records))
  sites) (GENLIST (\j. ricf_protection_prune_sites (ricf_protection_ranges
  (RPE_SuspendedInherited j) (FILTER keep records)) (EL j maps)) (LENGTH stk)) stk (cur INTER
  ricf_protection_ranges RPE_Current (FILTER keep records)) (GENLIST (\j. EL j curs INTER
  ricf_protection_ranges (RPE_SuspendedCurrent j) (FILTER keep records)) (LENGTH stk)) (FILTER
  keep records)
Proof
  simp[LET_THM, ricf_protection_alignment_def,
       ricf_protection_prune_sites_def, ricf_site_triples_def,
       FLOOKUP_DRESTRICT, EL_GENLIST, ricf_protection_ranges_def,
       MEM_FILTER, EXTENSION] >>
  rpt strip_tac >> PairCases_on `x` >> gvs[pairTheory.FORALL_PROD] >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Constructor boundary tests: these do not purport to preserve the whole
   certificate, whose occurrence and alignment channels are independent. *)
Theorem ricf_protection_cursor_activate:
  ricf_protection_origin vs C p stk PG G tn ==>
  ricf_protection_cursor vs C p [] PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
Proof
  simp[ricf_protection_cursor_def] >>
  metis_tac[ricf_visit_prefix_start]
QED

Theorem ricf_protection_cursor_next:
  ricf_protection_cursor vs C p pre PG G tn fn s /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' ==>
  ricf_protection_cursor vs C p pre PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[ricf_protection_cursor_def] >>
  metis_tac[ricf_visit_prefix_next]
QED

Definition ricf_visit_owner_state_def:
  ricf_visit_owner_state pre s =
    if pre = [] then s else (LAST pre).cf_state
End

Theorem ricf_visit_prefix_owner_location:
  !C root RPG RG RT rs pre PG G tn fn s.
    ricf_visit_prefix C root RPG RG RT rs pre PG G tn fn s ==>
    (ricf_visit_owner_state pre s).vs_current_bb = rs.vs_current_bb /\
    rs.vs_inst_idx <= (ricf_visit_owner_state pre s).vs_inst_idx
Proof
  ho_match_mp_tac ricf_visit_prefix_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[ricf_visit_owner_state_def, listTheory.LAST_DEF] >>
  Cases_on `pre` >> gvs[listTheory.LAST_DEF] >>
  metis_tac[venomInstPropsTheory.step_preserves_control_flow,
    ptrDisciplineControlTheory.bind_return_current_bb]
QED

Theorem ricf_protection_cursor_no_reentry:
  ricf_protection_cursor vs C p [] PG G tn fn s ==>
  s.vs_current_bb =
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx).vs_current_bb /\
  SUC p.rpe_before.vs_inst_idx <= s.vs_inst_idx
Proof
  simp[ricf_protection_cursor_def] >> rpt strip_tac >>
  drule ricf_visit_prefix_owner_location >>
  simp[ricf_visit_owner_state_def]
QED

Theorem ricf_protection_inherited_start:
  !vs C p PG G tn caller s stk inv nm ops callee args cs s1 inst RO.
  ricf_protection_cursor vs C p [] PG G tn caller s /\
  frame_reachable vs C stk PG G tn caller inv s /\
  active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
  decode_invoke inv = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  FLOOKUP s.vs_allocas (SND p.rpe_dst) = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP s.vs_allocas (SND p.rpe_src) = SOME (p.rpe_sb,p.rpe_size) /\
  0 < p.rpe_size /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
       ==> RO nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
       ==> RO nm k) ==>
  ricf_protection_inherited vs C RO p
    (<| cf_fn := caller; cf_inst := inv; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `frame_reachable vs C stk PG G tn caller callinst s` >>
  simp[ricf_protection_inherited_def] >>
  qexistsl_tac
    [`<| cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>`,
     `stk`, `[]`, `tn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_start >> metis_tac[]
QED

(* Lifecycle producer obligations, deliberately not asserted as theorems:

   Activation: derive protection_origin at the source MCOPY from the Plan
   event plus source occurrence provenance.  In particular dr/sr root
   lookups, the two local occurrence owners, the literal full size, and the
   numeric operand evaluation must all be proved, not guessed from cert_core.
   cursor_activate then constructs the new same-visit history.  Occurrence
   annotation and natural geometry are separate existing source invariants.

   Ordinary: cursor_next handles event histories.  The actual source step's
   occurrence_sites_step / occurrence_step transport the annotation.  Records
   inherited in active callees use readonly_call_reachable_next, not the
   owner's same-block suffix.  Raw PG/G/tn must be used at these boundaries;
   cert_core's effective G0/tn0 are not substitutes.

   Calls: inherited_start displays the exact missing bridge.  BOTH endpoint
   lookups must be local to the common anchor, and BOTH sets of argument
   positions must satisfy RO.  Destination readonly is an event-use fact;
   source readonly needs the source-isolation/sibling restrictions and the
   analysis bridge.  Nothing here derives either from frame_reachable alone.
   Nested calls use readonly_call_reachable_call.  Saved current records
   become SuspendedCurrent; saved inherited records become SuspendedInherited.
   Their historical taint is existential, not current-memory taint applied to
   a saved memory.  A saved cursor is restored only by the matching return;
   ricf_visit_prefix_call/ret record the actual call/return execution prefix.

   Reentry: cursor_no_reentry rules out reusing an owner's old witness at a
   smaller cursor, including its copy instruction.  Owner terminators have
   no prefix constructor.  Retire its current records and restrict the ghost
   collections as in alignment_retire, then construct new events on the next
   visit.  Inherited readonly histories DO cross block transitions via their
   own block rule.  Zero-size ghosts have no record/history requirement.

   These tests do not establish global lifecycle preservation or actual-use
   read/write exclusion.  Those require the static analysis and origin
   producers and the subsequent lifecycle component's proof.
*)
