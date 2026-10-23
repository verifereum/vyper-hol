(* Conditional operational boundary for reclaim: semantic provenance and
 * escape/capture protection are ghost inputs, not analyzer conclusions.
 * Numeric address coincidence is deliberately not a provenance relation. *)
Theory fmpProvenanceProps
Ancestors
  fmpReclaimProps fmpAliasProps fmpReclaimDefs fmpAliasDefs list

Definition fmp_base_covers_def:
  fmp_base_covers env prov <=>
    !id v. prov id v ==> MEM id (fmp_bases env v)
End

Definition fmp_escape_covers_def:
  fmp_escape_covers insts env escaped <=>
    !id. escaped id ==>
      EXISTS (\inst. EXISTS (\v. MEM id (fmp_bases env v))
        (fmp_escaping_operands inst)) insts
End

(* Completeness for current live/escaped captures is a separate semantic
 * obligation. Static closure alone does not discharge this predicate. *)
Definition fmp_capture_covers_def:
  fmp_capture_covers fn live p caps capProtect <=>
    !id:num. capProtect id ==> EXISTS (fmp_capture_veto fn live p) caps
End

Definition fmp_protected_def:
  fmp_protected prov livevars escaped capProtect (id:num) <=>
    (?v. MEM v livevars /\ prov id v) \/ escaped id \/ capProtect id
End

Theorem fmp_dead_excludes_live_escape:
  fmp_base_covers env prov /\ fmp_escape_covers insts env escaped /\
  fmp_mark_dead insts env livevars mark /\
  fmp_dalloca_query insts env mark = SOME id ==>
    ~(?v. MEM v livevars /\ prov id v) /\ ~escaped id
Proof
  simp[fmp_base_covers_def, fmp_escape_covers_def,
       fmp_mark_dead_def] >> rpt strip_tac >>
  gvs[fmp_allocation_live_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem fmp_pop_member_dead:
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  MEM mark popped ==>
    fmp_mark_dead (fn_insts fn) env
      (live_vars_at live (FST p) (SND p)) mark
Proof
  rpt strip_tac >>
  `popped <> []` by (Cases_on `popped` >> gvs[]) >>
  drule_all fmp_pop_at_certificate >> simp[EVERY_MEM]
QED

Theorem fmp_pop_capture_unprotected:
  fmp_capture_covers fn live p st.frs_captures capProtect /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  popped <> [] ==> ~capProtect id
Proof
  simp[fmp_pop_at_def, fmp_capture_covers_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem fmp_pop_excludes_protected:
  fmp_base_covers env prov /\
  fmp_escape_covers (fn_insts fn) env escaped /\
  fmp_capture_covers fn live p st.frs_captures capProtect /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  MEM mark popped /\
  fmp_dalloca_query (fn_insts fn) env mark = SOME id ==>
    ~fmp_protected prov (live_vars_at live (FST p) (SND p))
      escaped capProtect id
Proof
  rpt strip_tac >>
  `popped <> []` by (Cases_on `popped` >> gvs[]) >>
  drule_all fmp_pop_member_dead >> strip_tac >>
  drule_all fmp_dead_excludes_live_escape >> strip_tac >>
  gvs[fmp_protected_def] >>
  metis_tac[fmp_pop_capture_unprotected]
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpProvenanceProps");
