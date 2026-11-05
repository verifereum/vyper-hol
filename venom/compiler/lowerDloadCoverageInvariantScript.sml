Theory lowerDloadCoverageInvariant
Ancestors
  lowerDloadSharedState lowerDloadFrameCertificate lowerDloadCertificateProbe
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadAllocation
  venomExecSemantics ptrDiscipline finite_map

(* Data at original-instruction boundaries, NOT the complete coverage
   invariant. Memory, live geometry, control and macro anchors are separate. *)
Definition ld_frame_data_def:
  ld_frame_data V U E L H AP BP AG BH tn un s t <=>
    ld_frame_embedding E L H s t /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
    ld_owned_vars U E AG BH tn un s t /\
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    ld_shared_state tn un s t
End

Theorem ld_frame_data_embedding:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_params:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  LIST_REL (ld_owned_selection E) AP BP
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_provenance:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  !v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_vars:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_owned_vars U E AG BH tn un s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_definedness:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  !v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_shared:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_shared_state tn un s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_initial:
  s.vs_allocas = FEMPTY ==>
  ld_frame_data V U FEMPTY FEMPTY FEMPTY [] [] FEMPTY FEMPTY
    entry_taint entry_taint s s
Proof
  simp[ld_frame_data_def, ld_frame_embedding_def, ld_erase_def,
       ld_owned_selection_def, ld_owned_empty_initial, ld_shared_state_identity]
QED

(* This is genuinely anchored at source entry. The reflexive second conjunct
   does not identify s1 with the transformed program's entered state. *)
Theorem ld_frame_data_source_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>) s1 /\
  s1.vs_allocas = FEMPTY /\ active_inst fn inst s1 ==>
  ld_annotated_reachable vs0 ctx [] 0 FEMPTY [] FEMPTY
    entry_taint fn inst s1 /\
  ld_frame_data V U FEMPTY FEMPTY FEMPTY [] [] FEMPTY FEMPTY
    entry_taint entry_taint s1 s1
Proof
  strip_tac >> conj_tac
  >- (irule ld_annotated_reachable_entry >> simp[] >>
      goal_assum (drule_at Any)) >>
  irule ld_frame_data_initial >> simp[]
QED

(* Indexed saved-stack probe: budgets count strictly older suspended scratch.
   This explicit schema is not yet a global coverage invariant. *)
Theorem ld_saved_indexed_empty:
  LENGTH ([]:ld_saved_frame list) = LENGTH ([]:ld_saved_frame list) /\
  LENGTH ([]:string set list) = LENGTH ([]:ld_saved_frame list) /\
  LENGTH ([]:num set list) = LENGTH ([]:ld_saved_frame list) /\
  LENGTH ([]:num set list) = LENGTH ([]:ld_saved_frame list) /\
  (!j. j < LENGTH ([]:ld_saved_frame list) ==>
    ld_saved_embedded
      {v | v IN EL j ([]:string set list) /\
           ~retpc_var (EL j ([]:ld_saved_frame list)).lf_fn v}
      E (EL j ([]:num set list))
      (32 * SUM (MAP CARD (DROP (SUC j) ([]:num set list))))
      (EL j ([]:num set list)) (EL j ([]:ld_saved_frame list)) (EL j ([]:ld_saved_frame list)) /\
    (!v. v IN EL j ([]:string set list) ==>
      (lookup_var v (EL j ([]:ld_saved_frame list)).lf_state = NONE <=>
       lookup_var v (EL j ([]:ld_saved_frame list)).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL j ([]:ld_saved_frame list)).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32) /\
    (!v. (case FLOOKUP (EL j ([]:ld_saved_frame list)).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32))
Proof
  simp[]
QED

Theorem ld_saved_indexed_cons:
  (LENGTH (g::gs) = LENGTH (f::fs) /\
   LENGTH (V::supports) = LENGTH (f::fs) /\
   LENGTH (keys0::keys) = LENGTH (f::fs) /\
   LENGTH (A::suspended) = LENGTH (f::fs) /\
   (!j. j < LENGTH (f::fs) ==>
     ld_saved_embedded
       {v | v IN EL j (V::supports) /\ ~retpc_var (EL j (f::fs)).lf_fn v}
       E (EL j (keys0::keys))
       (32 * SUM (MAP CARD (DROP (SUC j) (A::suspended))))
       (EL j (A::suspended)) (EL j (f::fs)) (EL j (g::gs)) /\
     (!v. v IN EL j (V::supports) ==>
       (lookup_var v (EL j (f::fs)).lf_state = NONE <=>
        lookup_var v (EL j (g::gs)).lf_state = NONE)) /\
     (!v. (case FLOOKUP (EL j (f::fs)).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32) /\
     (!v. (case FLOOKUP (EL j (g::gs)).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32))) <=>
  (ld_saved_embedded {v | v IN V /\ ~retpc_var f.lf_fn v}
     E keys0 (32 * SUM (MAP CARD suspended)) A f g /\
   (!v. v IN V ==>
     (lookup_var v f.lf_state = NONE <=> lookup_var v g.lf_state = NONE)) /\
   (!v. (case FLOOKUP f.lf_tvar v of NONE => {} | SOME m => m) SUBSET count 32) /\
   (!v. (case FLOOKUP g.lf_tvar v of NONE => {} | SOME m => m) SUBSET count 32) /\
   LENGTH gs = LENGTH fs /\ LENGTH supports = LENGTH fs /\
   LENGTH keys = LENGTH fs /\ LENGTH suspended = LENGTH fs /\
   (!j. j < LENGTH fs ==>
     ld_saved_embedded
       {v | v IN EL j supports /\ ~retpc_var (EL j fs).lf_fn v}
       E (EL j keys) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
       (EL j suspended) (EL j fs) (EL j gs) /\
     (!v. v IN EL j supports ==>
       (lookup_var v (EL j fs).lf_state = NONE <=>
        lookup_var v (EL j gs).lf_state = NONE)) /\
     (!v. (case FLOOKUP (EL j fs).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32) /\
     (!v. (case FLOOKUP (EL j gs).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32)))
Proof
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV
    (HO_REWR_CONV arithmeticTheory.FORALL_NUM))) >>
  simp[] >> metis_tac[]
QED

Theorem ld_saved_indexed_frame:
  LENGTH gs = LENGTH fs /\ LENGTH supports = LENGTH fs /\
  LENGTH keys = LENGTH fs /\ LENGTH suspended = LENGTH fs /\
  (!j. j < LENGTH fs ==>
    ld_saved_embedded
      {v | v IN EL j supports /\ ~retpc_var (EL j fs).lf_fn v}
      E (EL j keys) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
      (EL j suspended) (EL j fs) (EL j gs) /\
    (!v. v IN EL j supports ==>
      (lookup_var v (EL j fs).lf_state = NONE <=>
       lookup_var v (EL j gs).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL j fs).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32) /\
    (!v. (case FLOOKUP (EL j gs).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32)) /\
  j < LENGTH fs ==>
  ld_saved_embedded
    {v | v IN EL j supports /\ ~retpc_var (EL j fs).lf_fn v}
    E (EL j keys) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
    (EL j suspended) (EL j fs) (EL j gs)
Proof
  simp[]
QED

Theorem ld_owned_selection_owner_domain:
  ld_owned_selection E (SOME (owner,(bs,sz))) pt ==> owner IN FDOM E
Proof
  simp[ld_owned_selection_def, lowerDloadLifetimeTheory.ld_site_entry_def,
       FLOOKUP_DEF] >> metis_tac[]
QED

(* LIVE-SUPPORT AUDIT (C2.package.stack).
   ld_live_def is the disjunction of current ld_selected L AP AG and a
   selected local/parameter/provenance site of any saved frame MEM f astk.
   ld_selected_def covers all three sources, not only allocation locals.
   This matches the support needed by saved_embedded; its source selections
   identify owners in E by ld_owned_selection_owner_domain. The target
   selection has the same owner, and frame_embedding allows target-only
   scratch entries instead of demanding erase H = target.vs_allocas.
   No mismatch was found in the live-set definition. On table extension,
   existing supported entries must be retained. On return, restrict E only
   after identifying the selections of the surviving current/saved frames:
   historical FDOM E is NOT a live geometry bound, and callee memory must
   NOT be replaced by a saved caller memory snapshot. Indexed cons above
   computes the head's inherited scratch charge from suspended_tail only;
   it proves neither actual call push nor return preservation. *)
