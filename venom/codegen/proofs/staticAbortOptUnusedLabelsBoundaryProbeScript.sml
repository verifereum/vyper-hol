(* One deletion boundary, not a whole-filter transport.
   Pending fallthrough uses no symbolic, memory or spill invariant.
   An incoming tag needs syntactic provenance in addition to its numeric
   interpretation; the final probe separates those two requirements. *)
Theory staticAbortOptUnusedLabelsBoundaryProbe
Ancestors
  asmOptPruneUnused asmSplice asmSymSem asmSem blockSimHelpers
  staticAbortTrace symbolResolve

Theorem unused_label_pending_fallthrough_envelope:
  p = pre ++ [AsmLabel l] ++ tail /\ q = pre ++ tail /\
  s.as_pc = LENGTH pre /\ ~MEM l (asm_label_refs p) /\
  (!t. t.as_pc = LENGTH pre /\
       LENGTH t.as_stack = LENGTH s.as_stack /\
       t.as_call_ctx = s.as_call_ctx /\ t.as_requests = s.as_requests ==>
       D t) ==>
  asm_window_refines pre [AsmLabel l] [] tail /\
  ?u v.
    static_abort_normal lo o2pc p 1 s u /\
    static_abort_normal lo' o2pc' q 0
      (s with as_code := assemble q ++ data) v /\
    D v /\ u.as_pc = LENGTH pre + 1 /\ v.as_pc = LENGTH pre
Proof
  strip_tac >> conj_tac >- simp[unused_label_window_refines] >>
  qexistsl [`s with as_pc := s.as_pc + 1`,
            `s with as_code := assemble q ++ data`] >>
  `asm_block_at p s.as_pc [AsmLabel l]` by
    simp[asm_block_at_def, listTheory.EL_APPEND_EQN] >>
  `asm_steps lo o2pc p 1 s = AsmOK (s with as_pc := s.as_pc + 1)` by
    metis_tac[label_op_asm_steps] >>
  simp[static_abort_normal_def, static_abort_trace_def] >>
  (* E0032 failed tail: rpt strip_tac >> `k = 0` by decide_tac.
     simp has already eliminated the bounded index; that k was free. *)
  rpt strip_tac >>
  gvs[asm_steps_def, static_abort_safe_at_def, asm_block_at_def,
      listTheory.EL_APPEND_EQN]
QED

(* All three reference constructors are needed. In particular an offset
   push remains provenance even if its current numeric value is a jump
   target of a different shape. This claim is about a tag's label identity,
   not about aliases between byte offsets. *)
Theorem unused_label_excludes_provenanced_incoming_tag:
  ~MEM l (asm_label_refs p) /\
  (!k t d. tags k = SOME (t,d) ==>
     MEM (AsmPushLabel t) p \/ MEM (AsmPushOfst t d) p \/
     MEM (AsmDataLabel t) p) ==>
  !k d. tags k <> SOME (l,d)
Proof
  (* E0050 stopped route:
     strip_tac >> rpt gen_tac >> strip_tac >> first_x_assum drule >>
     qpat_x_assum `~MEM l (asm_label_refs p)` mp_tac >>
     simp[asmOptimizerTheory.asm_label_refs_def, listTheory.MEM_FLAT,
          listTheory.MEM_MAP, PULL_EXISTS] >> disch_tac >>
     first_assum (qspec_then `AsmPushLabel l` assume_tac) >>
     first_assum (qspec_then `AsmPushOfst l d` assume_tac) >>
     first_assum (qspec_then `AsmDataLabel l` assume_tac) >> gvs[]
     Residual: universal no-reference case expression implies three absences. *)
  strip_tac >> rpt gen_tac >> strip_tac >>
  (* E0054: after MEM_FLAT/MEM_MAP, directly supplying AsmPushLabel l
     to qexists failed: the outer witness must be a string list [l]. *)
  qpat_x_assum `!k t d. _` drule >> strip_tac
  >- (`MEM l (asm_label_refs p)` by
        (rewrite_tac[asmOptimizerTheory.asm_label_refs_def,
                     listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
         qexists `[l]` >> reverse conj_tac >- simp[] >>
         qexists `AsmPushLabel l` >> simp[]) >> gvs[])
  >- (`MEM l (asm_label_refs p)` by
        (rewrite_tac[asmOptimizerTheory.asm_label_refs_def,
                     listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
         qexists `[l]` >> reverse conj_tac >- simp[] >>
         qexists `AsmPushOfst l d` >> simp[]) >> gvs[]) >>
  `MEM l (asm_label_refs p)` by
    (rewrite_tac[asmOptimizerTheory.asm_label_refs_def,
                 listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
         qexists `[l]` >> reverse conj_tac >- simp[] >>
     qexists `AsmDataLabel l` >> simp[]) >> gvs[]
QED

(* A live protected-to-pending label value is NOT syntactic provenance.
   This is the zero-offset label interpretation from the candidate tag
   interface, in a program with no reference instructions at all. Thus a
   whole-pass producer must additionally retain the origin of live tags.
   This is not a counterexample to the frozen supplier. *)
Theorem unused_label_live_numeric_tag_without_reference:
  ~MEM "dead" (asm_label_refs [AsmLabel "dead"]) /\
  FLOOKUP (SND (compute_label_offsets [AsmLabel "dead"])) "dead" = SOME 0 /\
  FLOOKUP (build_offset_to_pc [AsmLabel "dead"]) 0 = SOME 0 /\
  EL 0 [0w:bytes32] = (n2w (0 + 0) : bytes32)
Proof
  EVAL_TAC
QED
