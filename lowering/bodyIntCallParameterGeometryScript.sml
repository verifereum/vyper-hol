(* Numeric geometry of full physical slots passed to internal callees. *)
Theory bodyIntCallParameterGeometry
Ancestors
  bodyIntCallSourceSpans intCallCallee

Theorem internal_args_memory_slot_bound:
  !cenv params env base argv frontier mem i off sz.
    internal_args_rel cenv params env base argv frontier mem /\
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP cenv.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    w2n (EL (base + i) argv) + sz <= frontier
Proof
  rpt strip_tac >>
  fs[internal_args_rel_def] >>
  qpat_x_assum `!i. i < LENGTH params ==> _` drule >>
  strip_tac >> gvs[]
QED

Theorem internal_args_separated_source_span:
  !cenv params env base argv frontier mem i off sz d dn s n M.
    internal_args_rel cenv params env base argv frontier mem /\
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP cenv.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) /\
    frontier < M /\
    regions_disjoint d dn (w2n (EL (base + i) argv)) sz /\
    w2n (EL (base + i) argv) <= s /\
    s + n <= w2n (EL (base + i) argv) + sz ==>
    s + n < M /\ regions_disjoint s n d dn
Proof
  rpt strip_tac >>
  drule_all internal_args_memory_slot_bound >> strip_tac >>
  mp_tac source_span_in_separated_slot >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def]
QED
