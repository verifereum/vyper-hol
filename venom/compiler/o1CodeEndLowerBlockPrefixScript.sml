Theory o1CodeEndLowerBlockPrefix
Ancestors
  lowerDloadSafetyKernel singleUseExpansionSupplySim list rich_list arithmetic

Theorem ld_prefix_initial_segment:
  ld_prefix C fn (X ++ Y) p h s t /\ h < LENGTH X ==>
  ld_prefix C fn X p h s t
Proof
  rw[ld_prefix_def] >>
  qexists_tac `R` >> gvs[EL_APPEND_EQN] >> rpt strip_tac >>
  `j < LENGTH X` by decide_tac >>
  qpat_x_assum `!j. j < h ==> _` (qspec_then `j` mp_tac) >> simp[]
QED

Theorem ld_prefix_slice:
  !h p s t X Y.
  ld_prefix C fn (X ++ Y) p (LENGTH X + h) s t ==>
  ?u. ld_prefix C fn (X ++ Y) p (LENGTH X) s u /\
      ld_prefix C fn Y (p + LENGTH X) h u t
Proof
  Induct_on `h`
  >- (rpt strip_tac >> gvs[] >> qexists_tac `t` >> simp[] >>
      drule ld_prefix_active >> drule ld_prefix_bound >>
      simp[ld_prefix_zero, EL_APPEND_EQN]) >>
  rpt strip_tac >>
  drule ld_prefix_bound >> strip_tac >>
  drule ld_prefix_active >> strip_tac >>
  qpat_assum `ld_prefix _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[GSYM ADD_SUC] >>
  disch_then (strip_assume_tac o MATCH_MP ld_prefix_predecessor) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `u'` >> simp[] >>
  irule ld_prefix_extend >>
  fs[EL_APPEND_EQN, LENGTH_APPEND] >>
  qexistsl_tac [`t'`, `u`] >> simp[ADD_ASSOC, ADD_COMM]
QED

Theorem ld_prefix_packet:
  ld_prefix C fn (FLAT packets) p h s t ==>
  ?k q u. k < LENGTH packets /\ q < LENGTH (EL k packets) /\
    h = LENGTH (FLAT (TAKE k packets)) + q /\
    ld_prefix C fn (FLAT packets) p
      (LENGTH (FLAT (TAKE k packets))) s u /\
    ld_prefix C fn (EL k packets)
      (p + LENGTH (FLAT (TAKE k packets))) q u t
Proof
  strip_tac >> drule ld_prefix_bound >> strip_tac >>
  drule sue_segment_interior >>
  simp[sue_segment_offset_def] >> strip_tac >>
  `FLAT packets = FLAT (TAKE i packets) ++
     (EL i packets ++ FLAT (DROP (SUC i) packets))` by
    (qpat_assum `i < LENGTH packets` (mp_tac o MATCH_MP TAKE_DROP_SUC) >>
     disch_then (mp_tac o AP_TERM ``FLAT : instruction list list -> instruction list``) >>
     simp[FLAT_APPEND]) >>
  `?u. ld_prefix C fn (FLAT packets) p
         (LENGTH (FLAT (TAKE i packets))) s u /\
       ld_prefix C fn (EL i packets ++ FLAT (DROP (SUC i) packets))
         (p + LENGTH (FLAT (TAKE i packets))) j u t` by
    (qpat_assum `FLAT packets = _` (fn th => rewrite_tac[th]) >>
     irule ld_prefix_slice >> metis_tac[ADD_COMM]) >>
  qexistsl_tac [`i`, `j`, `u`] >> simp[] >>
  irule ld_prefix_initial_segment >> metis_tac[]
QED
