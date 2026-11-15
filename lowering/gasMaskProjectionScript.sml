(* Project a partial target GAS mask to the events read by the source. *)
Theory gasMaskProjection
Ancestors
  gasSummary list pair sorting

Theorem gas_mask_recorded_partition:
  LENGTH marks = LENGTH slots ==>
  PERM
    (MAP THE (FILTER IS_SOME (MAP SND (FILTER FST (ZIP (marks, slots))))) ++
     MAP THE (FILTER IS_SOME
       (MAP SND (FILTER ($~ o FST) (ZIP (marks, slots))))))
    (MAP THE (FILTER IS_SOME slots))
Proof
  strip_tac >>
  rewrite_tac[GSYM MAP_APPEND] >> irule PERM_MAP >>
  rewrite_tac[GSYM FILTER_APPEND_DISTRIB] >> irule PERM_FILTER >>
  rewrite_tac[GSYM MAP_APPEND] >>
  irule PERM_TRANS >> qexists_tac `MAP SND (ZIP (marks, slots))` >>
  conj_tac
  >- (irule PERM_MAP >> simp[PERM_SYM, PERM_SPLIT]) >>
  simp[MAP_ZIP]
QED

Theorem gas_mask_filling_extension:
  LENGTH marks = LENGTH slots /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP SND (FILTER FST (ZIP (marks, slots)))) gobs ==>
  ?raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw /\
    !tail. gas_explicit marks (raw ++ tail) = gobs
Proof
  qid_spec_tac `gobs` >> qid_spec_tac `slots` >>
  Induct_on `marks`
  >- simp[ZIP] >>
  rpt gen_tac >> rename1 `gas_explicit (mark :: marks) _` >>
  Cases_on `slots` >- simp[] >>
  rename1 `ZIP (_, slot :: slots)` >> Cases_on `mark`
  >- (Cases_on `gobs` >> simp[ZIP] >>
      rename1 `gas_explicit _ _ = w :: gs` >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      rename1 `LIST_REL _ slots raw` >>
      qexists_tac `w :: raw` >>
      simp[gas_explicit_cons]) >>
  simp[ZIP] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `LIST_REL _ slots raw` >>
  qexists_tac `(case slot of NONE => 0w | SOME w => w) :: raw` >>
  Cases_on `slot` >> simp[gas_explicit_cons]
QED

(* Lift a property of every raw filling to the projected source mask. *)
Theorem gas_mask_projection:
  !flags slots unused readings (P : bytes32 list -> bool).
    LENGTH flags = LENGTH slots /\
    PERM (MAP THE (FILTER IS_SOME slots) ++ unused) readings /\
    (!raw tail.
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw ==>
       P (gas_explicit flags raw ++ tail)) ==>
    ?source_slots source_unused.
      PERM (MAP THE (FILTER IS_SOME source_slots) ++ source_unused) readings /\
      !gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) source_slots gs ==>
        P (gs ++ tail)
Proof
  rpt gen_tac >> strip_tac >>
  drule gas_mask_recorded_partition >> strip_tac >>
  qexistsl_tac
    [`MAP SND (FILTER FST (ZIP (flags, slots)))`,
     `MAP THE (FILTER IS_SOME
        (MAP SND (FILTER ($~ o FST) (ZIP (flags, slots))))) ++ unused`] >>
  conj_tac
  >- (rewrite_tac[APPEND_ASSOC] >> irule PERM_TRANS >>
      qexists_tac `MAP THE (FILTER IS_SOME slots) ++ unused` >>
      conj_tac >- simp[PERM_APPEND_IFF] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all gas_mask_filling_extension >> strip_tac >>
  qpat_x_assum `!raw tail. LIST_REL _ slots raw ==> _`
    (qspecl_then [`raw`, `tail`] mp_tac) >>
  simp[] >>
  qpat_x_assum `!tail. gas_explicit flags (raw ++ tail) = gs`
    (qspec_then `[]` mp_tac) >> simp[]
QED
