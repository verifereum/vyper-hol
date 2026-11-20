Theory internalBlockPackagingProps
Ancestors
  vyperCompiler venomInst list pair

(* A descriptor's label cannot occur in another segment's tail. *)
Theorem package_internal_blocks_separated_segments:
  !descs segs entry tail_label_ok.
    LIST_REL
      (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
        EVERY (\bb. tail_label_ok bb.bb_label) (TL seg)) descs segs /\
    ALL_DISTINCT (MAP FST descs) /\
    EVERY (\d. ~tail_label_ok (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) entry)) descs ==>
    package_internal_blocks descs (entry ++ FLAT segs) =
      SOME (entry,
            MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                            (SND (SND d))) descs segs)
Proof
  Induct >- rw[package_internal_blocks_def] >>
  PairCases >> rw[LIST_REL_CONS1] >>
  rename1 `segment <> []` >>
  Cases_on `segment` >> gvs[] >>
  rename1 `~MEM first.bb_label (MAP FST descs)` >>
  rename1 `EVERY (\bb. tail_label_ok bb.bb_label) tail` >>
  rename1 `LIST_REL _ descs segs` >>
  `split_blocks_at first.bb_label (entry ++ first :: (tail ++ FLAT segs)) =
     SOME (entry, first :: (tail ++ FLAT segs))` by
    (irule split_blocks_at_append_delimiter >> simp[]) >>
  gs[package_internal_blocks_def] >>
  first_x_assum (qspecl_then [`segs`, `first :: tail`, `tail_label_ok`] mp_tac) >>
  impl_tac
  >- (fs[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
      metis_tac[]) >>
  simp[]
QED
