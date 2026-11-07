(* General metadata and compiler-growth boundaries for body aggregate loops. *)
Theory exprSimAggregateBodyFrames
Ancestors
  exprLoweringProps vyperImmutableMetadataFrame compileEnv

Theorem aggregate_body_ci_mono_trans:
  ci_mono a b /\ ci_mono b c ==> ci_mono a c
Proof
  simp[ci_mono_def] >> rpt strip_tac >> gvs[] >>
  irule cs_extends_trans >> qexists_tac `b` >> simp[]
QED

Theorem immutable_metadata_frame_property:
  immutable_metadata_frame es mid /\
  (!name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables addr of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    P itv io) ==>
  !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables addr of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    P itv io
Proof
  rpt strip_tac >> fs[immutable_metadata_frame_def] >>
  qpat_x_assum `!addr. IS_SOME _ <=> IS_SOME _`
    (qspec_then `addr` mp_tac) >>
  Cases_on `ALOOKUP es.immutables addr` >>
  Cases_on `ALOOKUP mid.immutables addr` >> gvs[] >>
  rename1 `ALOOKUP es.immutables addr = SOME oldimms` >>
  qpat_x_assum `!addr imms imms' src id. _`
    (drule_all_then (qspecl_then [`ce.ce_module`, `name`] mp_tac)) >>
  Cases_on `FLOOKUP (get_source_immutables ce.ce_module oldimms) name` >>
  simp[] >> rename1 `SOME pair` >> Cases_on `pair` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
