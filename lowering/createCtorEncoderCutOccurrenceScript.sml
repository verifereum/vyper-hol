(* The two caller segments can meet the encoder exit PC only at their join. *)
Theory createCtorEncoderCutOccurrence
Ancestors
  createSizeEdgePC blockPrefixEquiv venomInst relation

Theorem ctor_encoder_cut_occurrence:
  (t.vs_current_bb,t.vs_inst_idx) = (lbl,SUC k) /\
  (z.vs_current_bb,z.vs_inst_idx) = (lbl,SUC k) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  get_instruction bb k = SOME j /\
  j.inst_opcode <> PHI /\ j.inst_id < h /\
  (!u v. A u v ==> (u.vs_current_bb,u.vs_inst_idx) <> (lbl,SUC k)) /\
  (!u v. B u v ==>
    ?bb' i ms.
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb' /\
      get_instruction bb' u.vs_inst_idx = SOME i /\ h <= i.inst_id /\
      gas_origin_edge F exp ctx fn u ms (OK v)) ==>
  (RTC A z t \/ RTC B t z) ==> z = t
Proof
  strip_tac >>
  `phi_prefix_length bb.bb_instructions <= k`
    by (irule phi_prefix_length_non_phi >>
        gvs[get_instruction_def, AllCaseEqs()]) >>
  `!u v. B u v ==> (v.vs_current_bb,v.vs_inst_idx) <> (lbl,SUC k)`
    by (rpt strip_tac >> gvs[] >>
        qpat_assum `!u v. B u v ==> _` drule >> strip_tac >>
        drule_all create_ok_edge_pc >> strip_tac >> gvs[] >> fs[]) >>
  strip_tac
  >- (qpat_x_assum `RTC A z t` mp_tac >>
      simp[Once RTC_CASES1] >> metis_tac[]) >>
  qpat_x_assum `RTC B t z` mp_tac >>
  simp[Once RTC_CASES2] >> metis_tac[]
QED
