(* Restrict the suffix frame without changing the saved value's interval. *)
Theory bodyExtSavedRowCutMods
Ancestors
  bodyPtrDefs loweringPosts freshWrites

Theorem ext_saved_row_restrict_frame:
  ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
  wb_frame cenv pos ee sb u t /\
  ghost_kept_at lo cenv pos sb Gp tp u G tn /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) ==>
  wb_frame cenv pos ee ss u t /\
  ghost_kept_at lo cenv pos ss Gp tp u G tn /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w)
Proof
  strip_tac >>
  `!x. not_fresh_at ss x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rpt conj_tac
  >- (qpat_assum `wb_frame _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
      rewrite_tac[wb_frame_def] >> rpt conj_tac
      >- metis_tac[]
      >- first_assum ACCEPT_TAC
      >- (qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
          `aid < sb.cs_next_id` by decide_tac >>
          qpat_assum `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
      rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
      >- metis_tac[]
      >- (qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
          `aid < sb.cs_next_id` by decide_tac >>
          qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
