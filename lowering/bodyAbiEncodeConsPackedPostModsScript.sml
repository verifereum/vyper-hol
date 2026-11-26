(* Compose positional ABI packing posts at the reached snapshot cut. *)
Theory bodyAbiEncodeConsPackedPostMods
Ancestors
  bodyAbiEncodePackedPostMods exprLoweringProps exprOperandVar
  exprSimWordArgs exprSimProps wordArgsPtr list pair finite_map

Triviality saved_rows_rebase:
  sa.cs_next_var <= ss.cs_next_var /\ sa.cs_next_id <= ss.cs_next_id /\
  LIST_REL (\(e,sv) v. ?si sm sx vv copy.
    abi_encode_saved_row_mods lo cenv cx ss sb e sv v si sm sx vv copy
      H ee G tn t) rows vs ==>
  LIST_REL (\(e,sv) v. ?si sm sx vv copy.
    abi_encode_saved_row_mods lo cenv cx sa sb e sv v si sm sx vv copy
      H ee G tn t) rows vs
Proof
  strip_tac >> irule LIST_REL_mono >>
  first_assum (irule_at Any) >> PairCases >> simp[] >>
  rpt gen_tac >>
  disch_then (qx_choosel_then [`si`,`sm`,`sx`,`vv`,`copy`] assume_tac) >>
  qexistsl_tac [`si`,`sm`,`sx`,`vv`,`copy`] >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def] >> decide_tac
QED

Theorem abi_encode_cons_packed_post_mods:
  ci_mono sa ss /\ ci_mono ss sb /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    [e] [sv] sa ss es s0 G0 tn0 H (INL [v]) mid Gm tm s_mid /\
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    xs svs ss sb mid s_mid Gm tm H (INL vs) ee G tn t /\
  abi_encode_saved_row_mods lo cenv cx sa sb e sv v si sm sx vv copy
    H ee G tn t ==>
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    (e::xs) (sv::svs) sa sb es s0 G0 tn0 H (INL (v::vs)) ee G tn t
Proof
  simp[abi_encode_packed_post_mods_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `MAP FDOM ee.scopes = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `sa.cs_next_var <= ss.cs_next_var /\ sa.cs_next_id <= ss.cs_next_id` by
    fs[ci_mono_def] >>
  `wb_frame cenv es ee sa s0 t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule wb_frame_trans) >>
     qpat_assum `wb_frame cenv es mid sa s0 s_mid` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee ss s_mid t` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (`!n b sz. local_region cenv es.scopes s0 n b sz <=>
                 local_region cenv mid.scopes s_mid n b sz` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
          (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule wb_frame_local_regions) >>
        qpat_assum `wb_frame cenv es mid sa s0 s_mid` (irule_at Any) >> simp[]) >>
     irule ghost_kept_at_trans >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gm tm` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid ss Gm tm s_mid G tn` (irule_at Any) >> simp[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qexistsl_tac [`si`,`sm`,`sx`,`vv`,`copy`] >> first_assum ACCEPT_TAC)
  >- (irule saved_rows_rebase >> qexists `ss` >> asm_rewrite_tac[])
  >- (rpt strip_tac >> irule compiler_ci_mono_not_fresh >> qexists `ss` >> simp[])
  >- (strip_tac >> irule pure_frame_trans >> simp[] >>
      qexistsl_tac [`mid`,`ss`,`s_mid`] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at ss x` by (irule compiler_ci_mono_not_fresh >> qexists `sa` >> simp[]) >>
      `lookup_var x s_mid = SOME w` by simp[] >> simp[])
QED
