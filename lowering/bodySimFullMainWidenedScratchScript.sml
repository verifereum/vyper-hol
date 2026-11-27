(* Scratch statement-level check for the widened body-simulation header. *)
Theory bodySimFullMainWidenedScratch
Ancestors
  loweringPosts bodyFullPostsMods bodyFullPredsMods bodyInvSplit bodySimFull bodySim
  bodyFullShadowBodyInv bodyLoopCalls contractInvContextProps constSubst constSubstMods
  vyperTypeContract[qualified,ignore_grammar] vyperAST vyperInterpreter
  vyperState vyperTypeCallGraph supportedStmts alist list option pair finite_map

val _ = Parse.hide "body";

Theorem stmt_state_rel_frame_wide:
  stmt_state_rel H ctx func cenv cx es s ==>
  immutable_frame_mods func cenv cx es s
Proof
  strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,
       immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def]
QED

Theorem stmt_state_rel_frame_conj_wide:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\ P <=>
  stmt_state_rel H ctx func cenv cx es s /\ P
Proof
  EQ_TAC
  >- metis_tac[]
  >- (strip_tac >>
      `immutable_frame_mods func cenv cx es s` by
        (irule stmt_state_rel_frame_wide >> metis_tac[]) >>
      metis_tac[])
QED

Theorem immutable_holds_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (immutable_holds_mods cenv cx t tv w es s <=>
   immutable_holds cenv cx t tv w es s)
Proof
  strip_tac >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    fs[cenv_module_pins_mods_def, module_body_inv_def] >>
  rw[immutable_holds_mods_def, immutable_holds_def] >>
  simp[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem vv_place_ptr_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (vv_place_ptr_mods cenv cx es s tv vv <=>
   vv_place_ptr cenv cx es s tv vv)
Proof
  strip_tac >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    fs[cenv_module_pins_mods_def, module_body_inv_def] >>
  Cases_on `vv` >> Cases_on `tv` >>
  TRY (rename1 `PlaceR place` >> Cases_on `place`) >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def,
       optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem vv_holds_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (vv_holds_mods cenv cx t tv vv es s <=> vv_holds cenv cx t tv vv es s)
Proof
  strip_tac >> Cases_on `vv` >> simp[vv_holds_mods_def] >>
  rename1 `p.ptr_location = LocCode` >>
  Cases_on `p.ptr_location = LocCode` >>
  simp[vv_holds_def, vv_holds_mods_def] >>
  metis_tac[immutable_holds_mods_wide]
QED

Theorem expr_post_mods_wide:
  expr_post_mods H ctx func cenv cx e es sa sb s0 es' v op s <=>
  expr_post H ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rw[expr_post_mods_def] >> EQ_TAC
  >- (strip_tac >> first_assum ACCEPT_TAC)
  >- (strip_tac >>
      `stmt_state_rel H ctx func cenv cx es' s` by
        (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[expr_post_def]) >>
      `immutable_frame_mods func cenv cx es' s` by
        (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
         simp[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def,
              immutable_frame_mods_def, immutables_rel_mods_def,
              immutable_alloca_sep_mods_def]) >>
      simp[])
QED

Theorem vv_post_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (vv_post_mods H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
   vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s)
Proof
  strip_tac >> EQ_TAC
  >- (strip_tac >>
      `vv_holds_mods cenv cx (post_value_type cenv e) tv vv es' s <=>
       vv_holds cenv cx (post_value_type cenv e) tv vv es' s` by
        (irule vv_holds_mods_wide >> metis_tac[]) >>
      `vv_place_ptr_mods cenv cx es' s tv vv <=>
       vv_place_ptr cenv cx es' s tv vv` by
        (irule vv_place_ptr_mods_wide >> metis_tac[]) >>
      fs[vv_post_mods_def, vv_post_def] >> metis_tac[])
  >- (strip_tac >>
      `stmt_state_rel H ctx func cenv cx es' s` by fs[vv_post_def] >>
      `immutable_frame_mods func cenv cx es' s` by
        (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
         simp[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def,
              immutable_frame_mods_def, immutables_rel_mods_def,
              immutable_alloca_sep_mods_def]) >>
      `vv_holds_mods cenv cx (post_value_type cenv e) tv vv es' s <=>
       vv_holds cenv cx (post_value_type cenv e) tv vv es' s` by
        (irule vv_holds_mods_wide >> metis_tac[]) >>
      `vv_place_ptr_mods cenv cx es' s tv vv <=>
       vv_place_ptr cenv cx es' s tv vv` by
        (irule vv_place_ptr_mods_wide >> metis_tac[]) >>
      fs[vv_post_mods_def, vv_post_def] >> metis_tac[])
QED

Theorem expr_sim_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (expr_sim_full_mods cfg cenv cx ty e es <=>
   expr_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[bodyFullPostsModsTheory.expr_sim_full_mods_def,
       bodySimFullTheory.expr_sim_full_def,
       dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
       ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
       expr_post_mods_wide, stmt_state_rel_frame_wide,
       stmt_state_rel_frame_conj_wide, SF CONJ_ss]
QED

Theorem expr_vv_sim_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (expr_vv_sim_full_mods cfg cenv cx ty e es <=>
   expr_vv_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  drule_all immutable_holds_mods_wide >>
  drule_all vv_holds_mods_wide >>
  drule_all vv_place_ptr_mods_wide >>
  strip_tac >> strip_tac >> strip_tac >>
  ASM_SIMP_TAC bool_ss
    [bodyFullPostsModsTheory.expr_vv_sim_full_mods_def,
     bodySimFullTheory.expr_vv_sim_full_def,
     bodyFullPostsModsTheory.vv_post_mods_def,
     loweringPostsTheory.vv_post_def,
     dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
     ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
     immutable_holds_mods_wide, vv_holds_mods_wide,
     vv_place_ptr_mods_wide,
     stmt_state_rel_frame_wide, stmt_state_rel_frame_conj_wide,
     SF CONJ_ss]
QED

Theorem expr_map_sim_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (expr_map_sim_full_mods cfg cenv cx ty e es <=>
   expr_map_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[bodyFullPostsModsTheory.expr_map_sim_full_mods_def,
       bodySimFullTheory.expr_map_sim_full_def,
       dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
       ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
       stmt_state_rel_frame_wide, stmt_state_rel_frame_conj_wide, SF CONJ_ss]
QED

Theorem stmt_frag_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (stmt_frag_full_mods cfg cx lctx RetQ cenv m shadow_m source es <=>
   stmt_frag_full cfg cx lctx RetQ cenv m shadow_m source es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[bodyFullPostsModsTheory.stmt_frag_full_mods_def,
       bodySimFullTheory.stmt_frag_full_def,
       dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
       ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
       stmt_state_rel_frame_wide, stmt_state_rel_frame_conj_wide, SF CONJ_ss]
QED

(* The signed header keeps its two guards.  The post callbacks are the
   widened single-file posts, by expr_post_mods_wide and vv_post_mods_wide.
   The induction itself is intentionally admitted in this fast-fail scratch. *)
val linked_body_guard_wide =
  ``ALOOKUP cx.sources cx.txn.target = SOME mods /\
    vyperTypeContract$exports_ok cx.layouts cx.txn.target mods exps /\
    IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target mods) /\
    EVERY (struct_args_unique o SND) mods /\
    (!src tops vis mut nr raw fn args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
       stmts_loop_calls_ok mods
         (subst_consts_stmts_mods (consts_env_mods mods) ss))``;
val linked_calls_live_wide =
  ``\calls. EVERY (\k. MEM k
      (vyperTypeContract$linked_live_functions mods exps)) calls``;
fun linked_body_ind_wide rank_guard =
  evaluate_ind |> Q.SPECL [
    `\cx s. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_stmt s) /\ stmt_loop_calls_ok mods s ==>
       body_stmt_full_ok_mods mods exps cx s`,
    `\cx ss. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_stmts ss) /\ stmts_loop_calls_ok mods ss ==>
       body_stmts_full_ok_mods mods exps cx ss`,
    `\cx it. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_iterator it) ==>
       body_iterator_full_ok_mods mods exps cx it`,
    `\cx tyv nm body vs. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_stmts body) /\ stmts_loop_calls_ok mods body ==>
       body_for_full_ok_mods mods exps cx tyv nm body vs`,
    `\cx e. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_expr e) ==>
       body_expr_full_ok_mods mods exps cx e`,
    `\cx es. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_exprs es) ==>
       body_exprs_full_ok_mods mods exps cx es`,
    `\cx t. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_target t) ==>
       body_base_target_full_ok_mods mods exps cx t`,
    `\cx t. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_target t) ==>
       body_base_target_full_ok_mods mods exps cx t`,
    `\cx g v. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_atarget g) ==>
       body_tuple_target_full_ok_mods mods exps cx g v`,
    `\cx gs vs. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_atargets gs) ==>
       body_tuple_targets_full_ok_mods mods exps cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV);
val ranked_linked_body_ind_wide = linked_body_ind_wide ``LENGTH (remcode cx) <= rank``;

Theorem body_sim_full_mutual_ranked_widened:
  !mods exps rank:num. ^(snd (dest_imp (concl ranked_linked_body_ind_wide)))
Proof
  cheat
QED

Theorem body_sim_header_post_equiv:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  ((expr_post_mods H ctx func cenv cx e es sa sb s0 es' v op s <=>
    expr_post H ctx func cenv cx e es sa sb s0 es' v op s) /\
   (vv_post_mods H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
    vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s))
Proof
  strip_tac >>
  conj_tac
  >- irule expr_post_mods_wide
  >- (irule vv_post_mods_wide >> metis_tac[])
QED
