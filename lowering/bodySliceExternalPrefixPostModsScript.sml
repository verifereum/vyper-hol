(* Rebase the external-code Slice's memory post over its three forced reads. *)
Theory bodySliceExternalPrefixPostMods
Ancestors
  bodyFullPostsMods bodyForcedStorageFrameMods bodyFullHashKeccakFixed
  exprSimSliceOrdinaryContinue exprSimCalldataSlice exprSimWordArgs wordArgsPtr
  exprLoweringProps loweringPosts vyperStorageFootprint vyperState context
Libs monadsyntax

val wp = ``\e es sa sb s0 ee v op t G0 tn0 G tn (H:(bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ ee.gas_obs = [] /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val cut = ``\e es sa sb s0 ee v op t G0 tn0 G tn marks.
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ^wp e es sa sb s0 ee v op t G0 tn0 G tn H)``;

Triviality slice_read_prefix_horizon:
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  valid_horizon cx st0 H mid.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace /\ MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  conj_tac
  >- (qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
      simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Triviality slice_prefix_memory_vv_post:
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value (BytesV bs))
    (LocatedValue ann (mk_ptr out LocMemory)) t <=>
  vv_post H ctx func cenv cx e es sa sb s0 ee (Value (BytesV bs))
    (LocatedValue ann (mk_ptr out LocMemory)) t /\ immutable_frame_mods func cenv cx ee t
Proof
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,mk_ptr_def] >>
  metis_tac[]
QED

Triviality slice_read_ghost_rebase:
  expr_post (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid v op s /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ ci_mono sa sm /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 s HG tm ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm
Proof
  strip_tac >> drule_then assume_tac expr_post_frame >>
  fs[ci_mono_def] >>
  drule_all ghost_kept_at_wb_trans >> simp[]
QED

Theorem slice_external_prefix_post_mods:
  let ann = BaseT (BytesT (Dynamic n));
      e = Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len];
      tv = Value (BytesV (TAKE k (DROP i code)));
      vv = LocatedValue ann (mk_ptr out LocMemory)
  in
  ^cut start es sa s1 s0 mid v1 x t1 G0 tn0 G1 tn1 marks1 /\
  ^cut len mid s1 s2 t1 fin v2 y t2 G1 tn1 G2 tn2 marks2 /\
  ^cut addr fin s2 s3 t2 ae av aop z G2 tn2 G3 tn3 marks3 /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  valid_horizon cx st0 H ee.storage_trace /\ ee.storage_trace = ae.storage_trace /\
  vv_post_mods H ctx func cenv cx e ae s3 sb z ee tv vv t /\
  ghost_kept_at lo cenv ae s3 G3 tn3 z HG tm /\ z.vs_alloca_next <= t.vs_alloca_next ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)
Proof
  BETA_TAC >> simp_tac bool_ss [LET_THM,slice_prefix_memory_vv_post] >> strip_tac >>
  `valid_horizon cx st0 H ae.storage_trace` by
    (qpat_x_assum `ee.storage_trace = ae.storage_trace` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!tail. bind (eval_expr cx addr) _ _ = _`
    (mp_then Any (drule_then strip_assume_tac) slice_read_prefix_horizon) >>
  qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
    (mp_then Any (drule_then strip_assume_tac) slice_read_prefix_horizon) >>
  qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
    (mp_then Any (drule_then strip_assume_tac) slice_read_prefix_horizon) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H ae.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[expr_post_mods_def,ci_mono_def] >>
  `stmt_state_rel H ctx func cenv cx es s0` by simp[] >>
  `stmt_state_rel H ctx func cenv cx mid t1` by drule_then ACCEPT_TAC expr_post_state >>
  `stmt_state_rel H ctx func cenv cx fin t2` by
    (qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC expr_post_state)) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> simp[]) >>
  (conj_tac >- suspend "vv") >>
  simp[] >> (conj_tac >- suspend "ghost") >> suspend "alloca"
QED

Resume slice_external_prefix_post_mods[vv]:
  qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
    (mp_then (Pat `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`) match_mp_tac
       slice_two_operand_post_rebase) >>
  qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> irule vv_post_prefix_frame >>
  qpat_assum `vv_post H _ _ _ _ _ ae _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (strip_tac >>
      qpat_assum `expr_post H _ _ _ _ addr _ _ _ _ _ _ _ _`
        (mp_then Any irule expr_post_pure_frame) >> simp[]) >>
  qpat_assum `expr_post H _ _ _ _ addr _ _ _ _ _ _ _ _`
    (mp_then Any ACCEPT_TAC expr_post_frame)
QED

Resume slice_external_prefix_post_mods[ghost]:
  `ghost_kept_at lo cenv fin s2 G2 tn2 t2 HG tm` by
    (irule slice_read_ghost_rebase >>
     qpat_assum `expr_post H _ _ _ _ addr _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ae s3 G3 tn3 z HG tm` (irule_at Any) >>
     simp[ci_mono_def]) >>
  `ghost_kept_at lo cenv mid s1 G1 tn1 t1 HG tm` by
    (irule slice_read_ghost_rebase >>
     qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv fin s2 G2 tn2 t2 HG tm` (irule_at Any) >>
     simp[ci_mono_def]) >>
  irule slice_read_ghost_rebase >>
  qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t1 HG tm` (irule_at Any) >>
  simp[ci_mono_def]
QED

Resume slice_external_prefix_post_mods[alloca]:
  qpat_assum `vv_post H _ _ _ _ _ ae _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  qpat_assum `stmt_state_rel H _ _ _ _ ee t`
    (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)
QED

Finalise slice_external_prefix_post_mods
