(* Execute a selected bytestring operand and append its silent hash path. *)
Theory bodyBopBytestringOperandRunMods
Ancestors
  bodyBopBytestringChildMods bodyBopBytestringHashMods bodyFullIfExpReach
  gasOutcomeIfSuffixMods gasOutcomeFullPostPathMods gasOutcomeFullPostMods
  vyperStorageFootprint vyperState bodyMemoryDefs exprSimDefs bodyBopBytestringBindMods
  exprBopSimDefs vyperStorageTrace
Libs monadsyntax

val forced = ``bind (eval_expr cx e) (read_result cx)``;
val exit = ``\(H : (bool # 256 word # type_value) list # num list) (res:value + exception) ee (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val hash_post = ``\(H : (bool # 256 word # type_value) list # num list) (res:value + exception) ee G' tn' u. ?v bs.
  res = INL v /\ (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
  eval_operand h u = SOME (word_of_bytes_be (Keccak_256_w64 bs)) /\
  op_prov G' h = NONE /\ op_taint tn' h = {} /\
  (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  expr_sim_inv_mods mods cenv cx env ee /\
  stmt_state_rel H ctx func cenv cx ee u /\
  immutable_frame_mods func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' u /\
  ghost_kept_at lo cenv es sa G tn s G' tn' /\
  ~u.vs_halted /\ u.vs_current_bb = sz.cs_current_bb /\
  u.vs_inst_idx = LENGTH sz.cs_current_insts /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame cenv es ee sa s u /\ (~expr_has_effect e ==> pure_frame cenv func es sa s u)``;

Theorem bop_bytestring_operand_run_mods:
  is_bytestring_type (expr_type e) /\ expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
  (case bytestring_literal_hash e of
     SOME digest => h = Lit digest /\ sz = sa
   | NONE => ?m cb shadow_cb.
       lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
       lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
         shadow_sa = (m,shadow_cb) /\
       expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,cb,shadow_sa,shadow_cb) /\
       compile_bytestring_hash m cb = (h,sz) /\ fn_has_code cb sz func /\
       gas_admissible ^forced expr_res_ok es) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 ^forced (es,s,G,tn)
    (\H res ee G' tn' u. (?v. res = INL v /\ ^hash_post H (INL v) ee G' tn' u /\
      (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t)))
    (\H res ee gt r. ?exc. res = INR exc /\ ^exit H (INR exc) ee gt r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac bop_bytestring_child_mods >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ Child Exit` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 ^forced (es,s,G,tn)
     (\H res ee G' tn' t. Child H res ee G' tn' t /\
       ?gs. ^forced (es with gas_obs := gs) = (res,ee)) Exit` by
    (irule gas_outcome_full_mods_post_source >> qexistsl_tac [`Child`,`Exit`] >>
     BETA_TAC >> simp[] >> rpt strip_tac >> qexists_tac `xs` >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
       qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 ^forced (es,s,G,tn) ^hash_post Exit` by
    (irule gas_outcome_full_mods_zero_suffix_mono >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G' tn' t. _ /\ _) Exit`
       (irule_at Any) >> BETA_TAC >> simp[] >>
     qx_genl_tac [`res`,`ee`,`Gc`,`tnt`,`t`] >> strip_tac >>
     `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
     irule bop_bytestring_hash_mods >> simp[] >>
     qexists_tac `gs` >> first_assum ACCEPT_TAC) >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 ^forced (es,s,G,tn)
     (\H res ee G' tn' u. ^hash_post H res ee G' tn' u /\
       (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t)) Exit` by
    (irule gas_outcome_full_mods_post_path >> qexists_tac `^hash_post` >>
     BETA_TAC >> simp[] >> rpt strip_tac >>
     drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G' tn' u. _ /\
    (!fn inst t. frag_reachable _ _ u fn inst t ==> _)) Exit` (irule_at Any) >>
  simp[Abbr `Exit`] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `?v bs. res = INL v /\ _`
        (qx_choose_then `v` (qx_choose_then `bs` (map_every assume_tac o CONJUNCTS))) >>
      qexists_tac `v` >> simp[] >> conj_tac
      >- (qexists_tac `bs` >> simp[]) >> first_assum ACCEPT_TAC) >>
  gen_tac >> Cases >> simp[expr_exit_def]
QED

(* Keep the start of each hash in its own post, so the second post is
   instantiated only after the first operand has reached its endpoint. *)
val landing = ``\e es sa s G tn h sz H v ee G' tn' u.
    ^hash_post H (INL v) ee G' tn' u /\
    (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t)``;
val landing1 = ``^landing e1 es sa s0 G0 tn0 h1 sh1``;
val landing2 = ``\(v1:value) mid G1 tn1 t. ^landing e2 mid sh1 t G1 tn1 h2 sh2``;
val force1 = ``bind (eval_expr cx e1) (read_result cx)``;
val force2 = ``bind (eval_expr cx e2) (read_result cx)``;
val exit_only = ``\H (res : value + exception) ee gt r. ?exc. res = INR exc /\ ^exit H (INR exc) ee gt r``;
val suffix = ``\v1 v2 ss. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ss,ss)``;

Theorem bop_bytestring_bind_hashes_mods:
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 ^force1 (es,s0,G0,tn0)
    (\H res mid G1 tn1 t. ?v1. res = INL v1 /\ ^landing1 H v1 mid G1 tn1 t) ^exit_only /\
  (!m1 v1 mid G1 tn1 t.
     (!tail. ^force1 (es with gas_obs := gas_explicit m1 s0.vs_gas_readings ++ tail) =
              (INL v1,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> ^landing1 H v1 mid G1 tn1 t) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 ^force2 (mid,t,G1,tn1)
       (\H res ee G2 tn2 u. ?v2. res = INL v2 /\ ^landing2 v1 mid G1 tn1 t H v2 ee G2 tn2 u)
       ^exit_only) /\
  (!m1 v1 mid G1 tn1 t m2 v2 ee G2 tn2 u.
     (!tail. ^force1 (es with gas_obs := gas_explicit m1 s0.vs_gas_readings ++ tail) =
              (INL v1,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> ^landing1 H v1 mid G1 tn1 t) /\
     (!tail. ^force2 (mid with gas_obs := gas_explicit m2 t.vs_gas_readings ++ tail) =
              (INL v2,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~u.vs_halted /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> ^landing2 v1 mid G1 tn1 t H v2 ee G2 tn2 u) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (^suffix v1 v2) (ee,u,G2,tn2) Q ^exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind ^force1 (\v1. bind ^force2 (^suffix v1))) (es,s0,G0,tn0) Q ^exit
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ho_match_mp_tac (GEN_ALL bop_bytestring_bind_mods) >>
  qexistsl_tac [`^landing2`,`^landing1`] >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[storage_trace_frame_def,bop_result_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
