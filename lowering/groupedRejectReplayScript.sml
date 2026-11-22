(* Restore the real outcomes and replay the initializer to its first cut. *)
Theory groupedRejectReplay
Ancestors
  ptrDiscipline fragGasOriginPtr list fragExec fragGasOrigin fragGasPathPtr gasEvents pred_set
  venomInst venomState callRejectMemory[ignore_grammar] contextRawReachable compileEnv
  vyperContext fragFuel finite_map rich_list words pair dftCommutation
  loweringBudgetFrameOracleTransport loweringBudgetNonconsumingOracleTransport arithmetic
  relation vyperAST groupedRejectOmittedArguments groupedRejectSourceError groupedRejectTerminal
  vyperTypeContract fragGasPath venomExecSemantics bodyPtrDefs exprLoweringProps moduleLowering
  gasShadowState gasShadow allocaHistory loweringStateRelDefs vyperStorageFootprint
  vyperValue[qualified,ignore_grammar] gasContext gasShadowUnit bodyFullShadowBodyInv
  exprSimHypsDefs bodyFullPreds
Libs
  runtimeDefaultRejectSyntaxLib groupedRejectCutLib groupedRejectSlotsLib

val _ = Parse.hide "tops";

Theorem row22_omitted_seed_path:
  compile_init_kwargs ce vars off 0 hi sa = ((),sb) /\
  compile_init_kwargs ce (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
    off 0 hi sha = ((),shb) /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
  LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
    dst = Var p /\ runtime_constant_expr [(NONE,src_tops)] e /\ expr_type e = ty /\
    (!es'. expr_sim_inv (ce with ce_vars := FEMPTY) cx env es' ==>
      expr_body_pre (ce with ce_vars := FEMPTY) cx env e es') /\
    lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
      lower_value compile_expr ce ty e /\
    lower_value compile_expr (ce with ce_vars := FEMPTY) ty (gas_shadow_expr e) =
      lower_value compile_expr ce ty (gas_shadow_expr e) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256)) vars slots /\
  EVERY (^row22_kw_alloc sa s G tn) slots /\
  EVERY (^row22_kw_initialized sa s G tn) kept /\
  ALL_DISTINCT (MAP FST slots ++ MAP FST kept) /\
  body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
  env.type_defs = get_tenv cx /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct fn /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) 0 (ce with ce_vars := FEMPTY) cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx es G tn s) /\
  expr_sim_inv (ce with ce_vars := FEMPTY) cx env es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  alloca_history fn s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f inst u. frag_reachable ctx fn s f inst u ==> dalloca_no_wrap inst u) /\
  ~s.vs_halted /\ at_point sa s /\
  check_contract F layouts addr [(NONE,src_tops)] = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,src_tops)] /\
  no_sha256_exprs (MAP (\(_,_,_,e). e) vars) /\
  storage_trace_domain cx st0 es.storage_trace ==>
  ?D explicit marks r J tz.
    gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,G,tn) marks (r,J,tz) /\
    (!w. r = OK w ==> at_point sb w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (runtime_constant_expr [(NONE,src_tops)]) (MAP (\(_,_,_,e). e) vars)` by
    (simp[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     simp[FORALL_PROD] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >>
     disch_then (qx_choose_then `slot` strip_assume_tac) >>
     PairCases_on `slot` >> fs[]) >>
  mp_tac row22_source_no_exempt_if_descent >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (GEN_ALL grouped_default_error_descent))) >>
  disch_then (qspecl_then [`cx`, `[(NONE,src_tops)]`, `MAP (\(_,_,_,e). e) vars`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> mp_tac row22_omitted_seed_path_if_no_exempt >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* Transport just the fetched instruction, not all of the installed code. *)
Triviality row22_edge_outcomes_update[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ^default_opcode i.inst_opcode /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,H,ty) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s with vs_outcomes := os,G,tn)
    marks (map_result_state (\t. t with vs_outcomes := os) r,H,ty)
Proof
  strip_tac >> irule gas_origin_ptr_edge_outcomes_update_at >> fs[]
QED

(* A path supplied by the initializer model may reach the cut more than
   once. Restore the real outcome list only on the prefix to the first cut. *)
Triviality row22_path_restore_outcomes[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,H,tz) /\
  (!t. r = OK t ==> at_point cut t) /\
  P (s with vs_outcomes := os) /\
  (!u v n. P u /\ ~at_point cut u /\ gas_path_edge ctx fn u n (OK v) ==> P v) /\
  (!u bb i. P u /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> ^default_opcode i.inst_opcode) ==>
  ?tags r' J tj. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s with vs_outcomes := os,G,tn) tags (r',J,tj) /\
    (!t. r' = OK t ==> at_point cut t)
Proof
  qsuff_tac `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
    !s G tn.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\
      (!t. FST out = OK t ==> at_point cut t) /\
      P (s with vs_outcomes := os) /\
      (!u v n. P u /\ ~at_point cut u /\ gas_path_edge ctx fn u n (OK v) ==> P v) /\
      (!u bb i. P u /\ ~at_point cut u /\
        lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb u.vs_inst_idx = SOME i ==> ^default_opcode i.inst_opcode) ==>
      ?tags r' J tj. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
          (s with vs_outcomes := os,G,tn) tags (r',J,tj) /\
        (!t. r' = OK t ==> at_point cut t)`
  >- (strip_tac >> strip_tac >> res_tac >> (simp[pairTheory.FST])) >>
  ho_match_mp_tac gas_origin_ptr_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (qexistsl_tac [`[]`,`OK (s with vs_outcomes := os)`,`G`,`tn`] >>
      fs[gas_origin_ptr_path_rules, at_point_def]) >>
  `~s.vs_halted /\ ?bb inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst` by
    metis_tac[gas_origin_ptr_edge_common_fuel] >>
  (Cases_on `at_point cut (s with vs_outcomes := os)`
   >- (qexistsl_tac [`[]`,`OK (s with vs_outcomes := os)`,`G`,`tn`] >>
       simp[gas_origin_ptr_path_rules])) >>
  `^default_opcode inst.inst_opcode` by
    (qpat_assum `!u bb i. P u /\ _ /\ lookup_block _ _ = SOME bb /\ _ ==> _`
       (qspecl_then [`s with vs_outcomes := os`, `bb`, `inst`] mp_tac) >> simp[]) >>
  drule_all row22_edge_outcomes_update >>
  disch_then (qspec_then `os` assume_tac) >> gvs[map_result_state_def]
  >- suspend "continue"
  >> suspend "exit"
QED

Resume row22_path_restore_outcomes[continue]:
  `P (mid with vs_outcomes := os)` by
    (qpat_assum `gas_origin_ptr_edge _ (s with vs_outcomes := os,G,tn) _ _`
       (mp_tac o MATCH_MP entry_origin_edge_erase) >> metis_tac[]) >>
  qpat_x_assum `P (mid with vs_outcomes := os) /\ _ ==> ?tags r' J tj. _` mp_tac >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tail`,`rnext`,`hnext`,`tk`] strip_assume_tac) >>
  qexistsl_tac [`left ++ tail`,`rnext`,`hnext`,`tk`] >>
  simp[] >> metis_tac[cj 2 gas_origin_ptr_path_rules]
QED

Resume row22_path_restore_outcomes[exit]:
  qexistsl_tac [`marks`,`map_result_state (\t. t with vs_outcomes := os) r`,
                `G'`,`tn'`] >>
  conj_tac
  >- (irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_outcomes_update]) >>
  Cases_on `r` >> gvs[exit_result_def, map_result_state_def]
QED

Finalise row22_path_restore_outcomes[local]

Triviality row22_real_initializer_replay[local]:
  (?D explicit marks r H tz.
    gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (u with vs_outcomes := [],G,tn)
      marks (r,H,tz) /\ (!t. r = OK t ==> at_point cut t)) /\
  P u /\
  (!u v n. P u /\ ~at_point cut u /\ gas_path_edge ctx fn u n (OK v) ==> P v) /\
  (!u bb i. P u /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> ^default_opcode i.inst_opcode) ==>
  (?z J tj tags. z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (u,G,tn) tags
      (Abort Revert_abort z,J,tj)) \/
  (?t J tj tags. P t /\ at_point cut t /\
    !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (u,G,tn) tags (OK t,J,tj))
Proof
  strip_tac >>
  mp_tac (Q.INST [`s` |-> `u with vs_outcomes := []`, `os` |-> `u.vs_outcomes`,
                  `lo` |-> `0`, `PG` |-> `[]`] row22_path_restore_outcomes) >>
  `u with vs_outcomes := u.vs_outcomes = u` by simp[] >>
  simp[] >>
  impl_tac >- (fs[] >> conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tags`,`rreal`,`hreal`,`treal`] strip_assume_tac) >>
  irule entry_replay_default_through_cut >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `\i. ^default_opcode i.inst_opcode` >>
      fs[] >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`D`,`hreal`,`explicit`,`tags`,`rreal`,`treal`] >>
  simp[] >> first_assum ACCEPT_TAC
QED

(* First stop the real supplied path at the cut or its endpoint. If the
   endpoint is reached before the cut, retain only its stopped reachability;
   continue with the original supplied path and its original ghosts. *)
Theorem row22_replay_initializer:
  ^row22_cut_facts ctx fn cut a entry /\
  (!D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (a,Ga,ta) [] (OK u,G,tn)) /\
  (?D explicit marks r H tz.
    gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (u with vs_outcomes := [],G,tn) marks (r,H,tz) /\
    (!t. r = OK t ==> at_point cut t)) ==>
  (?z J tj tags. z.vs_returndata = [] /\
    !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (a,Ga,ta) tags (Abort Revert_abort z,J,tj)) \/
  (?w J tj tags. at_point cut w /\ fresh_vars_wrt entry w /\ w.vs_call_ctx = a.vs_call_ctx /\
    (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
    !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (a,Ga,ta) tags (OK w,J,tj))
Proof
  BETA_TAC >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `P = ^row22_stopped ctx fn cut a` >>
  `P a` by simp[Abbr `P`, RTC_REFL] >>
  `!x y n. P x /\ ~at_point cut x /\ gas_path_edge ctx fn x n (OK y) ==> P y` by
    (simp[Abbr `P`] >> rpt strip_tac >> irule (cj 2 RTC_RULES_RIGHT1) >>
     qexists_tac `x` >> simp[] >> qexists_tac `n` >> simp[]) >>
  Q.SUBGOAL_THEN `(?z J tj tags. z.vs_returndata = [] /\
     !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (a,Ga,ta) tags (Abort Revert_abort z,J,tj)) \/
   (?w J tj tags. P w /\ (at_point cut w \/ w = u) /\
     !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (a,Ga,ta) tags (OK w,J,tj))`
    (DISJ_CASES_THEN (qx_choosel_then [`w`,`J`,`tj`,`tags`] (map_every assume_tac o CONJUNCTS)))
  >- (irule (BETA_RULE (Q.INST [`at_cut` |-> `\w. at_point cut w \/ w = u`,
      `safe` |-> `\i. ^default_opcode i.inst_opcode`] entry_replay_default_through_cut)) >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
     >- (rpt gen_tac >> strip_tac >> qpat_assum `!u bb i. _ ==> ~MEM _ _`
           (drule_at (Pat `get_instruction _ _ = SOME _`)) >>
         disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >> fs[Abbr `P`])
     >- (rpt strip_tac >> qpat_assum `!x y n. P x /\ _ ==> P y`
           (drule_at (Pat `gas_path_edge _ _ _ _ _`)) >> fs[])
     >> qexistsl_tac [`ARB`,`G`,`EMPTY`,`[]`,`OK u`,`tn`] >> simp[])
  >- (disj1_tac >> qexistsl_tac [`w`,`J`,`tj`,`tags`] >> asm_rewrite_tac[]) >>
  Cases_on `at_point cut w`
  >- (qpat_assum `!w. _ ==> fresh_vars_wrt entry w /\ _` (qspec_then `w` mp_tac) >>
      impl_tac >- fs[Abbr `P`] >> strip_tac >>
      disj2_tac >> qexistsl_tac [`w`,`J`,`tj`,`tags`] >> asm_rewrite_tac[]) >>
  `P u` by metis_tac[] >>
  Q.SUBGOAL_THEN `(?z J tj tags. z.vs_returndata = [] /\
     !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (u,G,tn) tags (Abort Revert_abort z,J,tj)) \/
   (?w J tj tags. P w /\ at_point cut w /\
     !D. gas_origin_ptr_path (D,0,EMPTY,ctx,fn,[]) (u,G,tn) tags (OK w,J,tj))`
    (DISJ_CASES_THEN (qx_choosel_then [`v`,`Kv`,`tk`,`ms`] (map_every assume_tac o CONJUNCTS)))
  >- (irule (BETA_RULE row22_real_initializer_replay) >>
      rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >> simp[Abbr `P`] >>
      first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [MEM]))
  >- (disj1_tac >> qexistsl_tac [`v`,`Kv`,`tk`,`ms`] >> simp[] >>
      metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  qpat_assum `!w. _ ==> fresh_vars_wrt entry w /\ _` (qspec_then `v` mp_tac) >>
  impl_tac >- fs[Abbr `P`] >> strip_tac >>
  disj2_tac >> qexistsl_tac [`v`,`Kv`,`tk`,`ms`] >> asm_rewrite_tac[] >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED
