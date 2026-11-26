(* The linked value post at the successful EC packet's actual endpoint. *)
Theory bodyECArithSuccessVVMods
Ancestors
  bodyFullPostsMods bodyPtrPrecompileBuiltinsArithmeticValue
  exprSimCalldataSlice exprSimWordArgs wordArgsPtr exprSimProps
  bodyFullHashKeccakFixed exprLoweringProps loweringPosts loweringStateRelDefs
  vyperStorageFootprint vyperTypeSystem vyperValue vyperContext vyperState
  exprSimMemDefs valueEncoding venomInst venomState
  context compileEnv finite_map words pred_set list pair option
Libs
  markerLib

Theorem ec_result_stack_bounds_own[local]:
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  vv = StackValue a (Var dst) /\
  eval_operand (Var dst) t = SOME wo /\
  w2n wo + 64 <= t.vs_alloca_next /\
  FLOOKUP t.vs_allocas aid = SOME (w2n wo,64) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!n b sz. local_region cenv ee.scopes t n b sz ==>
    regions_disjoint (w2n wo) 64 b sz) ==>
  vv_store_bound cx a a ee (Value (mk_ec_result (rx,ry))) vv t /\
  vv_own cenv cx a sa sb ee (Value (mk_ec_result (rx,ry))) vv t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 2)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2))` by
    simp[evaluate_type_def, type_slot_size_def, wordsTheory.dimword_def,
         fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  conj_tac
  >- (simp[vv_store_bound_def, is_word_type_def, read_result_def, return_def,
       mk_ec_result_def, val_store_size_def, type_memory_size_def]) >>
  simp[vv_own_def, expr_val_own_def, is_word_type_def, read_result_def, return_def] >>
  disj1_tac >> qexistsl [`aid`,`w2n wo`,`64`] >>
  simp[mk_ec_result_def, val_footprint_def, type_memory_size_def,
       GSYM regions_disjoint_def] >> first_assum ACCEPT_TAC
QED

Theorem ec_arith_success_vv_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  vv = StackValue a (Var dst) /\
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\
  expr_post_mods H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
  expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= s2.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  wb_frame cenv es2 es2 s2 t2 u /\ pure_frame cenv func es2 s2 t2 u /\
  stmt_state_rel H ctx func cenv cx es2 u /\
  wb_frame cenv es2 ee s2 u t /\
  stmt_state_rel H ctx func cenv cx ee t /\
  ee.scopes = es2.scopes /\ ee.accounts = es2.accounts /\ ee.tStorage = es2.tStorage /\
  MEM (mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
  FLOOKUP u.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64) /\
  s2.cs_next_id <= out_alloc.cs_next_id /\ out_alloc.cs_next_id < sb.cs_next_id /\
  t.vs_allocas = u.vs_allocas /\ eval_operand (Var dst) t = SOME wo /\
  (!n b sz. local_region cenv es2.scopes u n b sz ==>
    regions_disjoint (w2n wo) 64 b sz) /\
  (!off len. regions_disjoint off len (w2n wo) 64 ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory) /\
  mem_bytes_at (w2n wo) 64 t.vs_memory =
    word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T /\
  w2n wo + 64 <= t.vs_alloca_next /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\
  s0.vs_alloca_next <= t1.vs_alloca_next /\ t1.vs_alloca_next <= t2.vs_alloca_next /\
  t2.vs_alloca_next <= u.vs_alloca_next /\ t.vs_alloca_next = u.vs_alloca_next /\
  immutable_frame_mods func cenv cx ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_covers G tn dst t 64 /\
  (!i. w2n wo <= i /\ i < w2n wo + 64 ==> i NOTIN tn.t_mem) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2 /\
  ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu /\
  ghost_kept_at lo cenv es2 s2 Gu tnu u G tn ==>
  ?tv. INL (Value (mk_ec_result (rx,ry))) = INL tv /\
    vv_post_mods H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee tv vv t /\
    vv_store_bound cx (post_value_type cenv (Builtin a bt [e1;e2]))
      (lowered_value_type cenv (Builtin a bt [e1;e2])) ee tv vv t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_vv_ok cx (post_value_type cenv (Builtin a bt [e1;e2])) tv vv ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) /\
        ~is_bytestring_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        vv_own cenv cx (post_value_type cenv (Builtin a bt [e1;e2])) sa sb ee tv vv t /\
        (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Builtin a bt [e1;e2])) = SOME rt /\
         eval_operand (vv_operand vv) t = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           val_in_memory rt val (w2n w) mem)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
      ptr_buf_ok cenv (Builtin a bt [e1;e2]) op G t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv (Builtin a bt [e1;e2]) p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `Value (mk_ec_result (rx,ry))` >>
  qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_post_mods_def]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_post_mods_def]) >>
  suspend "frame"
QED

Resume ec_arith_success_vv_mods[frame]:
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> decide_tac) >>
  qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
  `!n b sz. local_region cenv es2.scopes t2 n b sz <=>
            local_region cenv es2.scopes u n b sz` by
    (qpat_assum `wb_frame cenv es2 es2 s2 t2 u`
       (mp_then (Pat `wb_frame _ _ _ _ _ _`) irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions)) >>
     simp[] >> qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `!n b sz. local_region cenv es2.scopes u n b sz <=>
            local_region cenv ee.scopes t n b sz` by
    (qpat_assum `wb_frame cenv es2 ee s2 u t`
       (mp_then (Pat `wb_frame _ _ _ _ _ _`) irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions)) >>
     simp[] >> qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `!n b sz. local_region cenv es2.scopes t2 n b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (qpat_assum `!n b sz. local_region cenv es2.scopes t2 n b sz <=> _`
       (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `!n b sz. local_region cenv ee.scopes t n b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (qpat_assum `!n b sz. local_region cenv es2.scopes u n b sz <=> _`
       (pure_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es2 ee s2 t2 t` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
     >- (qexistsl [`es2`,`s2`,`u`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `pure_frame cenv func es2 s2 t2 t` by
    (irule pure_frame_buffer_tail >>
     qexistsl [`w2n wo`,`64`,`mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]`,`u`] >>
     simp[mk_inst_def] >> rpt conj_tac >>
     qpat_assum `ee.scopes = es2.scopes` (fn eq =>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [mk_inst_def,eq]))) >>
  `storage_well_formed_on cx ee (FST H)` by
    (mp_tac (Q.INST [`st'` |-> `ee`, `st` |-> `es2`,
         `regions` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`]
       (INST_TYPE [alpha |-> ``:256``] storage_well_formed_on_backends)) >> simp[]) >>
  suspend "value"
QED

Resume ec_arith_success_vv_mods[value]:
  `!c. bt <> Concat c` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >> simp[]) >>
  `post_value_type cenv (Builtin a bt [e1;e2]) = a /\
   lowered_value_type cenv (Builtin a bt [e1;e2]) = a` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >>
     simp[post_value_type_def, exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]) >>
  `FLOOKUP t.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64) /\
   sa.cs_next_id <= out_alloc.cs_next_id` by
    (conj_tac >- simp[] >> decide_tac) >>
  `ptr_val_ok cx a (mk_ec_result (rx,ry)) (Var dst) G tn t /\
   ptr_buf_ok cenv (Builtin a bt [e1;e2]) (Var dst) G t /\
   vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es2 s2 sb t2 ee
     (Value (mk_ec_result (rx,ry))) vv t /\
   ptr_vv_ok cx a (Value (mk_ec_result (rx,ry))) vv ee G tn t` by
    (qpat_assum `vv = StackValue a _` (pure_rewrite_tac o single) >>
     qpat_assum `a = ArrayT _ _` (pure_rewrite_tac o single) >>
     irule (SIMP_RULE (srw_ss()) [exprLoweringTheory.as_stack_val_def]
       ec_builtin_result_posts) >>
     simp[] >> qexists_tac `out_alloc.cs_next_id` >> simp[] >>
     qpat_assum `ee.scopes = es2.scopes` (fn eq =>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  `vv_store_bound cx a a ee (Value (mk_ec_result (rx,ry))) vv t /\
   vv_own cenv cx a sa sb ee (Value (mk_ec_result (rx,ry))) vv t` by
    (irule ec_result_stack_bounds_own >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`out_alloc.cs_next_id`,`dst`,`wo`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "prefix"
QED

Resume ec_arith_success_vv_mods[prefix]:
  qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
  qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
    (mp_then Any assume_tac expr_post_frame) >>
  qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
    (mp_then Any assume_tac expr_post_frame) >>
  `(~expr_has_effect (Builtin a bt [e1;e2]) ==> pure_frame cenv func es sa s0 t1) /\
   (~expr_has_effect (Builtin a bt [e1;e2]) ==> pure_frame cenv func es1 s1 t1 t2)` by
    (simp[] >> rpt strip_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es1 s1 sb t1 ee
     (Value (mk_ec_result (rx,ry))) vv t` by
    (qpat_assum `vv_post _ _ _ _ _ _ es2 s2 _ t2 _ _ _ _`
       (mp_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) irule vv_post_prefix_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee
     (Value (mk_ec_result (rx,ry))) vv t` by
    (qpat_assum `vv_post _ _ _ _ _ _ es1 s1 _ t1 _ _ _ _`
       (mp_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) irule vv_post_prefix_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "ghost"
QED

Resume ec_arith_success_vv_mods[ghost]:
  `ghost_kept_at lo cenv es2 s2 G2 tn2 t2 G tn` by
    (qpat_assum `ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu`
       (mp_then (Pos hd) irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans)) >>
     simp[] >> conj_tac >- (qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl [`es2`,`es2`,`u`,`s2`] >> simp[]) >>
  `ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G tn` by
    (qpat_assum `ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2`
       (mp_then (Pos hd) irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans)) >>
     simp[] >> conj_tac >- (qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl [`es2`,`es2`,`t2`,`s2`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
       (mp_then (Pos hd) irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans)) >>
     simp[] >> conj_tac >- (qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl [`es1`,`es1`,`t1`,`s1`] >> simp[]) >>
  suspend "finish"
QED

Resume ec_arith_success_vv_mods[finish]:
  `vv_post_mods H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee
     (Value (mk_ec_result (rx,ry))) vv t` by
    (qpat_assum `vv_post _ _ _ _ _ _ es sa _ s0 _ _ _ _` mp_tac >>
     qpat_assum `vv = StackValue a _` (pure_rewrite_tac o single) >>
     simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def, vv_place_ptr_mods_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee t`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  pure_rewrite_tac[sumTheory.INL_11] >>
  qpat_assum `post_value_type _ (Builtin _ _ _) = a` (pure_rewrite_tac o single) >>
  qpat_assum `lowered_value_type _ (Builtin _ _ _) = a` (pure_rewrite_tac o single) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    simp[contextTheory.vv_location_def, is_word_type_def, is_bytestring_type_def]) >>
  qpat_assum `a = ArrayT _ _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC
QED

Finalise ec_arith_success_vv_mods
