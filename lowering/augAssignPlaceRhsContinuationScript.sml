(* Counted forced-RHS execution with a memory-safe zero-observation suffix. *)
Theory augAssignPlaceRhsContinuation
Ancestors
  augAssignPlaceSuffixMemory exprSimMemDefs stmtSimForced
  gasOutcome gasSummary loweringPosts exprLowering
  bodyBinopFamiliesMemory bodyBinopFragMemory stmtSimAugAssignPlaceMemory
  vyperState exprSimWordArgs vyperStorageTrace vyperStorageFootprint
  vyperStoragePlaceObserved stmtSimAugAssign

(* Concrete, observation-free operator/write suffix.  Write success and its
   source replay are established by the memory or storage branch. *)
Theorem aug_place_operator_write_path_mem[local]:
  bop <> In /\ bop <> NotIn /\ word_value cur /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
    [ty;expr_type e] cur rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\
       storage_well_formed_on cx ee (FST H)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> storage_place_observed H p) /\
  alloca_history func s /\
  alloca_frame cenv es0 sa s_entry cenv ee s /\
  s_entry.vs_alloca_next <= s.vs_alloca_next /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type ty) /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type dtv v /\ ?ff. write_place cx p v ee = (INL (),ff) /\
      (!tail. write_place cx p v (ee with gas_obs := tail) =
        (INL (),ff with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ff.storage_trace ==>
           storage_well_formed_on cx ff (FST H))) /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\ ~block_is_terminated sf /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) ==>
  ?res ff r.
    (!tail. bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx p) (ee with gas_obs := tail) =
        (res,ff with gas_obs := tail)) /\
    gas_marked_path T ctx func s 0 r /\
    ((?u. r = OK u /\ res = INL () /\
      alloca_history func u /\ s_entry.vs_alloca_next <= u.vs_alloca_next /\
      (!H. valid_horizon cx st0 H ff.storage_trace ==>
           stmt_post H ctx func cx lctx cenv cenv sa sf es0 s_entry
             res (ff with gas_obs := []) u)) \/
     (exit_result r /\
      !H. valid_horizon cx st0 H ff.storage_trace ==>
          !tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r))
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule stmtSimAugAssignTheory.bop_result_augassign >> simp[] >>
     metis_tac[stmtSimAugAssignTheory.word_value_not_bytes]) >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`st0`, `s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac
  >- (qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
      rename1 `eval_operand op t = SOME (val_to_w256 v)` >>
      `stmt_state_rel H0 ctx func cenv cx ee s` by
        (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                          stmt_state_rel H _ _ _ _ ee s /\ _`
           (qspec_then `H0` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      `stmt_state_rel H0 ctx func cenv cx ee t` by
        (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                          stmt_state_rel H _ _ _ _ ee t /\ _`
           (qspec_then `H0` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      `alloca_frame cenv es0 sa s_entry cenv ee t` by
        (qspecl_then [`H0`, `cenv`, `es0`, `sa`, `s_entry`, `cenv`, `ee`, `s`,
                      `ctx`, `func`, `cx`, `s2`, `ee`, `t`] mp_tac
           augAssignPlaceWordStoreMemoryTheory.alloca_frame_memory_kept >>
         impl_tac >- (rpt conj_tac >> FIRST [REFL_TAC, first_assum ACCEPT_TAC]) >>
         simp[]) >>
      qpat_x_assum `!v. bop_result _ _ _ _ _ _ _ = INL v ==> _`
        (qspec_then `v` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      rename1 `write_place cx p v ee = (INL (),ff)` >>
      drule_all aug_place_word_store_after_operator_mem >> strip_tac >>
      `alloca_frame cenv es0 sa s_entry cenv (ff with gas_obs := []) u` by
        (`alloca_frame cenv es0 sa s_entry cenv ff u` by
           (qpat_x_assum `!c0 e0 sa0 sx. alloca_frame _ _ _ _ _ _ _ ==> _`
              irule >> first_assum ACCEPT_TAC) >>
         pop_assum mp_tac >> simp[stmtSimDefsTheory.alloca_frame_def]) >>
      `gas_marked_path T ctx func s 0 (OK u)` by
        (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
      `!z w. not_fresh_at sa z /\ lookup_var z s_entry = SOME w ==>
             lookup_var z u = SOME w` by metis_tac[] >>
      `!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b` by metis_tac[] >>
      `s_entry.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
      qexistsl_tac [`INL ()`, `ff`, `OK u`] >>
      conj_tac >- (Cases_on `evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur rhs` >>
        gvs[vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
            vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disj1_tac >> qexists_tac `u` >>
      rpt conj_tac >- REFL_TAC >- REFL_TAC >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      `valid_horizon cx st0 H ee.storage_trace` by
        (mp_tac (Q.INST [`f` |-> `write_place cx p v`, `st` |-> `ee`,
                         `res` |-> `INL ()`, `st'` |-> `ff`]
                   (INST_TYPE [alpha |-> ``:unit``]
                      vyperStorageFootprintTheory.valid_horizon_frame)) >>
         impl_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
         first_assum ACCEPT_TAC) >>
      `stmt_state_rel H ctx func cenv cx ee t` by
        (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                          stmt_state_rel H _ _ _ _ ee t /\ _`
           (qspec_then `H` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      `storage_place_observed H p` by
        (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                          storage_place_observed H p`
           (qspec_then `H` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      `stmt_state_rel H ctx func cenv cx ff u` by
        (qpat_assum `!H'. storage_place_observed H' p /\
                           stmt_state_rel H' ctx func cenv cx ee t ==> _`
           (qspec_then `H` mp_tac) >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      `storage_well_formed_on cx ff (FST H)` by
        (qpat_assum `!H. valid_horizon cx st0 H ff.storage_trace ==>
                          storage_well_formed_on cx ff (FST H)`
           (qspec_then `H` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      `storage_well_formed_on cx (ff with gas_obs := []) (FST H)` by
        (`(ff with gas_obs := []).accounts = ff.accounts /\
          (ff with gas_obs := []).tStorage = ff.tStorage` by simp[] >>
         metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
      irule aug_place_normal_post >>
      simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    ptv bop cur rhs`
  >- gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `_ = INR err` >>
  qexistsl_tac [`INR (Error err)`, `ee`, `r`] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rpt gen_tac >> strip_tac >> simp[stmtSimDefsTheory.stmt_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
  gvs[]
QED

Theorem aug_place_rhs_operator_write_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e s1 = (y,s2) /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\ word_value cur /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!z. dst = Var z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!l. x <> Label l /\ dst <> Label l) /\
  eval_operand x s0 = SOME (val_to_w256 cur) /\ eval_operand dst s0 = SOME w /\
  place_ptr_rel cenv cx s0 (PlaceR p) w (SOME loc) (Type ty) /\
  (loc = LocMemory ==> w2n w + 32 <= s0.vs_alloca_next) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  is_word_type (expr_type e) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_place_observed H p) /\
  alloca_history func s0 /\
  alloca_frame cenv es0 sa s_entry cenv es s0 /\ sa.cs_next_id <= s1.cs_next_id /\
  s_entry.vs_alloca_next <= s0.vs_alloca_next /\
  ~s0.vs_halted /\ s0.vs_current_bb = s1.cs_current_bb /\
  s0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~block_is_terminated sf /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s0 = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s0.vs_allocas aid = SOME b) /\
  (!rhs ee. ee.gas_obs = [] /\
     (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
           (INL rhs,ee)) ==>
     word_value rhs /\ expr_sim_inv cenv cx env ee /\
     binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
       [ty;expr_type e] cur rhs ee /\
     expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
     (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type dtv v /\ ?ff. write_place cx p v ee = (INL (),ff) /\
         (!tail. write_place cx p v (ee with gas_obs := tail) =
           (INL (),ff with gas_obs := tail)) /\
         (!H. valid_horizon cx st0 H ff.storage_trace ==>
              storage_well_formed_on cx ff (FST H)))) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))) (es,s0)
    (\H res ff u. res = INL () /\
      stmt_post H ctx func cx lctx cenv cenv sa sf es0 s_entry res ff u /\
      alloca_history func u /\ s_entry.vs_alloca_next <= u.vs_alloca_next)
    (\H res ff r. !tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r)
Proof
  strip_tac >>
  `!z. y = Var z ==> not_fresh_at s2 z` by
    (drule_all exprOperandVarTheory.compile_lower_value_var >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  `(!z. x = Var z ==> not_fresh_at s2 z) /\
   (!z. dst = Var z ==> not_fresh_at s2 z) /\
   (!z. not_fresh_at sa z ==> not_fresh_at s2 z)` by metis_tac[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `y`, `s0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  irule forced_then_outcome >>
  qexists_tac `\H v ee t. expr_post H ctx func cenv cx e es s1 s2 s0 ee v y t /\
    expr_store_bound cx (expr_type e) v y t /\
    t.vs_current_bb = s2.cs_current_bb /\
    t.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  BETA_TAC >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_lifts,
           vyperStorageTraceTheory.storage_trace_frame_write_place])
  >- suspend "callback"
  >- (rpt strip_tac >> simp[stmtSimDefsTheory.stmt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
        stmtSimPropsTheory.expr_exit_INR_type] >> simp[])
QED

Resume aug_place_rhs_operator_write_mem[callback]:
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> strip_tac >>
     mp_tac (Q.INST [`f` |-> `bind (eval_expr cx e) (read_result cx)`,
                     `st` |-> `es with gas_obs := gs`, `res` |-> `INL v`,
                     `st'` |-> `ee`]
               (INST_TYPE [alpha |-> ``:value``]
                  vyperStorageFootprintTheory.valid_horizon_frame)) >>
     impl_tac
     >- (conj_tac
         >- simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame] >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                    expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `!rhs ee. ee.gas_obs = [] /\ _ ==> _`
    (qspecl_then [`v`, `ee`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `eval_operand y t = SOME (val_to_w256 v)` by
    (drule_all expr_post_word_operand >> simp[]) >>
  `eval_operand x t = SOME (val_to_w256 cur) /\ eval_operand dst t = SOME w` by
    (conj_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     qexistsl_tac [`s1`, `s0`] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  `place_ptr_rel cenv cx t (PlaceR p) w (SOME loc) (Type ty)` by
    (Cases_on `p`
     >- fs[place_ptr_rel_def]
     >- (rename1 `PlaceR (MemoryPlace id path)` >>
         mp_tac (Q.INST [`sa` |-> `s1`, `s` |-> `t`, `loc` |-> `SOME loc`,
                         `vt` |-> `Type ty`] aug_place_memory_ptr_frame) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         strip_tac >> first_assum ACCEPT_TAC)
     >> fs[place_ptr_rel_def]) >>
  `loc = LocMemory ==> w2n w + 32 <= t.vs_alloca_next` by
    (strip_tac >>
     `w2n w + 32 <= s0.vs_alloca_next` by
       (qpat_assum `loc = LocMemory ==> w2n w + 32 <= s0.vs_alloca_next` mp_tac >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
        first_assum ACCEPT_TAC) >>
     decide_tac) >>
  `(!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
          lookup_var z t = SOME u) /\
   (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b)` by metis_tac[] >>
  `s_entry.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                      valid_horizon cx st0 H es.storage_trace`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
                      stmt_state_rel H _ _ _ _ es s0 /\ _`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es0 sa s_entry cenv ee t` by
    (`alloca_frame cenv es s1 s0 cenv ee t` by
       (mp_tac (Q.INST [`H` |-> `H0`, `sa` |-> `s1`, `sb` |-> `s2`,
                        `op` |-> `y`] stmtSimDefsTheory.expr_post_alloca_frame) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     irule stmtSimDefsTheory.alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ s0`)) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ t`)) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\
       storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                       expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rewrite_tac[expr_post_def] >> strip_tac >> conj_tac >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> storage_place_observed H p` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
                       storage_place_observed H p`
       (qspec_then `H` mp_tac) >>
     impl_tac
     >- (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                          valid_horizon cx st0 H es.storage_trace`
           (qspec_then `H` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         first_assum ACCEPT_TAC) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`s` |-> `t`, `rhs` |-> `v`] aug_place_operator_write_path_mem) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  strip_tac
  >- (qexistsl_tac [`res`, `ff`, `r`] >> BETA_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disj1_tac >> qexists_tac `u` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H ff.storage_trace ==>
                        stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`res`, `ff`, `r`] >> BETA_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H ff.storage_trace ==>
                        !tail. stmt_exit _ _ _ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> simp[])
QED

Finalise aug_place_rhs_operator_write_mem
