(* Memory-safe operator execution with a successful-write callback. *)
Theory augAssignPlaceSuffixMemory
Ancestors
  augAssignPlaceRhsMemory augAssignPlaceWordStoreMemory
  stmtSimAugAssignPlaceMemory placeStore exprSimProps
  bodyBinopFamiliesMemory bodyBinopFragMemory
  stmtSimProps stmtSimDefs loweringPosts exprSimDefs gasOutcome gasSummary fragGasMode

Theorem aug_place_binop_write_callback_mem:
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE el tys cur rhs ee /\
  expr_res_ok (bop_result cx ty bop tys cur rhs ee) /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\
  stmt_state_rel ctx func cenv cx ee s /\ alloca_history func s /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  k ee = (res,ff) /\
  (!tail. k (ee with gas_obs := tail) = (res,ff with gas_obs := tail)) /\
  (!ex. bop_result cx ty bop tys cur rhs ee = INR ex ==> res = INR ex) /\
  (!v t. bop_result cx ty bop tys cur rhs ee = INL v /\ word_value v /\
     gas_marked_path T ctx func s 0 (OK t) /\
     stmt_state_rel ctx func cenv cx ee t /\
     eval_operand op t = SOME (val_to_w256 v) /\
     (!z w. not_fresh_at s2 z /\ lookup_var z s = SOME w ==>
            lookup_var z t = SOME w) /\
     (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
     t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
     t.vs_current_bb = s3.cs_current_bb /\
     t.vs_inst_idx = LENGTH s3.cs_current_insts /\
     alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next ==>
     ?u. gas_marked_path T ctx func t 0 (OK u) /\
         Q res (ff with gas_obs := []) u) ==>
  gas_outcome T (cx_tops cx) (ctx,func) k (ee,s) Q
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  strip_tac >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (gvs[] >>
      qpat_x_assum `!t. gas_marked_path _ _ _ _ _ _ /\ _ ==> _`
        (qspec_then `s''` mp_tac) >> simp[] >> strip_tac >>
      `gas_marked_path T ctx func s 0 (OK u)` by
        (drule_all gas_marked_path_then >> simp[]) >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def] >>
      qexistsl_tac [`res`, `ff`, `OK u`] >> simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`res`, `ff`, `r`] >> simp[] >>
  disj2_tac >> gen_tac >>
  Cases_on `bop_result cx ty bop tys cur rhs ee` >>
  gvs[expr_exit_def, stmt_exit_def] >> disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

(* Transport the saved destination and its numerical bound across the operator.
   The same adapter handles local memory, storage, and transient words. *)
Theorem aug_place_word_store_after_operator_mem:
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
  gas_marked_path T ctx func s 0 (OK t) /\
  (!z u. not_fresh_at s2 z /\ lookup_var z s = SOME u ==>
         lookup_var z t = SOME u) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type ty) /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  eval_operand op t = SOME (val_to_w256 v) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv v /\ word_value v /\ expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ storage_place_region cx p /\
  stmt_state_rel ctx func cenv cx ee t /\
  write_place cx p v ee = (INL (),ff) /\
  fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\ alloca_history func t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) ==>
  ?u. gas_marked_path T ctx func t 0 (OK u) /\
      stmt_state_rel ctx func cenv cx ff u /\
      (!z. not_fresh_at s3 z ==> lookup_var z u = lookup_var z t) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
      u.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next = u.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand dst t = SOME w` by
    (metis_tac[aug_place_saved_operand]) >>
  `place_ptr_rel cenv cx t (PlaceR p) w (SOME loc) (Type ty)` by
    (Cases_on `p`
     >- fs[place_ptr_rel_def]
     >- metis_tac[aug_place_memory_ptr_frame] >>
     fs[place_ptr_rel_def]) >>
  `expr_val_rel cx ty v op t` by
    simp[expr_val_rel_def, typed_val_to_w256_word_value] >>
  `!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (metis_tac[aug_place_store_entry_types]) >>
  `!z. dst = Var z ==> not_fresh_at s3 z` by metis_tac[] >>
  `(loc = LocMemory ==> w2n w + 32 <= t.vs_alloca_next)` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all place_store_word_run_mem >> simp[]
QED
