(* Scalar immutable suffix, framed against the original statement entry. *)
Theory immutableAugAssignSuffixMemory
Ancestors
  immutableAugAssignContinuation immutableAugAssignSourceContinuation
  immutableAugAssignRootWrite stmtSimDeclStore exprSimProps

Theorem immutable_augassign_scalar_suffix_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  expr_body_pre cenv cx env e es /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv cur /\ word_value cur /\
  cenv.ce_is_ctor /\ is_word_type ty /\
  FLOOKUP env.bare_global_assignable (cenv.ce_module,id) = SOME ty /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  off < dimword (:256) /\ ~block_is_terminated sf /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  type_memory_size tv = 32 /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_id <= s1.cs_next_id /\
  alloca_frame cenv es_entry sa s_entry cenv es s0 /\
  lower_value compile_expr cenv ty e s1 = (y,s2) /\
  compile_binop bop x y ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (op,s3) /\
  emit_void MSTORE [Lit (n2w off);op] s3 = ((),sf) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
  (!l. x <> Label l) /\
  eval_operand x s0 = SOME (val_to_w256 cur) /\
  w2n (n2w off : bytes32) + 32 <= s0.vs_alloca_next /\
  is_word_type (expr_type e) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  gas_admissible
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (\rhs. vyperState$bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur rhs)) (write_place cx (ImmutablePlace cenv.ce_module id []))))
    (stmt_res_ok lctx) es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = s1.cs_current_bb /\
  s0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  s_entry.vs_alloca_next <= s0.vs_alloca_next /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s0 = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s0.vs_allocas aid = SOME b) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (\rhs. vyperState$bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        tv bop cur rhs)) (write_place cx (ImmutablePlace cenv.ce_module id [])))) (es,s0)
    (\H res ff u. res = INL () /\
      stmt_post H ctx func cx lctx cenv cenv sa sf es_entry s_entry res ff u /\
      alloca_history func u /\ s_entry.vs_alloca_next <= u.vs_alloca_next)
    (\H res ff r.
      (!tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r) /\
      halt_exit H cx ff res r)
Proof
  strip_tac >>
  irule (immutable_augassign_rhs_mem |> SPEC_ALL |>
    Q.INST [`dst` |-> `Lit (n2w off)`, `w` |-> `n2w off`] |> GEN_ALL) >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_binop _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexists `off` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all immutable_augassign_rhs_source >> simp[]) >>
  (conj_tac >- (
  rpt strip_tac >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by
    fs[loweringPostsTheory.expr_post_def] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (rename1 `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL rhs,ee)` >>
     mp_tac (Q.INST [`H` |-> `H0`,
       `f` |-> `bind (eval_expr cx e) (read_result cx)`,
       `st` |-> `es with gas_obs := gs`, `res` |-> `INL rhs`, `st'` |-> `ee`]
       (INST_TYPE [alpha |-> ``:value``]
         vyperStorageFootprintTheory.valid_horizon_frame)) >>
     impl_tac
     >- (conj_tac
         >- simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame] >>
         conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  drule_all immutable_augassign_rhs_source >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  drule_all immutable_augassign_current_root >> strip_tac >>
  `FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ty` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[]) >>
  `value_has_type tv v` by metis_tac[] >>
  `store_lays_out tv tv v` by metis_tac[store_lays_out_typed] >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    metis_tac[typed_val_to_w256_word_value] >>
  `(!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
           lookup_var z t = SOME u) /\
   (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b)` by
    (fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `s_entry.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `alloca_frame cenv es s1 s0 cenv ee s` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >>
     simp[] >> strip_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.expr_post_alloca_frame) >>
     simp[] >> qexistsl_tac [`H0`, `ctx`, `cx`, `e`, `func`, `y`, `s2`, `rhs`] >>
     simp[]) >>
  `alloca_frame cenv es_entry sa s_entry cenv ee s` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `alloca_frame cenv es_entry sa s_entry cenv ee t` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       augAssignPlaceWordStoreMemoryTheory.alloca_frame_memory_kept) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`H0`, `ctx`, `cx`, `func`, `s2`] >>
     fs[loweringPostsTheory.expr_post_def]) >>
  irule immutable_augassign_root_write_callback >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[])) >>
  gvs[venomStateTheory.eval_operand_def]
QED
