(* Counted nonempty memory-local assignment, using the actual RHS endpoint. *)
Theory assignBasePtrLocalFragment
Ancestors assignBasePtrLocalFragmentSource assignBasePtrLocalAssign bodyPtrPreds stmtSimAssignMem
  stmtSimAssignSource stmtSimDeclMem bodySim bodyPtrDefs stmtFragPtr
  stmtLowering exprLoweringProps exprOperandVar gasSummaryComposePtr
  gasSummary gasExemptCert fragGasPathPtr fragGasPath fragGasMode gasOutcome list
  exprSimDefs exprSimProps exprSimHypsDefs loweringPosts compileEnv
  valueCopyBytes valueTypingMemoryProps finite_map words vyperState
  annAssignPtrMemorySource exprSimWordArgs stmtSimProps vyperLookup
Libs monadsyntax

Theorem compile_assign_local_memory_widen_stmt_frag_ptr:
  !d PG tops ctx func cx lctx RetQ cenv ty id e es p sz vtyp tyv etv ltv env.
    body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
    body_expr_ptr_ok cx e /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~is_word_type (expr_type e) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    ((vtyp = expr_type e /\ vtyp = lowered_value_type cenv e) \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e)) /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    type_memory_bytes cenv (expr_type e) = type_memory_size etv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    type_memory_size etv < 2 ** 64 /\
    type_memory_size ltv < dimword (:256) /\
    0 < type_memory_size etv /\ 0 < type_memory_size ltv /\
    (!gs v es1 entry.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v /\
       value_has_type etv v /\ value_has_type ltv v) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN ``lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp`` assume_tac
  >- (qpat_x_assum `(_ /\ _) \/ _` mp_tac >> metis_tac[]) >>
  drule_all assign_local_memory_widen_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule assign_local_admissible_rhs >> simp[]) >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ptr_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[] >>
  metis_tac[gas_exempt_cert_unforce_result]
QED

Resume compile_assign_local_memory_widen_stmt_frag_ptr[summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >>
  qpat_x_assum `res = INR ex` SUBST_ALL_TAC >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (drule assign_local_admissible_run >> strip_tac >>
      qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_ptr_def] >> strip_tac >>
      simp[bind_def]) >>
  disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assign_local_memory_widen_stmt_frag_ptr[normal]:
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v, es_end with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id es_end.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv /\ value_has_type tyv v /\
   value_has_type etv v /\ value_has_type ltv v` by
    (qpat_x_assum `!gs v es1 entry. _` irule >>
     qexistsl_tac [`es_end with gas_obs := []`, `gas_explicit marks s0.vs_gas_readings`] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by simp[] >>
  SUBGOAL_THEN ``expr_type e = lowered_value_type cenv e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e)``
    assume_tac >- metis_tac[] >>
  drule_all (annassign_memory_rhs_layout_ptr |> SPEC_ALL |>
    Q.INST [`typ` |-> `lowered_value_type cenv e`, `tyv` |-> `ltv`] ) >> strip_tac >>
  suspend "source"
QED

Resume compile_assign_local_memory_widen_stmt_frag_ptr[source]:
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `not_fresh_at sB src` by metis_tac[compile_lower_value_var] >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sB
    (es_end with gas_obs := []) v (Var src) t` by
    (irule assign_base_local_rhs_val_at >> conj_tac
     >- (qexists_tac `ltv` >> simp[]) >>
     qexistsl_tac [`expr_type e`, `etv`] >> simp[] >> fs[expr_post_def]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[is_bytestring_word_type] >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x)` by
    metis_tac[not_fresh_at_mono] >>
  `~t.vs_halted` by
    (drule gas_marked_exec_ptr_exec >> strip_tac >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by fs[expr_post_def] >>
  SUBGOAL_THEN ``vtyp = lowered_value_type cenv e \/
    is_bytestring_type vtyp /\ is_bytestring_type (lowered_value_type cenv e)``
    assume_tac >- metis_tac[] >>
  `find_containing_scope id (es_end with gas_obs := []).scopes =
    SOME (pre,env',entry,rest)` by simp[] >>
  `evaluate_type (get_tenv cx) vtyp = SOME entry.type /\
   value_has_type entry.type v /\
   type_memory_bytes cenv vtyp = type_memory_size entry.type /\
   type_memory_size entry.type + 64 < dimword (:256) /\
   ptr_covers G tn src t (type_memory_size ltv)` by
    (simp[] >> qpat_x_assum `ptr_covers G tn src t _` mp_tac >> simp[]) >>
  drule_all assign_base_local_memory_assign_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "compose"
QED

Resume compile_assign_local_memory_widen_stmt_frag_ptr[compose]:
  qabbrev_tac `ee = es_end with scopes :=
    pre ++ (env' |+ (id, entry with <|value := v; popped := []|>)) :: rest` >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) (write_place cx (MemoryPlace id [])))
    (es,s0,G0,tn0) marks (INL ()) ee Gf tf (OK u)` by
    (irule (SIMP_RULE std_ss [APPEND_NIL]
       (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
     qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v`] >>
     simp[gas_marked_exec_ptr_def, gas_explicit_def, Abbr `ee`]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (es,s0,G0,tn0) marks (INL ()) ee Gf tf (OK u)` by
    (drule assign_local_admissible_run >> strip_tac >>
     qpat_x_assum `gas_marked_exec_ptr _ _ _ (bind _ _) _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def]) >>
  qexistsl_tac [`INL ()`, `ee`, `Gf`, `tf`, `OK u`] >> simp[] >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  suspend "post"
QED

Resume compile_assign_local_memory_widen_stmt_frag_ptr[post]:
  `0 < type_memory_bytes cenv vtyp` by
    (qpat_x_assum `(_ /\ _) \/ _` mp_tac >> strip_tac
     >- (qpat_x_assum `vtyp = expr_type e` SUBST_ALL_TAC >> simp[]) >>
     metis_tac[bytestring_memory_bytes_positive]) >>
  conj_tac
  >- (drule_at (Pos last) compile_assign_value_memory_widen_open >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with <|scopes := _; gas_obs := _|>) u` mp_tac >>
      unabbrev_all_tac >>
      qmatch_goalsub_abbrev_tac `es_end with scopes := scs` >>
      `es_end with <|scopes := scs; gas_obs := []|> =
       (es_end with scopes := scs) with gas_obs := []` by
        simp[evaluation_state_component_equality] >>
      qpat_x_assum `es_end with <|scopes := scs; gas_obs := []|> = _`
        (fn th => pure_once_rewrite_tac [th]) >>
      simp[stmt_state_rel_gas_obs]) >>
  conj_tac
  >- (qpat_x_assum `ghost_inv _ _ _ (_ with <|scopes := _; gas_obs := _|>) _ _ u` mp_tac >>
      simp[Abbr `ee`, GSYM evaluation_state_accfupds]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!x. not_fresh_at sB x ==> _` drule >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `not_fresh_at sB x` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!x. not_fresh_at sB x ==> _` drule >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_def]
QED

Finalise compile_assign_local_memory_widen_stmt_frag_ptr
