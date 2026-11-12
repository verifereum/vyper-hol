(* Counted forcing of a value already located in memory. *)
Theory exprSimMemoryForce
Ancestors
  exprSimMemorySource exprSimMemoryPath exprSimMemoryRead
  exprSimUnwrapProps exprSimProps exprSimDefs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext gasStorage
  vyperStorageTrace vyperStorageFootprint valueEncodingProps valueCopyBytes
  fragGasPath fragGasMode emitHelperProps loweringPosts
  exprLowering exprLoweringProps compileEnv loweringSlice
  list rich_list finite_map pred_set fragExec varsExt freshWrites
  vyperAST vyperInterpreter vyperState vyperTypeSystem valueEncoding
  valueEncodingProofs venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* unwrap_memory_marked_read at every valid horizon, with one endpoint: the
   MLOAD address is the pointer operand's value in the start state. *)
Theorem unwrap_memory_marked_read_horizons:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!H. valid_horizon cx st0 H tr ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s) /\
  valid_horizon cx st0 H0 tr /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    (!H. valid_horizon cx st0 H tr ==>
       expr_post H ctx func cenv cx e es sa sb s0 ee v op u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_post H0 ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s` by
    metis_tac[] >>
  `(is_word_type t ==> t = post_value_type cenv e) /\
   ?w v. eval_operand p.ptr_operand s = SOME w /\
     read_result cx tv ee = (INL v,ee) /\
     (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
       val_in_memory tvt v (w2n w) s.vs_memory /\
       (is_word_type (post_value_type cenv e) ==>
        mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v))` by
    (qpat_x_assum `!H. _` kall_tac >>
     gvs[vv_post_def, vv_holds_def, is_bytestring_word_type]) >>
  `!H. valid_horizon cx st0 H tr ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[vv_post_read_result] >>
  `!u. gas_marked_path F ctx func s 0 (OK u) ==>
       gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s) [] (INL v) ee (OK u)` by
    (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  Cases_on `is_word_type t`
  >- (gvs[unwrap_memory_compile] >>
      qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var))
         (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
      `eval_operand op u = SOME (mload (w2n w) s) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
          lookup_var x u = SOME w') /\
       u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
        (qunabbrev_tac `u` >> irule emit_mload_endpoint >>
         simp[] >> qexists_tac `p.ptr_operand` >> simp[]) >>
      qexistsl_tac [`v`, `u`] >> conj_tac
      >- (first_x_assum irule >>
          drule_all emit_mload_marked_path >> simp[Abbr `u`]) >>
      simp[] >> qx_gen_tac `H1` >> strip_tac >>
      qpat_assum `!H. _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ (Value _) _ _`
        (qspec_then `H1` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      irule expr_post_of_vv_post_load_physical >>
      goal_assum (drule_at Any) >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> fs[GSYM mem_word_at_eq_mload]) >>
      conj_tac
      >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
          irule stmt_state_rel_update_var >>
          `stmt_state_rel H1 ctx func cenv cx ee s` by fs[vv_post_def] >>
          simp[] >> irule local_ptrs_reserved_fresh >>
          qexists_tac `sm` >> simp[]) >>
      qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]) >>
  gvs[unwrap_memory_compile, comp_return_def] >>
  qexistsl_tac [`v`, `s`] >> simp[] >> conj_tac
  >- (first_x_assum irule >> simp[gas_marked_path_def] >>
      irule (cj 1 gas_path_rules) >> simp[]) >>
  rpt strip_tac >> irule expr_post_of_vv_post_memory >> simp[] >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem expr_sim_of_vv_sim_memory:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa vv sm. compile_expr cenv ty e sa = (vv, sm) ==>
                sm = sa /\
                ?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `!sa vv sm. compile_expr _ _ _ _ = _ ==> _` drule >>
  strip_tac >> gvs[] >>
  drule_all unwrap_memory_extends >> strip_tac >>
  `fn_has_code sa sa func` by
    (irule (cj 1 fn_has_code_split) >> simp[cs_extends_refl] >>
     qexists_tac `sb` >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sa`, `LocatedValue t p`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_read_result]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `es_end`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >>
          simp[storage_trace_frame_read_result] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE)) >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >> BETA_TAC
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          first_assum (drule_then strip_assume_tac) >> gvs[] >>
          `~t'.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
          `!H. valid_horizon cx st0 H es_end.storage_trace ==>
             vv_post H ctx func cenv cx e es sa sa s0 (es_end with gas_obs := [])
               tv (LocatedValue t p) t'` by metis_tac[] >>
          drule_all unwrap_memory_marked_read_horizons >> strip_tac >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `expr_exit res r` by metis_tac[] >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  strip_tac >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[force_exempt_cert]
QED
