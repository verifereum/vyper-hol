(* Arbitrary-state preparation: remove stale temporary bindings internally. *)
Theory exprSimExtract32Lift
Ancestors
  exprSimExtract32Post exprSimExtract32Assembly exprSimExtract32Read
  exprSimProps freshWrites varsExt loweringPosts exprLoweringProps
  compileEnv venomState venomExecSemantics finite_map list
  gasSummary fragGasMode vyperState

Theorem extract32_post_drop_fresh:
  expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at sm z) ==>
  expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op (drop_fresh sm s)
Proof
  strip_tac >>
  `eval_operand op (drop_fresh sm s) = eval_operand op s` by
    (irule eval_operand_drop_fresh >> simp[]) >>
  `!n b sz. local_region cenv es'.scopes (drop_fresh sm s) n b sz <=>
             local_region cenv es'.scopes s n b sz` by
    (rpt gen_tac >> simp[local_region_def] >>
     eq_tac >> strip_tac >> goal_assum (drule_at Any) >> simp[] >>
     `not_fresh_at sm p` by
       (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[lookup_var_drop_fresh]) >>
  `stmt_state_rel ctx func cenv cx es' (drop_fresh sm s)` by
    metis_tac[stmt_state_rel_drop_fresh, expr_post_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >> strip_tac >> simp[] >>
  conj_tac
  >- (gvs[expr_val_rel_def, drop_fresh_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[expr_val_at_def] >> simp[drop_fresh_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
      simp[lookup_var_drop_fresh] >> metis_tac[]) >>
  simp[drop_fresh_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  strip_tac >> match_mp_tac exprSimPropsTheory.pure_frame_mem_tail >>
  qexists_tac `s` >> simp[drop_fresh_def]
QED

Theorem extract32_post_vars_ext:
  expr_post ctx func cenv cx src es sa sb s0 es' (BytesV bs) op s /\
  local_ptrs_reserved cenv sb /\ varsExt$vars_ext s u ==>
  expr_post ctx func cenv cx src es sa sb s0 es' (BytesV bs) op u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (fs[vars_ext_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x w. lookup_var x s = SOME w ==> lookup_var x u = SOME w` by
    (gvs[vars_ext_def, lookup_var_def] >> metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  `!w. eval_operand op s = SOME w ==> eval_operand op u = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     rpt strip_tac >> drule eval_operand_vars_ext >>
     disch_then (qspec_then `op` mp_tac) >> simp[]) >>
  `local_ptrs_rel func cenv es'.scopes s` by
    gvs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  `!n b sz. local_region cenv es'.scopes u n b sz <=>
             local_region cenv es'.scopes s n b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (irule local_region_frame >>
         conj_tac >- (qexists_tac `func` >> simp[]) >>
         qexistsl_tac [`sb`,`es'.scopes`,`u`] >> simp[]) >>
     irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sb`,`es'.scopes`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es' u` by
    (irule stmt_state_rel_vars_ext >> qexists_tac `s` >> simp[] >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >> strip_tac >> simp[] >>
  conj_tac >- (gvs[expr_val_rel_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[expr_val_at_def] >> rpt strip_tac >>
      first_x_assum drule_all >>
      disch_then (mp_tac o CONJUNCT2) >>
      disch_then (qx_choose_then `w` strip_assume_tac) >>
      qexists_tac `w` >> simp[]
      >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
          first_assum MATCH_ACCEPT_TAC) >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`n`,`b`,`sz`] >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  strip_tac >> match_mp_tac pure_frame_mem_tail >> qexists_tac `s` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >- res_tac >> simp[]
QED

Theorem extract32_prepare_post_arbitrary:
  expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  compile_bytestring_src op sm = ((len,dp),sb) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var ==>
  ?u p. run_inst_seq (emitted_insts sm sb) s = OK u /\
    expr_post ctx func cenv cx src es sa sb s0 es' (BytesV bs) op u /\
    eval_operand op u = SOME (n2w p) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand dp u = SOME (n2w (p+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p u.vs_memory /\
    LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256)
Proof
  strip_tac >>
  `expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op
     (drop_fresh sm s)` by metis_tac[extract32_post_drop_fresh] >>
  `fresh_vars_wrt sm (drop_fresh sm s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all extract32_prepare_post >>
  disch_then (qx_choose_then `v` (qx_choose_then `p` strip_assume_tac)) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~is_ext_call_op i.inst_opcode) (emitted_insts sm sb)` by
    (drule_at (Pos (el 2)) extract32_read_code_shape >>
     simp[extract32_read_prepare] >> simp[EVERY_MEM]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sm sb) (drop_fresh sm s))
                   (run_inst_seq (emitted_insts sm sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >>
  rename1 `vars_ext v u` >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[] >>
     qspec_then `op` (qspec_then `sm` mp_tac) ci_mono_compile_bytestring_src >>
     simp[ci_mono_def]) >>
  `expr_post ctx func cenv cx src es sa sb s0 es' (BytesV bs) op u` by
    metis_tac[extract32_post_vars_ext] >>
  `u.vs_memory = v.vs_memory` by
    (fs[vars_ext_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x w. eval_operand x v = SOME w ==> eval_operand x u = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> rpt strip_tac >>
     drule eval_operand_vars_ext >> disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qexists_tac `p` >> simp[]
QED

Theorem extract32_prepare_counted_arbitrary:
  expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  compile_bytestring_src op sm = ((len,dp),sb) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u p. gas_marked_exec F (ctx,func) (return (BytesV bs)) (es',s) []
          (INL (BytesV bs)) es' (OK u) /\
    expr_post ctx func cenv cx src es sa sb s0 es' (BytesV bs) op u /\
    eval_operand op u = SOME (n2w p) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand dp u = SOME (n2w (p+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p u.vs_memory /\
    LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all extract32_prepare_post_arbitrary >>
  disch_then (qx_choose_then `u` (qx_choose_then `p` strip_assume_tac)) >>
  drule_all extract32_prepare_run_path >> strip_tac >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`p`] >>
  simp[] >>
  conj_tac
  >- simp[gas_marked_exec_def, vyperStateTheory.return_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, lookup_var_def, local_region_def, locals_kept_def] >>
  strip_tac >> simp[] >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
