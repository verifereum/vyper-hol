(* Readonly scalar suffix endpoint transport; no execution assumptions. *)
Theory bodyFullConvertScalarFrame
Ancestors
  bodyFullGhostFrame bodyPtrDefs stateFrame assignTuplePtrLoadStep loweringPosts exprSimDefs
  exprLoweringProps exprSimProps loweringShapeDefs compileEnv vyperAST venomState

Theorem scalar_readonly_post[local]:
  expr_post H ctx func cenv cx e es sa s1 s0 ee v1 x t0 /\
  stmt_state_rel H ctx func cenv cx ee s /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
         lookup_var z s = SOME w) /\
  s.vs_allocas = t0.vs_allocas /\ s.vs_memory = t0.vs_memory /\
  is_word_type typ /\ sa.cs_next_var <= s1.cs_next_var ==>
  expr_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee v op s
Proof
  simp[expr_post_def, expr_type_def] >> strip_tac >>
  `locals_kept cenv es ee s0 s` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
  simp[expr_val_rel_def, expr_val_at_def] >> conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      metis_tac[]) >>
  `pure_frame cenv func es sa s0 s <=> pure_frame cenv func es sa s0 t0` by
    (irule pure_frame_state_cong >> asm_rewrite_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem scalar_convert_endpoint_frames:
  expr_post H ctx func cenv cx e es sa s1 s0 ee v1 x t0 /\
  ghost_inv_at D lo d cenv cx ee G tn t0 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  storage_well_formed_on cx ee (FST H) /\
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  local_ptrs_reserved cenv s1 /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at s1 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at s1 z) /\
  sa.cs_next_var <= s1.cs_next_var /\
  state_frame s = state_frame (t0 with vs_inst_idx := s.vs_inst_idx) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!z. not_fresh_at s1 z ==>
       lookup_var z s = lookup_var z t0 /\
       FLOOKUP Gf z = FLOOKUP G z /\
       op_taint tnf (Var z) = op_taint tn (Var z)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  op_taint tnf op = {} /\ op_prov Gf op = NONE ==>
  expr_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee v op s /\
  ghost_inv_at D lo d cenv cx ee Gf tnf s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf /\
  storage_well_formed_on cx ee (FST H) /\
  ptr_val_ok cx typ v op Gf tnf s /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `s = (t0 with vs_inst_idx := s.vs_inst_idx) with vs_vars := s.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  `s.vs_memory = t0.vs_memory /\ s.vs_allocas = t0.vs_allocas /\
   s.vs_alloca_next = t0.vs_alloca_next /\
   s.vs_call_ctx = t0.vs_call_ctx /\ s.vs_accounts = t0.vs_accounts /\
   s.vs_transient = t0.vs_transient /\
   s.vs_immutables = t0.vs_immutables` by
    (pop_assum SUBST1_TAC >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     qexistsl_tac [`t0`,`s1`] >> fs[expr_post_def] >> metis_tac[]) >>
  conj_tac
  >- (irule scalar_readonly_post >> metis_tac[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >> qexistsl_tac [`G`,`ee`,`t0`,`s1`,`tn`] >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` mp_tac >>
      pure_rewrite_tac [ghost_kept_at_def] >> strip_tac >>
      conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at s1 x'` by
            (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
          metis_tac[]) >>
      metis_tac[]) >>
  simp[ptr_val_ok_word]
QED
