(* Actual counted scratch-allocation prefix, starting from the RHS post. *)
Theory annAssignPtrStage
Ancestors
 annAssignPtrScratch annAssignPtrSetup exprOperandVar exprSimProps
 stmtSimProps compileEnv loweringPosts finite_map fragGasPathPtr
 ptrDiscipline venomState venomInst venomExecSemantics bodyPtrDefs

Theorem annassign_static_stage_ptr:
 !ctx func cenv cx es st sm sn dst src k s0 sa d PG G0 tn0
   t ea eb tv v a.
 emit_inst ALLOCA [Lit (n2w k)] [dst] st = ((),sm) /\
 compile_copy_memory (Var dst) (Var src) k sm = ((),sn) /\
 stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
 MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w k)] [dst]) (fn_insts func) /\
 not_local_ptr cenv es.scopes dst /\ k < dimword (:256) /\
 ~not_fresh_at sa dst /\ local_ptrs_reserved cenv sa /\
 sa.cs_next_id <= st.cs_next_id /\ src <> dst /\
 (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> x <> dst) /\
 (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> x <> dst) /\
 fn_has_code st sm func /\ fn_has_code sm sn func /\
 ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
 s0.vs_current_bb = st.cs_current_bb /\
 s0.vs_inst_idx = LENGTH st.cs_current_insts /\
 ghost_inv d cenv cx es G0 tn0 s0 /\
 expr_val_at cenv cx t ea eb es v (Var src) s0 /\
 evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
 lookup_var src s0 = SOME a /\ ptr_covers G0 tn0 src s0 k /\
 val_wf tv v /\ val_footprint tv v <= k /\
 (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
 ?s G tn b.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G tn (OK s) /\
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_covers G tn dst s k /\
 lookup_var dst s = SOME b /\
 FLOOKUP s.vs_allocas st.cs_next_id = SOME (w2n b,k) /\
 s.vs_current_bb = sn.cs_current_bb /\
 s.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~s.vs_halted /\
 (!x. x <> dst ==> lookup_var x s = lookup_var x s0) /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_setup_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 drule_all annassign_alloca_source_transport_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 `ptr_covers G1 tn1 src s1 k /\ lookup_var src s1 = SOME a /\
  (!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
       val_in_memory tv v (w2n a) m)` by
   gvs[ptr_covers_def, lookup_var_def] >>
 `!n lo nsz. local_region cenv es.scopes s0 n lo nsz ==>
             local_region cenv es.scopes s1 n lo nsz` by
   (rpt strip_tac >> irule local_region_frame_fwd >>
    qexistsl [`s0`,`sa`,`es.scopes`] >> simp[] >>
    rpt strip_tac >> `x <> dst` by metis_tac[] >> metis_tac[]) >>
 qpat_x_assum `s1 = _ with vs_inst_idx := _` kall_tac >>
 qpat_x_assum `G1 = step_prov _ _ _ _` kall_tac >>
 qpat_x_assum `tn1 = step_taint _ _ _ _` kall_tac >>
 qpat_x_assum `step_inst_base _ _ = _` kall_tac >>
 qpat_x_assum `lookup_var src u = _` kall_tac >>
 qpat_x_assum `ptr_covers (step_prov _ _ _ _) _ _ _ _` kall_tac >>
 qpat_x_assum `!m. mem_agree_outside (step_taint _ _ _ _).t_mem _ _ ==> _` kall_tac >>
 qpat_x_assum `s1.vs_memory = _` kall_tac >>
 drule_at (Pat `MEM _ (fn_insts _)`) annassign_allocated_static_copy_ptr >>
 disch_then (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`) o SRULE [mk_inst_def]) >>
 simp[] >>
 disch_then drule_all >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 qexistsl [`s'`,`G1`,`tn'`,`w`] >> simp[] >>
 `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 (0+0)
   G1 tn' (OK s')` by
   (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >> fs[]
QED

(* The actual RHS interface supplies both the placement and freshness used
   above.  Staging reads the lowered source buffer, not the annotation size. *)
Theorem annassign_rhs_stage_input_ptr:
 !ctx func cenv cx e es ea eb s0 es1 v op s G tn dst tv k.
 expr_post ctx func cenv cx e es ea eb s0 es1 v op s /\
 lower_value compile_expr cenv (expr_type e) e ea = (op,eb) /\
 local_ptrs_reserved cenv ea /\ ~not_fresh_at eb dst /\
 evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv /\
 ~is_word_type (post_value_type cenv e) /\
 ptr_val_ok cx (post_value_type cenv e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
 k = type_memory_bytes cenv (lowered_value_type cenv e) /\ 0 < k /\
 k < dimword (:256) ==>
 ?src a. op = Var src /\ src <> dst /\ lookup_var src s = SOME a /\
 ptr_covers G tn src s k /\ val_wf tv v /\
 expr_val_at cenv cx (post_value_type cenv e) ea eb es1 v (Var src) s /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule compile_lower_value_var >> disch_then drule >> disch_tac >>
 `expr_val_at cenv cx (post_value_type cenv e) ea eb es1 v op s` by
   fs[expr_post_def] >>
 `val_wf tv v /\ ?w. eval_operand op s = SOME w` by
   (fs[expr_val_at_def] >> metis_tac[]) >>
 fs[ptr_buf_ok_def] >>
 qexists `w` >>
 gvs[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
 metis_tac[]
QED
