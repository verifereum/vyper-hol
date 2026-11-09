(* Scratch staging retains the allocation and local-region frames that the
   declaration destination needs, even though it is not yet a live local. *)
Theory annAssignPtrMemoryStageFrame
Ancestors
 annAssignPtrStage annAssignPtrMemorySource annAssignPtrBytestring
 annAssignPtrSetup annAssignPtrScratch
 stmtSimDeclMem stmtSimProps exprSimProps bodyPtrDefs compileEnv loweringStateRelDefs loweringPosts
 finite_map ptrDiscipline venomState venomInst venomExecSemantics fragGasPathPtr

Theorem annassign_static_stage_frame_ptr:
 !ctx func cenv cx es st sm sn dst src k s0 sa d PG G0 tn0 t ea eb tv v a.
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
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
              FLOOKUP s.vs_allocas aid = SOME entry) /\
 (!n lo sz. local_region cenv es.scopes s0 n lo sz ==>
            local_region cenv es.scopes s n lo sz) /\
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
 simp[] >> disch_then drule_all >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 `!n lo sz. local_region cenv es.scopes s0 n lo sz ==>
            local_region cenv es.scopes s' n lo sz` by
   (rpt strip_tac >> irule local_region_frame_fwd >>
    qexistsl [`s1`,`sa`,`es.scopes`] >> simp[] >> metis_tac[]) >>
 qexistsl [`s'`,`G1`,`tn'`,`w`] >> simp[] >>
 `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 (0+0)
   G1 tn' (OK s')` by
   (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >>
 fs[]
QED

Theorem annassign_memory_staged_source_ptr:
 !ctx func cenv cx es sa sb p cap w aid src a sty dty info bytes
  s0 d PG G0 tn0 t ea eb tv dtv v.
 compile_assign_value cenv (Var p) LocMemory (Var src) F (SOME LocMemory)
   dty sty info bytes sa = ((),sb) /\
 (sty = dty \/ is_bytestring_type dty) /\
 0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
 local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\ not_fresh_at sa src /\
 (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
 (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
 ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
 s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
 expr_val_at cenv cx t ea eb es v (Var src) s0 /\
 evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
 evaluate_type (get_tenv cx) dty = SOME dtv /\
 (t = dty \/ is_bytestring_type t /\ is_bytestring_type dty) /\
 value_has_type dtv v /\
 lookup_var src s0 = SOME a /\ ptr_covers G0 tn0 src s0 (type_memory_bytes cenv sty) /\
 val_wf tv v /\ val_footprint tv v <= type_memory_bytes cenv sty /\
 (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
 lookup_var p s0 = SOME w /\ ptr_covers G0 tn0 p s0 cap /\
 FLOOKUP s0.vs_allocas aid = SOME (w2n w,cap) ==>
 ?sn tmp s G tn b.
 compile_store_memory cenv (Var tmp) (Var p) dty dty sn = ((),sb) /\
 fn_has_code sn sb func /\ cs_extends sa sn /\
 sa.cs_next_var <= sn.cs_next_var /\ not_fresh_at sn tmp /\
 gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G tn (OK s) /\
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\
 lookup_var tmp s = SOME b /\ ptr_covers G tn tmp s (type_memory_bytes cenv sty) /\
 lookup_var p s = SOME w /\ ptr_covers G tn p s cap /\
 FLOOKUP s.vs_allocas aid = SOME (w2n w,cap) /\
 (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
 (!i entry. FLOOKUP s0.vs_allocas i = SOME entry ==> FLOOKUP s.vs_allocas i = SOME entry) /\
 (!n lo sz. local_region cenv es.scopes s0 n lo sz ==>
            local_region cenv es.scopes s n lo sz) /\
 s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
 ~s.vs_halted /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory dtv v (w2n b) m)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all annassign_staged_memory_widen_parts >>
 disch_then (qx_choosel_then [`sx`,`sm`,`sn`,`tmp`] strip_assume_tac) >>
 `MEM (mk_inst sx.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) (fn_insts func)` by
   (irule loweringHaltTheory.emit_inst_fn_member >> qexists `sm` >> simp[]) >>
 `not_local_ptr cenv es.scopes tmp` by
   (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
 `src <> tmp /\ p <> tmp` by metis_tac[] >>
 `compile_copy_memory (Var tmp) (Var src) (type_memory_bytes cenv sty) sm = ((),sn)` by
   (Cases_on `type_memory_bytes cenv sty` >> gvs[contextTheory.compile_copy_memory_def]) >>
 `s0.vs_current_bb = sx.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sx.cs_current_insts /\ sa.cs_next_id <= sx.cs_next_id` by simp[] >>
 `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> x <> tmp) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> x <> tmp)` by metis_tac[] >>
 drule_all annassign_static_stage_frame_ptr >>
 disch_then (qspec_then `PG` mp_tac) >>
 disch_then (qx_choosel_then [`s`,`G`,`tn`,`b`] strip_assume_tac) >>
 `ptr_covers G tn p s cap` by
   (irule annassign_declared_pointer_after_rhs_ptr >> metis_tac[]) >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory dtv v (w2n b) m` by
   (qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` mp_tac >>
    qpat_x_assum `evaluate_type _ t = _` mp_tac >>
    qpat_x_assum `evaluate_type _ dty = _` mp_tac >>
    qpat_x_assum `t = dty \/ _` mp_tac >>
    qpat_x_assum `value_has_type dtv v` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[annassign_robust_layout_transfer_ptr]) >>
 `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
 qexistsl [`sn`,`tmp`,`s`,`G`,`tn`,`b`] >> simp[] >> metis_tac[]
QED
