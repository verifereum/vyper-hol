(* Select the Range suffix before the source handler forgets whether the
   body fell through or executed Continue. The landing is independent of H. *)
Theory bodyForRangeLandingMods
Ancestors
  bodyForRangeHeaderMods bodyFullForRange bodyFullIfExpReach bodyFullShared
  bodyMemoryDefs bodyFullPostsMods allocaHistory stmtSimDefs stmtSimProps
  exprLoweringProps loweringPosts bodyPtrDefs ptrDiscipline venomState
  venomInst fragGasOriginPtr fragExec integer_word bodyInvSplit loweringStateRelDefs
  bodyFullShadowBodyInv compileEnv

Theorem range_landing_immutable_jump[local]:
  immutable_frame_mods func cenv cx ee (jump_to lbl t) <=>
  immutable_frame_mods func cenv cx ee t
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       jump_to_def, local_region_def, lookup_var_def]
QED

Theorem range_landing_ghost_jump[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn (jump_to lbl t) <=>
  ghost_inv_at_mods D lo d cenv cx ee G tn t
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem range_landing_outer_jump[local]:
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t ==>
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn (jump_to lbl t)
Proof
  simp[range_outer_frame_mods_def] >> strip_tac >>
  `alloca_history func (jump_to lbl t)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `t` >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv ee (jump_to lbl t)` by
    (irule alloca_frame_same_state >> qexists_tac `t` >> simp[jump_to_def]) >>
  `allocas_below_fmp (jump_to lbl t) = allocas_below_fmp t` by
    simp[jump_to_def, allocas_below_fmp_def] >>
  simp[] >> simp[jump_to_def, lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem range_landing_classify[local]:
  stmt_lands (InLoop exit_lbl incr_lbl) sb raw t ==>
  raw = INL () \/ raw = INR BreakException \/ raw = INR ContinueException
Proof
  simp[stmt_lands_def] >> strip_tac >> simp[]
QED

Theorem range_body_landing_mods:
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 raw t /\ ~t.vs_halted /\
  (raw = INL () ==> ~block_is_terminated sb1) /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
    fn_has_code sb1 sj func) /\
  sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
  sb0.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok cenv sa t /\ return_buf_frame d cenv sb0 t /\
  return_buf_sep d cenv ee t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 t /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v) /\
  not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
  lookup_var cv u = SOME (i2w (n1 + &k)) /\ lookup_var ev u = SOME (i2w n2) /\
  lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p u sz /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
  (!x v. not_fresh_at sb0 x /\ lookup_var x u = SOME v ==> lookup_var x t = SOME v) /\
  (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sb0 x ==>
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) ==>
  let land = if raw = INL () then jump_to incr_lbl t else t in
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK land,G1,tn1) /\
    (if raw = INR BreakException then
       range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0 H ee G1 tn1 land
     else
       (raw = INL () \/ raw = INR ContinueException) /\
       land.vs_current_bb = incr_lbl /\ land.vs_inst_idx = 0 /\ ~land.vs_halted /\
       lookup_var cv land = SOME (i2w (n1 + &k)) /\ lookup_var ev land = SOME (i2w n2) /\
       lookup_var p land = SOME w /\ FLOOKUP land.vs_allocas aid = SOME (w2n w,sz) /\
       ptr_covers G1 tn1 p land sz /\
       op_taint tn1 (Var cv) = {} /\ op_prov G1 (Var cv) = NONE /\
       op_taint tn1 (Var ev) = {} /\ op_prov G1 (Var ev) = NONE /\
       stmt_state_rel H ctx func cenv cx ee land /\
       immutable_frame_mods func cenv cx ee land /\
       storage_well_formed_on cx ee (FST H) /\
       ret_pc_ok cenv sa land /\ return_buf_frame d cenv sb0 land /\
       return_buf_sep d cenv ee land /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 land /\
       (!fn inst v. frag_reachable ctx func land fn inst v ==> dalloca_fmp_headroom inst v) /\
       range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 land)
Proof
  strip_tac >> simp[LET_THM, NoAsms] >>
  qabbrev_tac `land = if raw = INL () then jump_to incr_lbl t else t` >>
  qpat_assum `stmt_lands (InLoop _ _) _ raw _`
    (assume_tac o MATCH_MP range_landing_classify) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK land,G1,tn1) /\
   land.vs_inst_idx = 0 /\ (raw = INR BreakException ==> t.vs_current_bb = exit_lbl) /\
   (raw <> INR BreakException ==> land.vs_current_bb = incr_lbl)` by
     suspend "path" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `raw = INR BreakException` >- suspend "break" >>
  suspend "increment"
QED

Resume range_body_landing_mods[path]:
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by fs[range_outer_frame_mods_def] >>
  simp[NoAsms, Abbr `land`] >>
  irule range_full_body_lands_path >> simp[] >> qexistsl_tac [`sb1`,`sj`] >> simp[]
QED

Resume range_body_landing_mods[break]:
  `land = t` by simp[Abbr `land`] >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ sb0 _`)) >> simp[]) >>
  gvs[range_done_mods_def, stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl]
QED

Resume range_body_landing_mods[increment]:
  `!x. lookup_var x land = lookup_var x t` by
    (Cases_on `raw = INL ()` >> simp[Abbr `land`, jump_to_def, lookup_var_def]) >>
  `land.vs_allocas = t.vs_allocas /\ ~land.vs_halted` by
    (Cases_on `raw = INL ()` >> simp[Abbr `land`, jump_to_def]) >>
  `!x v. not_fresh_at sb0 x /\ lookup_var x u = SOME v ==> lookup_var x land = SOME v` by
    simp[] >>
  `FLOOKUP land.vs_allocas aid = SOME (w2n w,sz)` by
    (simp[] >> first_x_assum irule >> simp[]) >>
  `ptr_covers G1 tn1 p land sz` by suspend "slot" >>
  `op_taint tn1 (Var cv) = {} /\ op_prov G1 (Var cv) = NONE /\
   op_taint tn1 (Var ev) = {} /\ op_prov G1 (Var ev) = NONE` by suspend "counters" >>
  `!fn inst v. frag_reachable ctx func land fn inst v ==> dalloca_fmp_headroom inst v` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK land,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `!fn inst v. frag_reachable ctx func t fn inst v ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  `lookup_var cv land = SOME (i2w (n1 + &k)) /\
   lookup_var ev land = SOME (i2w n2) /\ lookup_var p land = SOME w` by
    (rpt conj_tac >> qpat_assum `!x v. _ ==> lookup_var x land = SOME v` irule >> simp[]) >>
  qpat_x_assum `raw = INL () \/ _` mp_tac >> simp[] >> suspend "physical"
QED

Resume range_body_landing_mods[slot]:
  `lookup_var p land = lookup_var p u` by
    (simp[] >> qpat_assum `!x v. _ ==> lookup_var x land = SOME v` irule >> simp[]) >>
  qpat_assum `!x. not_fresh_at sb0 x ==> _` (qspec_then `p` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `ptr_covers G tn p u sz` mp_tac >> asm_rewrite_tac[ptr_covers_def]
QED

Resume range_body_landing_mods[counters]:
  qpat_assum `!x. not_fresh_at sb0 x ==> _` (qspec_then `cv` mp_tac) >>
  qpat_assum `!x. not_fresh_at sb0 x ==> _` (qspec_then `ev` mp_tac) >>
  gvs[op_prov_def]
QED

Resume range_body_landing_mods[physical]:
  Cases_on `raw = INL ()` >>
  gvs[Abbr `land`, stmt_state_rel_jump_to, range_landing_immutable_jump,
      ret_pc_ok_jump_to, return_buf_frame_jump_to, return_buf_sep_jump,
      range_landing_ghost_jump, range_landing_outer_jump] >>
  rpt strip_tac >> first_assum (drule_then ACCEPT_TAC)
QED

Finalise range_body_landing_mods
