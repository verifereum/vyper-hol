Theory bodyPtrPopTargetSimPost
Ancestors
  bodyPtrPopTargetDefs bodyPtrPopTargetSimAttributeAdd exprSimWordArgs assignTuplePtrLoadStep
  appendStorageGhostPtr bodyPtrEnvBuiltinsGhostCompose wordArgsPtr
  targetPlaceSimCasesBase stateFrame exprSimProps compileEnv loweringStateRelDefs venomState
  loweringPosts finite_map list

(* The operational and semantic parts of a target post are independent.
   Expose the existing wb_frame, rather than duplicate its composition proof. *)
Theorem target_post_wb_frame:
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s <=>
  stmt_state_rel ctx func cenv cx ee s /\
  (?w. eval_operand (FST r) s = SOME w /\
       place_ptr_rel cenv cx s pv w (FST (SND r)) vt) /\
  SND (SND r) = SOME (value_type_place vt) /\
  (!x. FST r = Var x ==> not_fresh_at sb x) /\
  place_readable cx ee pv /\ wb_frame cenv es ee sa s0 s
Proof
  simp[target_post_def, wb_frame_def]
QED

Theorem target_post_index_frame:
  target_post ctx func cenv cx es sa sm s0 em pv vt rb u /\
  expr_post ctx func cenv cx e em sm sn u ef v idx s /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
  wb_frame cenv es ef sa s0 s
Proof
  strip_tac >> imp_res_tac expr_post_frame >> fs[target_post_wb_frame] >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `sa`, `em`, `ef`, `sm`, `u`, `s`,
               `ctx`] mp_tac wb_frame_trans >> simp[]
QED

(* Child layout and source readability are deliberately supplied by the
   source selection boundary; neither follows just from the saved pointer. *)
Theorem target_post_readonly_suffix:
  wb_frame cenv es ef sa s0 s /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  stmt_state_rel ctx func cenv cx ef t /\
  eval_operand (FST r) t = SOME w /\
  place_ptr_rel cenv cx t child w (FST (SND r)) ty /\
  SND (SND r) = SOME (value_type_place ty) /\
  (!x. FST r = Var x ==> not_fresh_at sb x) /\
  place_readable cx ef child ==>
  target_post ctx func cenv cx es sa sb s0 ef child ty r t
Proof
  strip_tac >> simp[target_post_wb_frame] >>
  irule wb_frame_readonly_tail >>
  qexistsl_tac [`sn`, `s`] >> simp[]
QED

(* The suffix changes only fresh registers and the instruction cursor.
   Preserve both runtime relations without unfolding either invariant. *)
Theorem target_readonly_suffix_relations:
  stmt_state_rel ctx func cenv cx ef s /\
  ghost_inv d cenv cx ef G tn s /\ local_ptrs_reserved cenv sn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := pc|> /\
  (!x. not_fresh_at sn x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
     op_taint un (Var x) = op_taint tn (Var x)) /\
  un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
  un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm ==>
  stmt_state_rel ctx func cenv cx ef t /\ ghost_inv d cenv cx ef H un t
Proof
  strip_tac >> conj_tac
  >- (irule stmt_state_rel_old_vars_frame_ptr >>
      qexistsl_tac [`s`, `sn`] >> simp[] >>
      qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
      simp[state_frame_def]) >>
  irule ghost_inv_old_vars_frame_ptr >>
  qexistsl_tac [`G`, `s`, `sn`, `tn`] >> simp[] >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]
QED

(* Compiler-facing success boundary shared by all array layouts.  The saved
   operand is classified for the child by source selection, not readability
   of the pre-index parent.  All ghost effects here are fresh-register writes. *)
Theorem target_readonly_suffix_post_ptr:
  wb_frame cenv es ef sa s0 s /\
  stmt_state_rel ctx func cenv cx ef s /\ ghost_inv d cenv cx ef G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := pc|> /\
  (!x. not_fresh_at sn x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
     op_taint un (Var x) = op_taint tn (Var x)) /\
  un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
  un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
  eval_operand (FST r) t = SOME w /\
  place_ptr_rel cenv cx t child w (FST (SND r)) ty /\
  SND (SND r) = SOME (value_type_place ty) /\
  (!x. FST r = Var x ==> not_fresh_at sb x) /\ place_readable cx ef child /\
  target_ptr_ok cenv child rb G tn s /\
  op_taint un (FST r) = {} /\ op_prov H (FST r) = op_prov G (FST rb) ==>
  target_post ctx func cenv cx es sa sb s0 ef child ty r t /\
  ghost_inv d cenv cx ef H un t /\ target_ptr_ok cenv child r H un t /\
  ghost_kept cenv es sa G0 tn0 s0 H un
Proof
  strip_tac >> drule_all target_readonly_suffix_relations >> strip_tac >>
  conj_tac
  >- (irule target_post_readonly_suffix >> simp[] >>
      qexistsl_tac [`s`, `sn`] >> simp[] >>
      qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  simp[] >> conj_tac
  >- (irule target_ptr_ok_operand_transport >> simp[] >>
      qexistsl_tac [`G`, `rb`, `s`, `tn`] >> simp[] >>
      metis_tac[local_ptrs_reserved_def]) >>
  irule ghost_kept_suffix_compose >>
  qexistsl_tac [`G`, `sn`, `tn`] >> simp[]
QED
