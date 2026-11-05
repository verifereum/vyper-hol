Theory bodyPtrTypeBuiltinsIndexContinue
Ancestors
  bodyPtrTypeBuiltinsIndexEntry bodyPtrTypeBuiltinsSavedOperand
  bodyPtrTypeBuiltinsSourceCompile bodyPtrTypeBuiltinsSourceFrame gasSummaryComposePtr
  exprSimSource exprSimHypsDefs loweringPosts bodyPtrDefs exprSimProps exprBopSimProps
  compileEnv exprLoweringProps venomState venomExecSemantics vyperState
Libs
  monadsyntax

Theorem expr_val_at_readonly_end_frame:
  !cenv cx ty sa sb es v op s sc t.
    expr_val_at cenv cx ty sa sb es v op s /\
    sb.cs_next_id <= sc.cs_next_id /\
    (!w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\
    (!n b sz. local_region cenv es.scopes t n b sz <=>
              local_region cenv es.scopes s n b sz) ==>
    expr_val_at cenv cx ty sa sc es v op t
Proof
  simp[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]
QED

Theorem type_builtin_second_expr_sim_ptr_read:
  !cx src idx es v es1 tops ctx cenv env ann tb typ d PG func ty.
    body_exprs_ptr_ok cx [src;idx] /\
    vyperState$bind (eval_expr cx src) (read_result cx) es = (INL v,es1) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TypeBuiltin ann tb typ [src;idx]) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty idx es1
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_arg >> conj_tac
     >- gvs[expr_body_pre_def] >>
     qexistsl_tac [`ann`,`[src;idx]`,`es`,`tb`,`typ`] >> simp[]) >>
  drule expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`,`es1`] mp_tac) >>
  simp[vyperStateTheory.bind_def] >> strip_tac >>
  irule type_builtin_second_expr_sim_ptr >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`ann`,`env`,`es`,`src`,`tb`,`typ`,`v`] >> simp[] >>
  gvs[vyperStateTheory.bind_def]
QED

Theorem saved_source_index_outcome:
  !d ctx PG func cenv cx ty idx es sc iop sd s G tn env sty sa sv sop.
    expr_sim_ptr d ctx PG func cenv cx ty idx es /\
    lower_value compile_expr cenv ty idx sc = (iop,sd) /\
    fn_has_code sc sd func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sc /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
    gas_admissible (vyperState$bind (eval_expr cx idx) (read_result cx)) expr_res_ok es /\
    stmt_state_rel ctx func cenv cx es s /\
    ghost_inv d cenv cx es G tn s /\ ~s.vs_halted /\
    s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    expr_sim_inv cenv cx env es /\
    expr_val_at cenv cx sty sa sc es sv sop s /\ ~is_word_type sty /\
    (!tv. evaluate_type (get_tenv cx) sty = SOME tv ==> dynarray_free tv) /\
    ptr_mem_ok cx sty sv sop G tn s /\
    (!x. sop = Var x ==> not_fresh_at sc x) /\ (!l. sop <> Label l) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (vyperState$bind (eval_expr cx idx) (read_result cx)) (es,s,G,tn)
      (\res ee G' tn' t. ?iv. res = INL iv /\
        expr_post ctx func cenv cx idx es sc sd s ee iv iop t /\
        t.vs_current_bb = sd.cs_current_bb /\
        t.vs_inst_idx = LENGTH sd.cs_current_insts /\
        ghost_inv d cenv cx ee G' tn' t /\
        ptr_val_ok cx (expr_type idx) iv iop G' tn' t /\
        (~is_word_type (expr_type idx) ==> ptr_buf_ok cenv idx iop G' t) /\
        ghost_kept cenv es sc G tn s G' tn' /\
        ptr_mem_ok cx sty sv sop G' tn' t)
      (\res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (qspecl_then [`sc`,`sd`,`iop`,`s`,`G`,`tn`] mp_tac) >>
  simp[] >> strip_tac >>
  drule gas_outcome_ptr_conseq >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `v` >> simp[] >>
  irule saved_ptr_mem_ok >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem source_prefix_saved_entry:
  !ctx func cenv cx src es0 sa sb s0 es sv p s sc t G tn G' tn'.
    expr_post ctx func cenv cx src es0 sa sb s0 es sv (Var p) s /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb p /\
    sb.cs_next_id <= sc.cs_next_id /\
    t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    (!z. not_fresh_at sb z ==> lookup_var z t = lookup_var z s /\
         FLOOKUP G' z = FLOOKUP G z) /\
    ptr_mem_ok cx (expr_type src) sv (Var p) G tn s ==>
    stmt_state_rel ctx func cenv cx es t /\
    expr_val_at cenv cx (expr_type src) sa sc es sv (Var p) t /\
    ptr_mem_ok cx (expr_type src) sv (Var p) G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s` by gvs[expr_post_def] >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`s`,`sb`] >> simp[]) >>
  `!n b sz. local_region cenv es.scopes t n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >>
         conj_tac
         >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl_tac [`sb`,`es.scopes`,`t`] >> simp[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sb`,`es.scopes`] >> simp[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (irule expr_val_at_readonly_end_frame >>
      qexistsl_tac [`s`,`sb`] >> simp[eval_operand_def] >>
      conj_tac
      >- (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      gvs[expr_post_def]) >>
  gvs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]
QED

Theorem compile_bytestring_src_saved_entry:
  !ctx func cenv cx src es0 sa sb s0 es sv p s sc t G tn G' tn' len data.
    expr_post ctx func cenv cx src es0 sa sb s0 es sv (Var p) s /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb p /\
    compile_bytestring_src (Var p) sb = ((Var len,Var data),sc) /\
    t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    (!z. z <> len /\ z <> data ==> lookup_var z t = lookup_var z s /\
         FLOOKUP G' z = FLOOKUP G z) /\
    ptr_mem_ok cx (expr_type src) sv (Var p) G tn s ==>
    stmt_state_rel ctx func cenv cx es t /\
    expr_val_at cenv cx (expr_type src) sa sc es sv (Var p) t /\
    ptr_mem_ok cx (expr_type src) sv (Var p) G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_bytestring_src_shape_fresh >> strip_tac >> gvs[] >>
  `sb.cs_next_id <= sc.cs_next_id` by
    (qspec_then `Var p` (qspec_then `sb` mp_tac) ci_mono_compile_bytestring_src >>
     simp[ci_mono_def]) >>
  irule source_prefix_saved_entry >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
