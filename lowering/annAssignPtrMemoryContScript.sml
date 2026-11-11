(* Normal expression outcomes continue at the actual counted copy endpoint.
   fr is the pre-allocation frame frontier, sa the RHS start, sb the copy start. *)
Theory annAssignPtrMemoryCont
Ancestors
 annAssignPtrMemoryDispatch annAssignPtrWordCont annAssignPtrCompose
 annAssignPtrMemorySource stmtSimDeclSource stmtSimDeclCompose stmtSimDeclMem
 exprOperandVar exprSimProps exprSimDefs stmtFragPtr valueCopyBytes
 valueTypingMemoryProps loweringPosts bodyPtrDefs stmtLowering compileEnv
 gasSummaryComposePtr fragGasPathPtr fragGasPath finite_map list
 exprLoweringProps vyperState arithmetic exprSimWordArgs
Libs monadsyntax

Theorem annassign_memory_source_footprint_ptr:
 !tenv t sty tv stv v.
 (t = sty \/ is_bytestring_type t /\ is_bytestring_type sty) /\
 evaluate_type tenv t = SOME tv /\ evaluate_type tenv sty = SOME stv /\
 value_has_type tv v /\ value_has_type stv v ==>
 val_footprint tv v <= type_memory_size stv
Proof
 rpt gen_tac >> strip_tac >> Cases_on `t = sty`
 >- gvs[value_has_type_memory_wf, val_footprint_le] >>
 irule bytestring_val_footprint_le >> metis_tac[]
QED

Theorem annassign_memory_normal_continuation_ptr:
 !ctx func old c cx lctx id typ tyv e es etv ltv sa0 st sa sb sf salloc
   marks v ee s op p sz w inst loc info bytes fr d PG Ga tna G tn.
 declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
 (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
 ~is_word_type typ /\ ~is_word_type (expr_type e) /\ ~c.ce_is_ctor /\
 (expr_type e = typ \/ is_bytestring_type (expr_type e) /\ is_bytestring_type typ) /\
 (lowered_value_type c e = typ \/
   is_bytestring_type (lowered_value_type c e) /\ is_bytestring_type typ) /\
 (expr_type e = lowered_value_type c e \/
   is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type c e)) /\
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
 evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME ltv /\
 type_memory_bytes c typ = type_memory_size tyv /\ type_memory_size tyv <= sz /\
 type_memory_bytes c (lowered_value_type c e) = type_memory_size ltv /\
 0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256) /\
 (!gs v es1. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1) ==>
    value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v) /\
 local_ptrs_reserved c sa /\ local_ptrs_reserved c sb /\ cs_extends sa sb /\
 (!q n. c.ce_return_buf = SOME (PtrVar (Var q) n) ==> not_fresh_at sa q) /\
 (!q n. c.ce_return_pc = SOME (PtrVar (Var q) n) ==> not_fresh_at sa q) /\
 (!q. not_fresh_at fr q ==> not_fresh_at sa q) /\
 fr.cs_next_id <= sa.cs_next_id /\ fr.cs_next_id <= inst.inst_id /\
 lower_value compile_expr c (expr_type e) e sa = (op,sb) /\
 compile_assign_value c (Var p) LocMemory op F loc typ
   (lowered_value_type c e) info bytes sb = ((),sf) /\
 fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
 lookup_var p salloc = SOME w /\ ptr_covers Ga tna p salloc sz /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
   (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna)
   marks (INL v) ee G tn (OK s) /\
 expr_post ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op s /\
 s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ghost_inv d c cx (ee with gas_obs := []) G tn s /\
 ghost_kept c es sa Ga tna salloc G tn /\
 ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok c e op G s ==>
 ?ff u Gf tnf.
 gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (new_variable id tyv v)
   (ee with gas_obs := [],s,G,tn) [] (INL ()) ff Gf tnf (OK u) /\
 (?cenv''. stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\
   (~block_is_terminated sf /\ cenv'' = c) /\
   cenv_top_ext old cenv'' ff.scopes /\
   stmt_state_rel ctx func cenv'' cx ff u /\ ghost_inv d cenv'' cx ff Gf tnf u /\
   (!x z. not_fresh_at fr x /\ lookup_var x salloc = SOME z ==> lookup_var x u = SOME z) /\
   (!x. not_fresh_at fr x ==> FLOOKUP Gf x = FLOOKUP Ga x /\
      op_taint tnf (Var x) = op_taint tna (Var x)))
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `!tail. bind (eval_expr cx e) (read_result cx)
   (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
 `~s.vs_halted` by
   (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[gas_marked_exec_ptr_def] >> strip_tac >>
    drule gas_path_ptr_erase >> strip_tac >> drule gas_path_normal >> simp[]) >>
 drule_all annassign_continuation_all_tails >> strip_tac >>
 `value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v` by
   (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
 `0 < type_memory_bytes c (lowered_value_type c e)` by simp[] >>
 drule_all (annassign_memory_rhs_layout_ptr |> SPEC_ALL |>
   Q.INST [`typ` |-> `expr_type e`, `tyv` |-> `etv`] |> SRULE []) >>
 disch_then (qx_choosel_then [`src`,`a`] strip_assume_tac) >>
 qpat_x_assum `op = Var src` SUBST_ALL_TAC >> suspend "copy"
QED

Resume annassign_memory_normal_continuation_ptr[copy]:
 markerLib.RESUME_TAC >>
 `not_local_ptr c (ee with gas_obs := []).scopes p` by
   (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
 `cenv_top_ext old c
   ((sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)` by
   (irule cenv_top_ext_declare_local >> simp[] >>
    qexistsl [`id`,`sa0`,`st`,`typ`] >> gvs[lookup_scopes_def, AllCaseEqs()]) >>
 `val_footprint etv v <= type_memory_bytes c (lowered_value_type c e)` by
   (asm_rewrite_tac[] >> irule annassign_memory_source_footprint_ptr >> metis_tac[]) >>
 `lookup_var p s = SOME w /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  stmt_state_rel ctx func c cx (ee with gas_obs := []) s /\
  expr_val_at c cx (expr_type e) sa sb (ee with gas_obs := []) v (Var src) s` by
   (fs[expr_post_def] >> metis_tac[]) >>
 `FLOOKUP G p = FLOOKUP Ga p /\ op_taint tn (Var p) = op_taint tna (Var p)` by
   (qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
    simp[ghost_kept_def] >> metis_tac[]) >>
 `ptr_covers G tn p s sz` by
   (qpat_x_assum `ptr_covers Ga tna p salloc sz` mp_tac >>
    simp[ptr_covers_def] >> metis_tac[]) >>
 `not_fresh_at sb src` by
   (drule compile_lower_value_var >> disch_then drule >> simp[]) >>
 drule (cj 2 compile_expr_grows) >> strip_tac >>
 `not_fresh_at sb p /\ fr.cs_next_id <= sb.cs_next_id /\
  (!q. not_fresh_at fr q ==> not_fresh_at sb q)` by
   (rpt conj_tac >- metis_tac[stmtFragPtrTheory.not_fresh_at_mono]
    >- decide_tac >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
 `(!x n. c.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sb x) /\
  (!x n. c.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sb x)` by
   metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
 `~block_is_terminated sf` by
   (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac compile_assign_value_memory_widen_open) >>
    metis_tac[bytestring_memory_bytes_positive]) >>
 `?u Gf tnf.
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK u) /\
  u.vs_current_bb = sf.cs_current_bb /\ u.vs_inst_idx = LENGTH sf.cs_current_insts /\
  ~u.vs_halted /\
  stmt_state_rel ctx func c cx
   ((ee with gas_obs := []) with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) u /\
  ghost_inv d c cx
   ((ee with gas_obs := []) with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) Gf tnf u /\
  ghost_kept c (ee with gas_obs := []) fr G tn s Gf tnf /\
  (!q. not_fresh_at fr q ==> lookup_var q u = lookup_var q s) /\
  ptr_covers Gf tnf p u sz` by suspend "endpoint" >>
 suspend "post"
QED

Resume annassign_memory_normal_continuation_ptr[endpoint]:
 markerLib.RESUME_TAC >> gns[] >> irule annassign_memory_assignment_location_ptr >>
 simp[] >> conj_tac
 >- (qexists `inst` >> simp[]) >>
 goal_assum (drule_at Any) >> simp[] >>
 goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
 simp[] >> metis_tac[]
QED

Resume annassign_memory_normal_continuation_ptr[post]:
 markerLib.RESUME_TAC >>
 qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func c cx
   (ee with <|scopes := scs; gas_obs := []|>) u` >>
 `ee with <|scopes := scs; gas_obs := []|> =
  (ee with scopes := scs) with gas_obs := []` by
   simp[evaluation_state_component_equality] >>
 `stmt_state_rel ctx func c cx (ee with scopes := scs) u` by
   metis_tac[stmt_state_rel_gas_obs] >>
 `ghost_inv d c cx (ee with scopes := scs) Gf tnf u` by
   metis_tac[ghost_inv_gas_obs] >>
 qpat_x_assum `ee with <|scopes := scs; gas_obs := []|> = _` kall_tac >>
 unabbrev_all_tac >>
 qexistsl [`ee with <|gas_obs := []; scopes :=
   (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest|>`,
   `u`,`Gf`,`tnf`] >> conj_tac
 >- simp[gas_marked_exec_ptr_def] >>
 qexists `c` >>
 gns[stmt_lands_def, stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
 conj_tac
 >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> metis_tac[]) >>
 qpat_x_assum `ghost_kept c es sa Ga tna salloc G tn`
   (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >>
 qpat_x_assum `ghost_kept c _ fr G tn s Gf tnf`
   (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >>
 metis_tac[]
QED

Finalise annassign_memory_normal_continuation_ptr

Theorem annassign_memory_concrete_rhs_outcome_ptr:
 !ctx func old c cx lctx RetQ id typ tyv e es etv ltv sa0 st sa sb sf salloc
   op p sz w inst loc info bytes fr d PG Ga tna.
 declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
 (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
 ~is_word_type typ /\ ~is_word_type (expr_type e) /\ ~c.ce_is_ctor /\
 (expr_type e = typ \/ is_bytestring_type (expr_type e) /\ is_bytestring_type typ) /\
 (lowered_value_type c e = typ \/
   is_bytestring_type (lowered_value_type c e) /\ is_bytestring_type typ) /\
 (expr_type e = lowered_value_type c e \/
   is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type c e)) /\
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
 evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME ltv /\
 type_memory_bytes c typ = type_memory_size tyv /\ type_memory_size tyv <= sz /\
 type_memory_bytes c (lowered_value_type c e) = type_memory_size ltv /\
 0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256) /\
 (!gs v es1. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1) ==>
    value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v) /\
 local_ptrs_reserved c sa /\ local_ptrs_reserved c sb /\ cs_extends sa sb /\
 (!q n. c.ce_return_buf = SOME (PtrVar (Var q) n) ==> not_fresh_at sa q) /\
 (!q n. c.ce_return_pc = SOME (PtrVar (Var q) n) ==> not_fresh_at sa q) /\
 (!q. not_fresh_at fr q ==> not_fresh_at sa q) /\
 fr.cs_next_id <= sa.cs_next_id /\ fr.cs_next_id <= inst.inst_id /\
 lower_value compile_expr c (expr_type e) e sa = (op,sb) /\
 compile_assign_value c (Var p) LocMemory op F loc typ
   (lowered_value_type c e) info bytes sb = ((),sf) /\
 fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
 lookup_var p salloc = SOME w /\ ptr_covers Ga tna p salloc sz /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
   (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna)
   (\res ee G tn s. ?v. res = INL v /\
     expr_post ctx func c cx e es sa sb salloc ee v op s /\
     s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv d c cx ee G tn s /\ ptr_val_ok cx (expr_type e) v op G tn s /\
     (~is_word_type (expr_type e) ==> ptr_buf_ok c e op G s) /\
     ghost_kept c es sa Ga tna salloc G tn)
   (\res ee gt r. expr_exit res r) ==>
 gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
   (eval_stmt cx (AnnAssign id typ e)) (es,salloc,Ga,tna)
   (\res ee G tn s. ?cenv''.
     stmt_lands lctx sf res s /\ ~s.vs_halted /\
     (res = INL () ==> ~block_is_terminated sf /\ cenv'' = c) /\
     cenv_top_ext old cenv'' ee.scopes /\
     stmt_state_rel ctx func cenv'' cx ee s /\ ghost_inv d cenv'' cx ee G tn s /\
     (!x z. not_fresh_at fr x /\ lookup_var x salloc = SOME z ==> lookup_var x s = SOME z) /\
     (!x. not_fresh_at fr x ==> FLOOKUP G x = FLOOKUP Ga x /\
       op_taint tn (Var x) = op_taint tna (Var x)))
   (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 irule annassign_rhs_outcome_ptr >> goal_assum (drule_at Any) >> simp[] >>
 reverse conj_tac >- metis_tac[] >>
 rpt gen_tac >> strip_tac >>
 drule_all annassign_memory_normal_continuation_ptr >> strip_tac >>
 qexistsl [`ff`,`u`,`Gf`,`tnf`] >>
 gvs[ghost_inv_gas_obs, stmt_state_rel_gas_obs]
QED
