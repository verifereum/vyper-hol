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
   marks v ee s op p sz w inst loc bytes fr d PG Ga tna G tn.
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
   (lowered_value_type c e) bytes sb = ((),sf) /\
 fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
 lookup_var p salloc = SOME w /\ ptr_covers Ga tna p salloc sz /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 (?H. valid_horizon cx st0 H ee.storage_trace) /\
 (!H. valid_horizon cx st0 H ee.storage_trace ==>
 gas_marked_exec_ptr (cx_dead H cx) (ctx,func) PG
   (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna)
   marks (INL v) ee G tn (OK s) /\
 expr_post H ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op s /\
 ghost_inv H d c cx (ee with gas_obs := []) G tn s) /\
 s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ghost_kept c es sa Ga tna salloc G tn /\
 ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok c e op G s ==>
 ?ff u Gf tnf.
 gas_marked_exec F (ctx,func) (new_variable id tyv v)
   (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
 (!H. valid_horizon cx st0 H ff.storage_trace ==>
 gas_marked_exec_ptr (cx_dead H cx) (ctx,func) PG (new_variable id tyv v)
   (ee with gas_obs := [],s,G,tn) [] (INL ()) ff Gf tnf (OK u) /\
 (?cenv''. stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\
   (~block_is_terminated sf /\ cenv'' = c) /\
   cenv_top_ext old cenv'' ff.scopes /\
   stmt_state_rel H ctx func cenv'' cx ff u /\
   storage_well_formed_on cx ff (FST H) /\ ghost_inv H d cenv'' cx ff Gf tnf u /\
   (!x z. not_fresh_at fr x /\ lookup_var x salloc = SOME z ==> lookup_var x u = SOME z) /\
   (!x. not_fresh_at fr x ==> FLOOKUP Gf x = FLOOKUP Ga x /\
      op_taint tnf (Var x) = op_taint tna (Var x))))
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
   (qspec_then `H0` (strip_assume_tac o UNDISCH)) >>
 `post_value_type c e = expr_type e` by
   metis_tac[post_value_type_lowered, post_value_type_bytestring] >>
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
  stmt_state_rel H0 ctx func c cx (ee with gas_obs := []) s /\
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
   (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac compile_assign_value_memory_widen_open) >>
    metis_tac[bytestring_memory_bytes_positive]) >>
 `!HH. valid_horizon cx st0 HH ee.storage_trace ==>
   stmt_state_rel HH ctx func c cx (ee with gas_obs := []) s /\
   ghost_inv HH d c cx (ee with gas_obs := []) G tn s` by
   (rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `HH` (strip_assume_tac o UNDISCH)) >> fs[expr_post_def]) >>
 `?u Gf tnf.
  (!D. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK u)) /\
  u.vs_current_bb = sf.cs_current_bb /\ u.vs_inst_idx = LENGTH sf.cs_current_insts /\
  ~u.vs_halted /\
  (!HH. valid_horizon cx st0 HH ee.storage_trace ==>
   stmt_state_rel HH ctx func c cx
   ((ee with gas_obs := []) with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) u /\
  ghost_inv HH d c cx
   ((ee with gas_obs := []) with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) Gf tnf u) /\
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
 goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
 simp[] >> metis_tac[]
QED

Resume annassign_memory_normal_continuation_ptr[post]:
 markerLib.RESUME_TAC >>
 `gas_marked_exec_ptr (cx_dead H0 cx) (ctx,func) PG (new_variable id tyv v)
   (ee with gas_obs := [],s,G,tn) [] (INL ())
   (ee with <|gas_obs := []; scopes :=
     (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest|>)
   Gf tnf (OK u)` by simp[gas_marked_exec_ptr_def] >>
 `gas_marked_exec F (ctx,func) (new_variable id tyv v)
   (ee with gas_obs := [],s) [] (INL ())
   (ee with <|gas_obs := []; scopes :=
     (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest|>)
   (OK u)` by metis_tac[gas_marked_exec_ptr_exec] >>
 qexistsl [`ee with <|gas_obs := []; scopes :=
   (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest|>`,
   `u`,`Gf`,`tnf`] >> simp[] >> qx_gen_tac `HH` >> strip_tac >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
   (qspec_then `HH` (strip_assume_tac o UNDISCH)) >>
 qpat_assum `!HH. valid_horizon _ _ HH _ ==> stmt_state_rel HH _ _ _ _ _ _ /\ _`
   (qspec_then `HH` (strip_assume_tac o UNDISCH)) >>
 `!scs. storage_well_formed_on cx
    ((ee with gas_obs := []) with scopes := scs) (FST HH)` by
   fs[expr_post_def, vyperStorageFootprintTheory.storage_well_formed_on_def,
      vyperStorageBackendTheory.get_storage_scopes] >>
 conj_tac >- simp[gas_marked_exec_ptr_def] >>
 qexists `c` >>
 gns[stmt_lands_def, stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
 conj_tac
 >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> metis_tac[]) >>
 qpat_x_assum `ghost_kept c es sa Ga tna salloc G tn`
   (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >>
 qpat_x_assum `ghost_kept c _ fr G tn s Gf tnf`
   (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >> metis_tac[]
QED

Finalise annassign_memory_normal_continuation_ptr

Theorem annassign_memory_concrete_rhs_outcome_ptr:
 !ctx func old c cx lctx RetQ id typ tyv e es etv ltv sa0 st sa sb sf salloc
   op p sz w inst loc bytes fr d PG Ga tna.
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
   (lowered_value_type c e) bytes sb = ((),sf) /\
 fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
 lookup_var p salloc = SOME w /\ ptr_covers Ga tna p salloc sz /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
   (bind (eval_expr cx e) (read_result cx)) (es,salloc,Ga,tna)
   (\H res ee G tn s. ?v. res = INL v /\
     expr_post H ctx func c cx e es sa sb salloc ee v op s /\
     s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv H d c cx ee G tn s /\ ptr_val_ok cx (expr_type e) v op G tn s /\
     (~is_word_type (expr_type e) ==> ptr_buf_ok c e op G s) /\
     ghost_kept c es sa Ga tna salloc G tn)
   (\H res ee gt r. expr_exit res r) ==>
 gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
   (eval_stmt cx (AnnAssign id typ e)) (es,salloc,Ga,tna)
   (\H res ee G tn s. ?cenv''.
     stmt_lands lctx sf res s /\ ~s.vs_halted /\
     (res = INL () ==> ~block_is_terminated sf /\ cenv'' = c) /\
     cenv_top_ext old cenv'' ee.scopes /\
     stmt_state_rel H ctx func cenv'' cx ee s /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv H d cenv'' cx ee G tn s /\
     (!x z. not_fresh_at fr x /\ lookup_var x salloc = SOME z ==> lookup_var x s = SOME z) /\
     (!x. not_fresh_at fr x ==> FLOOKUP G x = FLOOKUP Ga x /\
       op_taint tn (Var x) = op_taint tna (Var x)))
   (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 irule annassign_rhs_outcome_ptr >> goal_assum (drule_at Any) >> simp[] >>
 reverse conj_tac >- metis_tac[] >>
 rpt gen_tac >> strip_tac >>
 drule_all annassign_memory_normal_continuation_ptr >> strip_tac >>
 qexistsl [`ff`,`u`,`Gf`,`tnf`] >>
 gvs[ghost_inv_gas_obs, stmt_state_rel_gas_obs]
QED
