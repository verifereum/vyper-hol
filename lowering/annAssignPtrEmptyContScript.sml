(* Empty declarations initialize only their live length word; padding may
   remain tainted.  The general declaration store supplies the robust ghost. *)
Theory annAssignPtrEmptyCont
Ancestors
 annAssignPtrCompose annAssignPtrStore stmtFragPtr stmtSimDeclCompose stmtSimDeclMem
 stmtSimDeclSource stmtSimProps bodyPtrDefs loweringPosts exprSimDefs
 gasSummaryComposePtr fragGasPathPtr fragGasPath stmtLowering valueEncoding
 valueEncodingProps ptrDiscipline exprLoweringProps
 vyperInterpreter vyperState venomState compileEnv list finite_map
Libs monadsyntax

Theorem annassign_empty_store_continuation_ptr:
 !ctx func old cenv cx lctx e es es1 s0 s sa sb sf vv id p sz w inst
   typ tyv sc rest d PG G0 tn0 G tn.
 vv_post ctx func cenv cx e es sa sb s0 es1 (Value (default_value tyv)) vv s /\
 ghost_inv d cenv cx es1 G tn s /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\
 has_length_word typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
 emit_void MSTORE [Var p; Lit 0w] sb = ((),sf) /\ fn_has_code sb sf func /\
 ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
 s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
 es1.scopes = sc::rest /\ lookup_scopes id es1.scopes = NONE /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
 lookup_var p s0 = SOME w /\ ptr_covers G tn p s sz /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 type_memory_size tyv <= sz /\ ~block_is_terminated sf /\
 cenv_top_ext old cenv
   ((sc |+ (id,<|assignable := T; type := tyv; value := default_value tyv; popped := []|>))::rest) /\
 (!tail. new_variable id tyv (default_value tyv) (es1 with gas_obs := tail) =
   (INL (), (es1 with scopes :=
     (sc |+ (id,<|assignable := T; type := tyv; value := default_value tyv; popped := []|>))::rest)
     with gas_obs := tail)) ==>
 ?ee t tnf.
 gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (new_variable id tyv (default_value tyv))
   (es1,s,G,tn) [] (INL ()) ee G tnf (OK t) /\
 (?cenv''. stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
   (~block_is_terminated sf /\ cenv'' = cenv) /\
   cenv_top_ext old cenv'' ee.scopes /\
   stmt_state_rel ctx func cenv'' cx ee t /\ ghost_inv d cenv'' cx ee G tnf t /\
   (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
   (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tnf (Var x) = op_taint tn0 (Var x)))
Proof
 rpt gen_tac >> strip_tac >>
 `stmt_state_rel ctx func cenv cx es1 s /\ lookup_var p s = SOME w /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz)` by
   (fs[vv_post_def] >> metis_tac[]) >>
 `!u. val_in_memory tyv (default_value tyv) (w2n w)
      (mstore (w2n w) 0w u).vs_memory /\
      val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
   (gen_tac >> irule memory_length_word_layout >>
    simp[mstore_mem_word_at_same] >> metis_tac[]) >>
 `val_wf tyv (default_value tyv) /\
  (!u. val_in_memory tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w u).vs_memory)` by metis_tac[] >>
 `32 <= type_memory_size tyv` by metis_tac[] >>
 `32 <= sz` by decide_tac >>
 `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {}` by
   simp[eval_operand_def, op_taint_def] >>
 qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _`
   (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >>
 `ghost_kept cenv es1 sa G tn s G tn` by simp[ghost_kept_def] >>
 drule_all annassign_declare_store_ptr >>
 disch_then (qspecl_then [`PG`,`T`] strip_assume_tac) >>
 qexistsl [`es1 with scopes :=
   (sc |+ (id,<|assignable := T; type := tyv; value := default_value tyv; popped := []|>))::rest`,
   `s'`,`tn'`] >> conj_tac
 >- gvs[gas_marked_exec_ptr_def] >>
 qexists `cenv` >> simp[stmt_lands_def] >>
 fs[vv_post_def, ghost_kept_def] >> metis_tac[]
QED

Theorem annassign_empty_normal_continuation_ptr:
 !ctx func old c cx lctx id typ tyv e es sa0 st sa sb sf salloc
   marks v ee s vv p sz w inst d PG Ga tna G tn.
 declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
 (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
 evaluate_type (get_tenv cx) typ = SOME tyv /\ has_length_word typ /\
 (!gs tv es1. eval_expr cx e (es with gas_obs := gs) = (INL tv,es1) ==>
    tv = Value (default_value tyv)) /\
 local_ptrs_reserved c sa /\ ~ctx_has_dalloca ctx /\
 emit_void MSTORE [Var p; Lit 0w] sb = ((),sf) /\ fn_has_code sb sf func /\
 fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
 lookup_var p salloc = SOME w /\ ptr_covers Ga tna p salloc sz /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 type_memory_size tyv <= sz /\
 gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_expr cx e)
   (es,salloc,Ga,tna) marks (INL (Value v)) ee G tn (OK s) /\
 vv_post ctx func c cx e es sa sb salloc (ee with gas_obs := []) (Value v) vv s /\
 s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ghost_inv d c cx (ee with gas_obs := []) G tn s /\
 ghost_kept c es sa Ga tna salloc G tn ==>
 ?ff u tnf.
 gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (new_variable id tyv v)
   (ee with gas_obs := [],s,G,tn) [] (INL ()) ff G tnf (OK u) /\
 (?cenv''. stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\
   (~block_is_terminated sf /\ cenv'' = c) /\
   cenv_top_ext old cenv'' ff.scopes /\
   stmt_state_rel ctx func cenv'' cx ff u /\ ghost_inv d cenv'' cx ff G tnf u /\
   (!x z. not_fresh_at sa x /\ lookup_var x salloc = SOME z ==> lookup_var x u = SOME z) /\
   (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP Ga x /\
      op_taint tnf (Var x) = op_taint tna (Var x)))
Proof
 rpt gen_tac >> strip_tac >>
 `!tail. eval_expr cx e
   (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
     (INL (Value v),ee with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
 `v = default_value tyv` by
   (first_x_assum (qspec_then `[]` assume_tac) >>
    qpat_x_assum `!gs tv es1. _` drule >> simp[]) >>
 `!tail. bind (eval_expr cx e) (read_result cx)
   (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)` by
   simp[bind_def, read_result_def, return_def] >>
 `~s.vs_halted` by
   (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[gas_marked_exec_ptr_def] >> strip_tac >>
    drule gas_path_ptr_erase >> strip_tac >> drule gas_path_normal >> simp[]) >>
 drule_all annassign_continuation_all_tails >> strip_tac >>
 `not_local_ptr c (ee with gas_obs := []).scopes p` by
   (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
 `cenv_top_ext old c
   ((sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest)` by
   (irule cenv_top_ext_declare_local >> simp[] >>
    qexistsl [`id`,`sa0`,`st`,`typ`] >> gvs[lookup_scopes_def, AllCaseEqs()]) >>
 `ptr_covers G tn p s sz` by
   (fs[ptr_covers_def, ghost_kept_def, vv_post_def] >> metis_tac[]) >>
 qpat_x_assum `v = default_value tyv` SUBST_ALL_TAC >>
 drule annassign_empty_store_continuation_ptr >> disch_then irule >>
 gvs[] >> conj_tac >- (qexists `typ` >> simp[]) >>
 qexists `inst` >> simp[]
QED
