(* Counted declaration outcomes compose the retained physical RHS and its fresh store. *)
Theory widenedDeclarationPtrOutcome
Ancestors exprSimWordArgs widenedDeclarationPtrRead annAssignPtrMemoryCont annAssignPtrCompose
 gasSummaryComposePtr stmtFragPtr loweringPosts bodyPtrDefs stmtLowering
 compileEnv exprSimDefs exprSimHypsDefs vyperState vyperAST finite_map

Theorem widened_declaration_rhs_outcome_ptr:
 !ctx func old c cx lctx RetQ id typ tyv e es etv ltv sa0 st sa sb sf salloc
   op p sz w inst loc bytes fr d PG Ga tna.
 body_inv tops ctx c cx /\ expr_body_pre c cx env e es /\
 e = Call typ (IntCall fid) args drv /\
 declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
 (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
 ~is_word_type typ /\ ~is_word_type (expr_type e) /\ ~c.ce_is_ctor /\
 ~is_bytestring_type typ /\
 ~(lowered_value_type c e = expr_type e \/
   is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type c e) /\
   arg_type_fits (lowered_value_type c e) (expr_type e)) /\
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
 evaluate_type (get_tenv cx) (lowered_value_type c e) = SOME ltv /\
 type_memory_bytes c typ = type_memory_size tyv /\ type_memory_size tyv <= sz /\
 type_memory_bytes c (lowered_value_type c e) = type_memory_size ltv /\
 0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256) /\
 (!gs v es1. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1) ==>
    value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v) /\
 stmt_state_rel ctx func c cx es salloc /\
 local_ptrs_reserved c sa /\ local_ptrs_reserved c sb /\ cs_extends sa sb /\
 (!q n. c.ce_return_buf = SOME (PtrVar (Var q) n) ==> not_fresh_at sa q) /\
 (!q n. c.ce_return_pc = SOME (PtrVar (Var q) n) ==> not_fresh_at sa q) /\
 (!q. not_fresh_at fr q ==> not_fresh_at sa q) /\
 fr.cs_next_id <= sa.cs_next_id /\ fr.cs_next_id <= inst.inst_id /\
 fr.cs_next_var <= sa.cs_next_var /\ inst.inst_id < sa.cs_next_id /\
 lower_value compile_expr c (expr_type e) e sa = (op,sb) /\
 compile_assign_value c (Var p) LocMemory op F loc typ
   (lowered_value_type c e) bytes sb = ((),sf) /\ loc = SOME LocMemory /\
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
     ghost_inv d c cx ee G tn s /\ ptr_val_ok cx (post_value_type c e) v op G tn s /\
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
 qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
 mp_tac (Q.INST [`e` |-> `Call typ (IntCall fid) args drv`,`s` |-> `t`]
   (SPEC_ALL widened_declaration_retained_read_store_ptr)) >>
 (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
   fs[vyperASTTheory.expr_type_def] >> metis_tac[])) >>
 disch_then (qx_choosel_then [`ff`,`u`,`Gf`,`tnf`] strip_assume_tac) >>
 qexistsl [`ff`,`u`,`Gf`,`tnf`] >>
 gvs[ghost_inv_gas_obs, stmt_state_rel_gas_obs]
QED
