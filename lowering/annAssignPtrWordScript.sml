(* Word annotated declarations, assembled from counted pointer boundaries. *)
Theory annAssignPtrWord
Ancestors
 annAssignPtrWordLayout annAssignPtrWordCont annAssignPtrSetup annAssignPtrCompose annAssignPtrFacts
 bodySimDeclCases bodyExprPreFacts exprSimSource vyperTyping vyperTypeExprResult
 bodySim exprSimHyps exprSimHypsDefs vyperTypeSystem vyperTypeInvariants
 vyperTypeExprSoundness stmtSimReturn stmtSimAssign
 stmtSimDeclStore stmtSimDecl stmtSimDeclGas stmtSimDeclCompose stmtSimDeclSource
 stmtSimProps stmtSimDefs bodyPtrDefs bodyPtrPreds exprSimDefs
 exprLoweringProps emitHelperProps stmtLowering compileEnv loweringStateRelDefs
 emitHelper rich_list loweringPosts fragGasPathPtr stmtFragPtr venomInst vyperInterpreter
 vyperState venomState valueEncoding list finite_map
Libs monadsyntax

Theorem compile_annassign_stmt_frag_ptr:
 !d ctx PG func cx lctx RetQ cenv ty id vtyp e es etv.
 cenv.ce_alloca_locals /\ is_word_type vtyp /\ ~has_length_word vtyp /\
 32 <= type_memory_bytes cenv vtyp /\
 type_memory_bytes cenv vtyp < dimword (:256) /\
 lookup_scopes id es.scopes = NONE /\
 (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 is_word_type (expr_type e) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
 (!gs tyv v es1. evaluate_type (get_tenv cx) vtyp = SOME tyv /\
   vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
   store_lays_out etv tyv v) /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   expr_sim_ptr d ctx PG func c cx (expr_type e) e es /\
   !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
     cs_extends sa sb) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ty (AnnAssign id vtyp e))
   (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
 rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_ptr_def] >>
 rpt gen_tac >> strip_tac >>
 `!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
     cs_extends a b` by metis_tac[] >>
 drule_all annassign_word_code_parts_ptr >>
 disch_then (qx_choosel_then [`st`,`sA`,`sB`,`op`,`p`] strip_assume_tac) >>
 rename1 `declare_local cenv id vtyp sa = (c,st)` >>
 qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
 `stmt_state_rel ctx func c cx es s0` by
   (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
 `ghost_inv d c cx es G0 tn0 s0` by
   (irule annassign_ghost_declare_local_entry_ptr >> metis_tac[]) >>
 `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
 `s0.vs_current_bb = st.cs_current_bb /\
  s0.vs_inst_idx = LENGTH st.cs_current_insts` by
   (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
 suspend "allocate"
QED

Resume compile_annassign_stmt_frag_ptr[allocate]:
 `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
   (`sA.cs_next_var = st.cs_next_var` by
      (drule emit_inst_extends >> simp[]) >>
    drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
 `~not_fresh_at sa p` by metis_tac[] >>
 `c.ce_return_buf = cenv.ce_return_buf /\ c.ce_return_pc = cenv.ce_return_pc` by
   (drule_all declare_local_ptr >> strip_tac >>
    qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
       ce_dynarray_capacity := _ |> = cenv` mp_tac >>
    simp[compile_env_component_equality]) >>
 `(!x n. c.ce_return_buf = SOME (PtrVar (Var x) n) ==> x <> p) /\
  (!x n. c.ce_return_pc = SOME (PtrVar (Var x) n) ==> x <> p)` by
   (fs[ret_pc_ok_def] >> metis_tac[]) >>
 drule_all annassign_setup_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 drule annassign_admissible_type >> strip_tac >>
 `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
   (irule annassign_admissible_rhs >> metis_tac[]) >>
 suspend "rhs"
QED

Resume compile_annassign_stmt_frag_ptr[rhs]:
 qpat_x_assum `!st0 c st1. _` kall_tac >>
 qpat_x_assum `!sa sb op. _` kall_tac >>
 `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
   (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s1,G1,tn1)
   (\res ee G tn t. ?v. res = INL v /\
     expr_post ctx func c cx e es sA sB s1 ee v op t /\
     t.vs_current_bb = sB.cs_current_bb /\
     t.vs_inst_idx = LENGTH sB.cs_current_insts /\
     ghost_inv d c cx ee G tn t /\ ptr_val_ok cx (expr_type e) v op G tn t /\
     (~is_word_type (expr_type e) ==> ptr_buf_ok c e op G t) /\
     ghost_kept c es sA G1 tn1 s1 G tn)
   (\res ee gt r. expr_exit res r)` by
   (qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[expr_sim_ptr_def] >> disch_then irule >> simp[] >>
    drule_all declare_local_ptr >> strip_tac >>
    fs[compile_env_component_equality, ret_pc_ok_def] >> metis_tac[]) >>
 `~block_is_terminated sb` by
   (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
    simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
         fresh_id_def, emit_def, comp_return_def] >>
    strip_tac >> Cases_on `sB.cs_current_insts` >>
    gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
        mk_inst_def, is_terminator_def]) >>
 qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
 `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
  FLOOKUP s1.vs_allocas ai.inst_id = SOME (w2n w,type_memory_bytes cenv vtyp)` by
   gvs[Abbr `ai`, mk_inst_def] >>
 `!gs v es1. vyperState$bind (eval_expr cx e) (read_result cx)
   (es with gas_obs := gs) = (INL v,es1) ==> store_lays_out etv tyv v` by
   metis_tac[] >>
 irule annassign_outcome_entry_prefix_ptr >>
 qexistsl [`G1`,`0`,`sA`,`s1`,`tn1`] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- fs[ghost_kept_def] >>
 reverse conj_tac >- asm_rewrite_tac[] >>
 irule annassign_concrete_rhs_outcome_ptr >>
 goal_assum (drule_at Any) >> simp[] >>
 conj_tac >- asm_rewrite_tac[] >>
 conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
 qexistsl [`ai`,`op`,`sB`,`w`] >> gvs[]

QED

Finalise compile_annassign_stmt_frag_ptr

Theorem compile_annassign_typed_stmt_frag_ptr:
 !d ctx PG func cx lctx RetQ cenv ty id vtyp e es tyv.
 cenv.ce_alloca_locals /\ is_word_type vtyp /\ ~has_length_word vtyp /\
 32 <= type_memory_bytes cenv vtyp /\
 type_memory_bytes cenv vtyp < dimword (:256) /\
 lookup_scopes id es.scopes = NONE /\
 (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 expr_type e = vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
 (!gs v es1. vyperState$bind (eval_expr cx e) (read_result cx)
   (es with gas_obs := gs) = (INL v,es1) ==> value_has_type tyv v) /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   expr_sim_ptr d ctx PG func c cx (expr_type e) e es /\
   !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
     cs_extends sa sb) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ty (AnnAssign id vtyp e))
   (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
 rpt strip_tac >> gvs[] >> irule compile_annassign_stmt_frag_ptr >>
 simp[] >> conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
 qpat_x_assum `!gs v es1. _ ==> value_has_type _ v` drule >> strip_tac >>
 irule store_lays_out_typed >> metis_tac[]
QED

Theorem body_annassign_word_ptr:
 !cx id typ e tops ctx func cenv env env' ret_ty lctx RetQ es d PG.
 (!tenv s'' tyv t. tenv = get_tenv cx /\
   lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
     (INL tyv,t) ==> body_expr_ptr_ok cx e) /\
 body_inv tops ctx cenv cx /\ supported_expr tops e /\
 (!target. supported_stmt_expr_exists
   (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
   occurs_abi_decode_target target tops) /\
 expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
 type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
 stmt_exprs_ok cenv (AnnAssign id typ e) /\
 call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
 is_word_type typ ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
   (eval_stmt cx (AnnAssign id typ e)) es
Proof
 rpt strip_tac >>
 `FLOOKUP cenv.ce_vars id = NONE` by
   (irule declared_name_unbound >> metis_tac[]) >>
 `well_typed_expr env e /\ expr_type e = typ /\
  id NOTIN FDOM env.var_types` by
   (gvs[type_stmt_def, AllCaseEqs()] >> metis_tac[type_widens_to_word]) >>
 `cenv.ce_alloca_locals` by fs[body_inv_def] >>
 `expr_body_pre cenv cx env e es` by metis_tac[annassign_rhs_pre_ptr] >>
 `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
   (drule expr_body_pre_type_evaluates >> simp[optionTheory.IS_SOME_EXISTS]) >>
 `body_expr_ptr_ok cx e` by (irule annassign_ih_ptr >> metis_tac[]) >>
 `lookup_scopes id es.scopes = NONE` by
   (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
    gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
    res_tac >> gvs[FLOOKUP_DEF]) >>
 drule_all word_type_sizes >> disch_then (qspec_then `cenv` strip_assume_tac) >>
 irule compile_annassign_typed_stmt_frag_ptr >>
 simp[is_word_type_no_length_word, wordsTheory.dimword_def] >>
 reverse conj_tac
 >- (rpt strip_tac >>
     `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
     suspend "source_typing") >>
 rpt gen_tac >> strip_tac >>
 reverse conj_tac >- metis_tac[compile_expr_grows] >>
 drule_all annassign_declared_expr_sim_ptr >> gvs[]
QED

Resume body_annassign_word_ptr[source_typing]:
     drule (SRULE [ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >>
     disch_then (qspecl_then [`INL v`,`es1`] mp_tac) >>
     gvs[vyperStateTheory.bind_def] >> strip_tac >>
     `env.type_defs = get_tenv cx` by
       gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
         value_result_typed_def, value_runtime_typed_def]
QED

Finalise body_annassign_word_ptr
