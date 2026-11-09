(* Empty annotated declarations on counted pointer paths. *)
Theory annAssignPtrEmpty
Ancestors
 annAssignPtrEmptyLayout annAssignPtrEmptySource annAssignPtrEmptyCont
 annAssignPtrSetup annAssignPtrCompose annAssignPtrFacts
 exprSimMemorySource exprSimWordArgs stmtSimDeclGas stmtSimDeclMem stmtSimDeclSource
 stmtSimDecl stmtSimProps stmtSimDefs bodyPtrDefs exprSimDefs
 exprLoweringProps emitHelperProps stmtLowering compileEnv
 emitHelper rich_list loweringPosts fragGasPathPtr stmtFragPtr venomInst vyperInterpreter
 vyperState venomState valueEncoding list finite_map
Libs monadsyntax

Theorem compile_annassign_empty_stmt_frag_ptr:
 !d ctx PG func cx lctx RetQ cenv ty id vtyp e es tyv.
 cenv.ce_alloca_locals /\ has_length_word vtyp /\ is_empty_value_expr e /\
 lookup_scopes id es.scopes = NONE /\
 (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 evaluate_type (get_tenv cx) vtyp = SOME tyv /\
 type_memory_bytes cenv vtyp = type_memory_size tyv /\
 type_memory_size tyv < dimword (:256) /\
 (!tv es1. eval_expr cx e es = (INL tv,es1) ==> tv = Value (default_value tyv)) /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   expr_vv_sim_ptr d ctx PG func c cx (expr_type e) e es /\
   !sa sb vv. compile_expr c (expr_type e) e sa = (vv,sb) ==> cs_extends sa sb) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ty (AnnAssign id vtyp e))
   (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
 rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_ptr_def] >>
 rpt gen_tac >> strip_tac >>
 `!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b vv. compile_expr c (expr_type e) e a = (vv,b) ==> cs_extends a b` by
   metis_tac[] >>
 drule_all annassign_empty_code_parts_ptr >>
 disch_then (qx_choosel_then [`st`,`sA`,`sB`,`vv`,`p`] strip_assume_tac) >>
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

Resume compile_annassign_empty_stmt_frag_ptr[allocate]:
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
 `type_memory_bytes cenv vtyp < dimword (:256)` by simp[] >>
 drule_all annassign_setup_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
   metis_tac[annassign_admissible_rhs, forced_expr_admissible_raw] >>
 suspend "rhs"
QED

Resume compile_annassign_empty_stmt_frag_ptr[rhs]:
 qpat_x_assum `!st0 c st1. _` kall_tac >>
 qpat_x_assum `!sa sb vv. _` kall_tac >>
 `post_value_type c e = expr_type e` by
   (irule post_value_type_not_int_call >> rpt strip_tac >>
    gvs[is_empty_value_expr_def]) >>
 `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
   (eval_expr cx e) (es,s1,G1,tn1)
   (\res ee G tn t. ?tv. res = INL tv /\
     vv_post ctx func c cx e es sA sB s1 ee tv vv t /\
     t.vs_current_bb = sB.cs_current_bb /\
     t.vs_inst_idx = LENGTH sB.cs_current_insts /\
     ghost_inv d c cx ee G tn t /\
     ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
     (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
       ptr_buf_ok c e op G t) /\
     (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok c e p.ptr_operand G t) /\
     ghost_kept c es sA G1 tn1 s1 G tn)
   (\res ee gt r. expr_exit res r)` by
   (qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[expr_vv_sim_ptr_def] >> disch_then irule >> simp[] >>
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
 `!gs tv es1. eval_expr cx e (es with gas_obs := gs) = (INL tv,es1) ==>
    tv = Value (default_value tyv)` by metis_tac[eval_empty_default_gas_obs_ptr] >>
 suspend "compose"
QED

Resume compile_annassign_empty_stmt_frag_ptr[compose]:
 irule annassign_outcome_entry_prefix_ptr >>
 qexistsl [`G1`,`0`,`sA`,`s1`,`tn1`] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- fs[ghost_kept_def] >>
 reverse conj_tac >- asm_rewrite_tac[] >>
 irule annassign_raw_rhs_outcome_ptr >>
 conj_tac >- metis_tac[] >>
 goal_assum (drule_at Any) >> simp[] >>
 reverse conj_tac >- metis_tac[] >>
 rpt gen_tac >> strip_tac >>
 drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)
   annassign_empty_normal_continuation_ptr >>
 disch_then drule >>
 disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
 simp[] >>
 disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
 disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
 disch_then (qspecl_then [`w`,`ai`] mp_tac) >>
 impl_tac >- (gvs[] >> first_assum MATCH_ACCEPT_TAC) >>
 disch_then (qx_choosel_then [`ff`,`tfin`,`tnf`] strip_assume_tac) >>
 qexistsl [`ff`,`tfin`,`G`,`tnf`] >>
 gvs[ghost_inv_gas_obs, stmt_state_rel_gas_obs]
QED

Finalise compile_annassign_empty_stmt_frag_ptr
