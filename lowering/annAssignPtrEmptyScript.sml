(* Empty annotated declarations on counted pointer paths. *)
Theory annAssignPtrEmpty
Ancestors
 annAssignPtrEmptyLayout annAssignPtrEmptySource annAssignPtrEmptyCont
 annAssignPtrSetup annAssignPtrCompose annAssignPtrFacts
 exprSimMemorySource exprSimWordArgs stmtSimDeclGas stmtSimDeclMem stmtSimDeclSource
 stmtSimDecl stmtSimProps stmtSimDefs bodyPtrDefs exprSimDefs
 exprLoweringProps emitHelperProps stmtLowering compileEnv loweringStateRelDefs
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
 Cases_on `storage_trace_domain cx st0 es.storage_trace`
 >~ [`~storage_trace_domain _ _ _`]
 >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
     irule gasStorageTheory.gas_bad_storage_at_initial >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
 `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
   fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
 `!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b vv. compile_expr c (expr_type e) e a = (vv,b) ==> cs_extends a b` by
   metis_tac[] >>
 drule_all annassign_empty_code_parts_ptr >>
 disch_then (qx_choosel_then [`st`,`sA`,`sB`,`vv`,`p`] strip_assume_tac) >>
 rename1 `declare_local cenv id vtyp sa = (c,st)` >>
 qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
 `!H. valid_horizon cx st0 H es.storage_trace ==>
   stmt_state_rel H ctx func c cx es s0 /\
   storage_well_formed_on cx es (FST H) /\ ghost_inv H d c cx es G0 tn0 s0` by
   (rpt strip_tac >> rpt conj_tac
    >- (irule stmt_state_rel_declare_local_entry >> metis_tac[])
    >- metis_tac[] >>
    irule annassign_ghost_declare_local_entry_ptr >> metis_tac[]) >>
 `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func c cx es s0 /\
   ghost_inv (storage_trace_horizon es.storage_trace) d c cx es G0 tn0 s0` by metis_tac[] >>
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
 `!H:(bool # bytes32 # type_value) list # num list. gas_path_ptr (cx_dead H cx) 0 ctx func PG G0 tn0 s0 0 G1 tn1 (OK s1)` by
   (gen_tac >> drule_all annassign_emit_instruction_ptr >> strip_tac >>
    `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s0.vs_inst_idx =
        SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p])` by
      simp[] >>
    drule_all annassign_alloca_path_ptr >>
    disch_then (qspecl_then [`cx_dead H cx`, `PG`, `G0`, `tn0`] mp_tac) >> gvs[]) >>
 `!H. valid_horizon cx st0 H es.storage_trace ==>
   stmt_state_rel H ctx func c cx es s1 /\
   storage_well_formed_on cx es (FST H) /\ ghost_inv H d c cx es G1 tn1 s1` by
   (rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ c _ _ s0 /\ _`
      (drule_then strip_assume_tac) >>
    drule_all annassign_setup_ptr >>
    disch_then (qspec_then `PG` strip_assume_tac) >> gvs[] >> metis_tac[]) >>
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
 `gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
   (eval_expr cx e) (es,s1,G1,tn1)
   (\H res ee G tn t. ?tv. res = INL tv /\
     vv_post H ctx func c cx e es sA sB s1 ee tv vv t /\
     t.vs_current_bb = sB.cs_current_bb /\
     t.vs_inst_idx = LENGTH sB.cs_current_insts /\
     ghost_inv H d c cx ee G tn t /\
     ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
     (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
       ptr_buf_ok c e op G t) /\
     (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok c e p.ptr_operand G t) /\
     ghost_kept c es sA G1 tn1 s1 G tn)
   (\H res ee gt r. expr_exit res r)` by
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
 qpat_x_assum `?H. valid_horizon _ _ H _`
   (qx_choose_then `H0` assume_tac) >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> _`
   (qspec_then `H0` mp_tac) >>
 impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
 drule_all (Q.INST [`H` |-> `H0`, `inst` |-> `ai`, `w` |-> `w`]
   (SPEC_ALL annassign_empty_normal_continuation_ptr)) >>
 disch_then (qx_choosel_then [`ff`,`tfin`,`tnf`] strip_assume_tac) >>
 `gas_marked_exec F (ctx,func) (new_variable id tyv v)
   (ee with gas_obs := [],t) [] (INL ()) ff (OK tfin)` by
   metis_tac[gas_marked_exec_ptr_exec] >>
 qexistsl [`ff`,`tfin`,`G`,`tnf`] >> conj_tac >- first_assum ACCEPT_TAC >>
 qx_gen_tac `HH` >> strip_tac >>
 `new_variable id tyv v (ee with gas_obs := []) =
   (INL (),ff with gas_obs := [])` by
   (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
 `valid_horizon cx st0 HH ee.storage_trace` by
   (mp_tac (Q.INST [`f` |-> `new_variable id tyv v`,
      `st` |-> `ee with gas_obs := []`, `st'` |-> `ff with gas_obs := []`,
      `res` |-> `INL ()`, `H` |-> `HH`]
      (INST_TYPE [alpha |-> ``:unit``] vyperStorageFootprintTheory.valid_horizon_frame)) >>
    simp[vyperStorageTraceTheory.storage_trace_frame_new_variable]) >>
 qpat_assum `!H. valid_horizon _ _ H _ ==> _`
   (qspec_then `HH` mp_tac) >>
 impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
 drule_all (Q.INST [`H` |-> `HH`, `inst` |-> `ai`, `w` |-> `w`]
   (SPEC_ALL annassign_empty_normal_continuation_ptr)) >> strip_tac >>
 gvs[gas_marked_exec_ptr_def, ghost_inv_gas_obs, stmt_state_rel_gas_obs]
QED

Finalise compile_annassign_empty_stmt_frag_ptr
