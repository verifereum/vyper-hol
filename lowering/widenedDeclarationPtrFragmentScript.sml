(* Counted pointer fragment for nonempty memory declarations. *)
Theory widenedDeclarationPtrFragment
Ancestors
 widenedDeclarationPtrOutcome widenedAssignPtrContinuation widenedAssignPtrRhsInput
 bodySim exprSimHypsDefs
 annAssignPtrMemoryLayout annAssignPtrMemoryCont annAssignPtrWord
 annAssignPtrSetup annAssignPtrCompose annAssignPtrFacts
 stmtSimDeclMem stmtSimDecl stmtSimDeclGas stmtSimDeclCompose stmtSimDeclSource
 stmtSimProps stmtSimDefs bodyPtrDefs exprSimDefs exprLoweringProps emitHelperProps
 stmtLowering compileEnv loweringStateRelDefs emitHelper rich_list loweringPosts fragGasPathPtr
 stmtFragPtr venomInst vyperInterpreter vyperState venomState valueEncoding vyperAST context
 vyperTypeArgFits valueCopyBytes list finite_map
Libs monadsyntax

Theorem widened_declaration_stmt_frag_ptr:
 !d ctx PG func cx lctx RetQ cenv ty id vtyp e es etv tyv ltv.
 cenv.ce_alloca_locals /\
 ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) /\
 lookup_scopes id es.scopes = NONE /\
 (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
 supported_expr tops e /\ e = Call vtyp (IntCall fid) args drv /\
 ~is_bytestring_type vtyp /\
 ~(lowered_value_type cenv e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
  arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
 evaluate_type (get_tenv cx) vtyp = SOME tyv /\
 evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
 type_memory_bytes cenv vtyp = type_memory_size tyv /\
 0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
 type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
 0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256) /\
 (!gs v es1. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1) ==>
    value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v) /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   expr_sim_ptr d ctx PG func c cx (expr_type e) e es /\
   (!sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
     cs_extends sa sb) /\
   body_inv tops ctx c cx /\ expr_body_pre c cx env e es) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ty (AnnAssign id vtyp e))
   (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `expr_type e = vtyp` by metis_tac[expr_type_def] >>
 rewrite_tac[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
 `!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
     cs_extends a b` by metis_tac[] >>
 drule_all annassign_memory_code_parts_ptr >>
 disch_then (qx_choosel_then [`st`,`sA`,`sV`,`sB`,`vv`,`op`,`p`] strip_assume_tac) >>
 rename1 `declare_local cenv id vtyp sa = (c,st)` >>
 qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
 drule_all annassign_declared_memory_types_ptr >> strip_tac >>
 `stmt_state_rel ctx func c cx es s0` by
   (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
 `ghost_inv d c cx es G0 tn0 s0` by
   (irule annassign_ghost_declare_local_entry_ptr >> metis_tac[]) >>
 `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
 `s0.vs_current_bb = st.cs_current_bb /\
  s0.vs_inst_idx = LENGTH st.cs_current_insts` by
   (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>

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
 `type_memory_bytes cenv vtyp < dimword (:256)` by (simp[] >> decide_tac) >>
 drule_all annassign_setup_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
   (irule annassign_admissible_rhs >> metis_tac[]) >>

 qpat_x_assum `!st0 c st1. _` kall_tac >>
 qpat_x_assum `!sa sb op. _` kall_tac >>
 `post_value_type c e = lowered_value_type c e /\
  ~is_word_type (post_value_type c e)` by
   (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
    drule retained_intcall_physical_layout >>
    simp[expr_type_def] >> metis_tac[]) >>
 `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
   (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s1,G1,tn1)
   (\res ee G tn t. ?v. res = INL v /\
     expr_post ctx func c cx e es sA sB s1 ee v op t /\
     t.vs_current_bb = sB.cs_current_bb /\
     t.vs_inst_idx = LENGTH sB.cs_current_insts /\
     ghost_inv d c cx ee G tn t /\ ptr_val_ok cx (post_value_type c e) v op G tn t /\
     (~is_word_type (expr_type e) ==> ptr_buf_ok c e op G t) /\
     ghost_kept c es sA G1 tn1 s1 G tn)
   (\res ee gt r. expr_exit res r)` by
   (qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[expr_sim_ptr_def] >> disch_then irule >> simp[] >>
    drule_all declare_local_ptr >> strip_tac >>
    fs[compile_env_component_equality, ret_pc_ok_def] >> metis_tac[]) >>
 qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
 `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
  FLOOKUP s1.vs_allocas ai.inst_id = SOME (w2n w,type_memory_bytes cenv vtyp)` by
   (simp[Abbr `ai`, mk_inst_def] >>
    qpat_x_assum `FLOOKUP s1.vs_allocas st.cs_next_id = _` mp_tac >>
    PURE_ASM_REWRITE_TAC [] >> simp[]) >>
 irule annassign_outcome_entry_prefix_ptr >>
 qexistsl [`G1`,`0`,`sa`,`s1`,`tn1`] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- fs[ghost_kept_def] >>
 reverse conj_tac >- asm_rewrite_tac[] >>

 `~c.ce_is_ctor` by
   (drule_all declare_local_ptr >> strip_tac >>
    qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
       ce_dynarray_capacity := _ |> = cenv` mp_tac >>
    simp[compile_env_component_equality] >> metis_tac[]) >>
 `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
 `sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_id <= sA.cs_next_id` by
   (drule_all declare_local_ptr >> strip_tac >>
    drule emit_inst_extends >> simp[] >>
    simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
    rpt strip_tac >> gvs[]) >>
 `local_ptrs_reserved c sB` by
   (irule local_ptrs_reserved_next_var >> qexists `sA` >>
    simp[] >> drule (cj 2 compile_expr_grows) >> simp[]) >>
 `!q n. cenv.ce_return_pc = SOME (PtrVar (Var q) n) ==> not_fresh_at sA q` by
   (fs[ret_pc_ok_def] >> metis_tac[]) >>
 qpat_x_assum `s1 = _` kall_tac >>
 qpat_x_assum `G1 = _` kall_tac >>
 qpat_x_assum `tn1 = _` kall_tac >>
 `0 < type_memory_bytes c (lowered_value_type c e) /\
  ?rp. vv = LocatedValue (c.ce_func_return_type (nsid_to_string fid)) rp /\
    rp.ptr_location = LocMemory` by
   (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
    irule widened_assign_retained_call_memory >> metis_tac[expr_type_def]) >>
 `vv_location vv = SOME LocMemory` by simp[vv_location_def] >>
 `sa.cs_next_var <= sA.cs_next_var /\ ai.inst_id < sA.cs_next_id` by
   (drule_all declare_local_ptr >> strip_tac >>
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
      comp_return_def, Abbr `ai`, mk_inst_def]) >>
 `ai.inst_id = st.cs_next_id` by simp[Abbr `ai`, mk_inst_def] >>
 qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
 mp_tac (Q.INST [`old` |-> `cenv`,`typ` |-> `vtyp`,
   `e` |-> `Call vtyp (IntCall fid) args drv`,
   `sa0` |-> `sa`,`sa` |-> `sA`,`sb` |-> `sB`,`fr` |-> `sa`,
   `sf` |-> `sb`,
   `bytes` |-> `type_memory_bytes c vtyp`,
   `salloc` |-> `s1`,`Ga` |-> `G1`,`tna` |-> `tn1`,
   `inst` |-> `ai`,`loc` |-> `vv_location vv`,
   `sz` |-> `type_memory_bytes cenv vtyp`]
   (SPEC_ALL widened_declaration_rhs_outcome_ptr)) >>
 (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
   fs[expr_type_def] >> metis_tac[])) >> simp[]
QED

