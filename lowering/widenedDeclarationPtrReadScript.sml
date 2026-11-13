(* Retained physical RHS to a counted fresh declaration. *)
Theory widenedDeclarationPtrRead
Ancestors exprSimWordArgs bodyPtrDefs fragGasPath stmtSimDeclCompose stmtFragPtr gasOutcome widenedDeclarationPtrStage widenedAssignPtrRhsInput
 annAssignPtrMemoryCont annAssignPtrContinuationFrame annAssignPtrMemoryContinuation
 annAssignPtrFacts annAssignPtrSetup annAssignPtrCompose
 bodyPtrIfExpZeroStore tupleMemoryFrame bodySim exprSimHyps exprSimHypsDefs
 exprSimDefs exprSimProps exprSimSource memoryLocalRhsProps
 exprLoweringProps exprLowering stmtSimDeclSource stmtSimDeclMem stmtSimProps
 assignValueMemoryOpen exprOpenTerminals
 compileEnv context loweringPosts loweringStateRelDefs ptrDiscipline
 gasSummaryComposePtr gasSummary fragGasPathPtr freshWrites
 valueTypingMemoryProps vyperTypeInvariants vyperEvalPreservesScopes vyperAST vyperState venomState
 finite_map words venomMemDefs
Libs monadsyntax

Theorem widened_declaration_retained_read_store_ptr:
 !ctx func old c cx lctx id typ tyv e es etv ltv sa0 st sa sb sf salloc
   marks v ee s op p sz w inst loc info bytes fr d PG Ga tna G tn.
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
   (lowered_value_type c e) info bytes sb = ((),sf) /\ loc = SOME LocMemory /\
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
 ptr_val_ok cx (post_value_type c e) v op G tn s /\ ptr_buf_ok c e op G s ==>
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
 `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings) =
    (INL v, ee with gas_obs := [])` by
   (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) = _`
      (fn th => ACCEPT_TAC (SIMP_RULE std_ss [listTheory.APPEND_NIL]
        (Q.SPEC `[]` th)))) >>
 `value_has_type tyv v /\ value_has_type etv v /\ value_has_type ltv v` by
   (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
    qpat_x_assum `!gs v es1. _`
      (qspecl_then [`gas_explicit marks salloc.vs_gas_readings`, `v`,
        `ee with gas_obs := []`] mp_tac) >> asm_rewrite_tac[]) >>
 `~is_word_type (post_value_type c e) /\
  post_value_type c e = lowered_value_type c e` by
   (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
    drule retained_intcall_physical_layout >> simp[] >> metis_tac[]) >>
 drule_all retained_rhs_physical_input_ptr >> strip_tac >- fs[] >>
 rename1 `evaluate_type (get_tenv cx) (post_value_type c e) = SOME physical_tv` >>
 rename1 `op = Var src` >> rename1 `eval_operand op s = SOME sw` >>
 qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
 `physical_tv = ltv` by metis_tac[optionTheory.SOME_11] >>
 `type_widens_to (get_tenv cx) (lowered_value_type c e) typ` by
   (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
    drule_all ifexp_call_annotation_widens >>
    fs[expr_body_pre_def,expr_sim_inv_def,env_consistent_def,
       env_context_consistent_def,lowered_value_type_def]) >>
 `val_wf tyv v` by metis_tac[value_has_type_memory_wf] >>
 suspend "metadata"
QED

Resume widened_declaration_retained_read_store_ptr[metadata]:
 `acyclic_struct_metadata c.ce_struct_fields` by fs[body_inv_def] >>
 `expr_sim_inv c cx env es` by fs[expr_body_pre_def] >>
 `sfields_tenv_consistent c.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields)` by
   (qpat_assum `expr_sim_inv c cx env es` mp_tac >>
    pure_rewrite_tac[expr_sim_inv_def] >> strip_tac >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
 `lookup_var p s = SOME w /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  stmt_state_rel ctx func c cx (ee with gas_obs := []) s /\
  (!aid ent. FLOOKUP salloc.vs_allocas aid = SOME ent ==>
    FLOOKUP s.vs_allocas aid = SOME ent)` by
   (fs[expr_post_def] >> metis_tac[]) >>
 `FLOOKUP G p = FLOOKUP Ga p /\
  op_taint tn (Var p) = op_taint tna (Var p)` by
   (qpat_assum `ghost_kept c es sa Ga tna salloc G tn`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_def]) >>
    disch_then (qspec_then `p` mp_tac) >> simp[]) >>
 `ptr_covers G tn p s sz` by
   (qpat_x_assum `ptr_covers Ga tna p salloc sz` mp_tac >>
    simp[ptr_covers_def] >> metis_tac[]) >>
 `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
   (fs[expr_post_def,locals_kept_def]) >>
 `!x z. not_fresh_at sa x /\ lookup_var x salloc = SOME z ==>
   lookup_var x s = SOME z` by fs[expr_post_def] >>
 `local_ptrs_rel func c es.scopes salloc` by
   fs[stmt_state_rel_def,state_rel_def] >>
 `!name. lookup_scopes name es.scopes = NONE ==>
   lookup_scopes name ee.scopes = NONE` by
   (rpt strip_tac >>
    mp_tac (Q.SPECL [`name`,`es.scopes`,`ee.scopes`]
      lookup_scopes_none_map_fdom) >> asm_rewrite_tac[]) >>
 `!name b n. local_region c es.scopes salloc name b n <=>
    local_region c (ee with gas_obs := []).scopes salloc name b n` by
   (rpt gen_tac >> irule tupleMemoryFrameTheory.local_region_scopes_domain >>
    simp[]) >>
 `ghost_kept c es fr Ga tna salloc G tn` by
   (irule ghost_kept_restrict_frontier_ptr >> qexists_tac `sa` >>
    asm_rewrite_tac[]) >>
 `ghost_kept c (ee with gas_obs := []) fr Ga tna salloc G tn` by
   (qpat_assum `ghost_kept c es fr Ga tna salloc G tn` mp_tac >>
    pure_rewrite_tac[ghost_kept_def] >>
    qpat_assum `!name b n. local_region c es.scopes salloc name b n <=> _`
      (fn th => pure_rewrite_tac[th]) >> disch_then ACCEPT_TAC) >>
 `!name b n. local_region c (ee with gas_obs := []).scopes salloc name b n <=>
    local_region c (ee with gas_obs := []).scopes s name b n` by
   (irule annassign_local_region_frame_iff_ptr >> rpt strip_tac >>
    rename1 `FLOOKUP c.ce_vars name = SOME (PtrVar (Var q) nsz)` >>
    `not_fresh_at sa q` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
    `?entry0. lookup_scopes name es.scopes = SOME entry0` by
      (Cases_on `lookup_scopes name es.scopes` >> simp[] >>
       qpat_assum `!name. lookup_scopes name es.scopes = NONE ==> _`
         (qspec_then `name` mp_tac) >> gvs[]) >>
    qpat_assum `local_ptrs_rel func c es.scopes salloc`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
    disch_then (qspecl_then [`name`,`entry0`,`q`,`nsz`] mp_tac) >>
    asm_rewrite_tac[] >> strip_tac >> metis_tac[]) >>
 `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
   (drule (cj 2 compile_expr_grows) >> simp[]) >>
 `not_fresh_at sb p /\ fr.cs_next_var <= sb.cs_next_var /\
  inst.inst_id < sb.cs_next_id` by
   (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
    conj_tac >> decide_tac) >>
 `(!q n. c.ce_return_buf = SOME (PtrVar (Var q) n) ==> not_fresh_at sb q) /\
  (!q n. c.ce_return_pc = SOME (PtrVar (Var q) n) ==> not_fresh_at sb q)` by
   metis_tac[not_fresh_at_mono] >>
 `not_local_ptr c (ee with gas_obs := []).scopes p` by
   (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
 `!x. not_fresh_at fr x ==> not_fresh_at sb x` by
   (rpt strip_tac >> irule not_fresh_at_mono >>
    qexists_tac `sa` >> simp[]) >>
 `w2n w + type_memory_size tyv < dimword (:256)` by
   (`alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
    `w2n w + sz <= s.vs_alloca_next` by
      metis_tac[alloca_inv_def,alloca_next_valid_def] >>
    fs[alloca_room_def] >> decide_tac) >>
 `ghost_kept c (ee with gas_obs := []) fr Ga tna salloc G tn` by first_assum ACCEPT_TAC >>
 suspend "store"
QED

Resume widened_declaration_retained_read_store_ptr[store]:
 mp_tac (Q.INST [`ce` |-> `c`,`sa` |-> `sb`,`sb` |-> `sf`,
   `sty` |-> `lowered_value_type c e`,`dty` |-> `typ`,
   `stv` |-> `ltv`,`dtv` |-> `tyv`,`va` |-> `sa`,`vb` |-> `sb`,
   `es` |-> `ee with gas_obs := []`,`s0` |-> `salloc`,
   `G0` |-> `Ga`,`tn0` |-> `tna`,`dw` |-> `(w:256 word)`,
   `sw` |-> `(sw:256 word)`,`cap` |-> `sz`]
   (SPEC_ALL widened_declaration_staged_store_ptr)) >>
 (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
   qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
   fs[expr_type_def] >> metis_tac[])) >>
 disch_then (qx_choosel_then [`Gf`,`tnf`,`u`] strip_assume_tac) >>
 `cenv_top_ext old c
   ((sc |+ (id,<|assignable := T;type := tyv;value := v;popped := []|>))::rest)` by
   (irule cenv_top_ext_declare_local >> simp[] >>
    qexistsl_tac [`id`,`sa0`,`st`,`typ`] >> gvs[lookup_scopes_def,AllCaseEqs()]) >>
 `~block_is_terminated sf` by
   (`~block_is_terminated sb` by
      (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
       qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
       simp[lower_value_def,comp_bind_def] >> rpt(pairarg_tac >> simp[]) >>
       strip_tac >>
       qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
       simp[Once compile_expr_def] >> strip_tac >>
       drule compile_intcall_open >> strip_tac >>
       drule_all unwrap_value_open >> simp[]) >>
    drule_all compile_assign_value_memory_open >> simp[]) >>

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
 first_assum (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ghost_kept_def])
QED

Finalise widened_declaration_retained_read_store_ptr
