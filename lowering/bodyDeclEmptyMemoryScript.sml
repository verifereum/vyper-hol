(* Counted memory simulation of a declaration initialised with the empty
   value: the local's ALLOCA, the right-hand side's code, and one MSTORE of
   a zero length word into the local.  The memory twin of
   stmtSimDeclEmpty's compile_annassign_empty_stmt_frag. *)
Theory bodyDeclEmptyMemory
Ancestors
  bodyDeclWordMemory bodyDeclMemoryCompose bodyDeclMemoryCounted
  bodyDeclMemoryCore stmtSimDeclCompose stmtSimDeclSource stmtSimDeclStore
  stmtSimDeclMem stmtSimDeclEmpty stmtSimDecl exprSimMemDefs
  exprSimMemorySource bodyMemoryDefs fragGasMode fragGasPathMem fragGasPath gasSummary
  gasSummaryCompose gasOutcome gasExemptCert loweringPosts exprSimDefs
  stmtSimDefs stmtSimProps loweringSlice exprLoweringProps localPtrsProps
  freshWrites valueEncodingProps emitHelper emitHelperProps fragExec
  venomInst venomState stmtLowering compileEnv vyperInterpreter vyperState
  list rich_list finite_map
Libs monadsyntax

(* The declaration's source action from the state after the local's
   ALLOCA, for a right-hand side whose value_vv is dropped: its raw
   outcome, and the binding of the local after a value. *)
Theorem annassign_raw_rhs_outcome_mem:
  !ctx func cx RetQ id typ tyv e es s0 salloc tops Q P.
    gas_path_mem ctx func s0 0 (OK salloc) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
       ?v. tv = Value v) /\
    gas_outcome T tops (ctx,func) (eval_expr cx e) (es,salloc) Q
      (\res ee r. expr_exit res r) /\
    (!res ee t. Q res ee t ==> ?tv. res = INL tv) /\
    (!marks v ee t.
      gas_marked_exec T (ctx,func) (eval_expr cx e) (es,salloc)
        marks (INL (Value v)) ee (OK t) /\
      Q (INL (Value v)) (ee with gas_obs := []) t ==>
      ?ff u. gas_marked_exec T (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
        P (INL ()) (ff with gas_obs := []) u) ==>
    gas_outcome T tops (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,s0) P
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `salloc` >> simp[] >>
  rewrite_tac[gas_outcome_def] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  once_rewrite_tac[bind_assoc] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >>
          `?tv. res = INL tv` by metis_tac[] >> gvs[] >>
          `?v. tv = Value v` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >> strip_tac >>
             first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
          gvs[] >>
          qpat_x_assum `!marks v ee t. _` (drule_then mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl [`es_end`, `t`, `Value v`] >>
          simp[read_result_def, bind_return]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Theorem annassign_empty_parts_mem[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word vtyp /\ is_empty_value_expr e ==>
    ?sA vv sB.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sB) /\
      emit_void MSTORE [Var p; Lit 0w] sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emit_inst_unit >> gvs[]
QED

(* x: T = e for a type T with a length word, where e is the empty value
   and its values are T's default value.  The lowering keeps e's code
   (e's judgment is expr_vv_sim_mem, as e's value_vv is never unwrapped)
   and stores a zero length word at the local's buffer of
   type_memory_bytes of T, which lays out T's default value. *)
Theorem compile_annassign_empty_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty id vtyp e es tyv.
    cenv.ce_alloca_locals /\
    has_length_word vtyp /\ is_empty_value_expr e /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    type_memory_size tyv < dimword (:256) /\
    (!gs tv es1. eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) ==>
                 tv = Value (default_value tyv)) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_vv_sim_mem ctx func c cx (expr_type e) e es) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  rename1 `declare_local cenv id vtyp sa = (c, st)` >>
  qpat_x_assum `!st0 c st1. _ ==> expr_vv_sim_mem _ _ _ _ _ _ _` drule >>
  strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf` by
    (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality] >> metis_tac[]) >>
  drule_all annassign_empty_parts_mem >>
  disch_then (qx_choosel_then [`sA`, `vv`, `sB`] strip_assume_tac) >>
  `cs_extends sA sB` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sb func` by
    (qspecl_then [`sA`, `sB`, `sb`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sa sA func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by
    metis_tac[] >>
  `STRING #"%" (toString sa.cs_next_var) = STRING #"%" (toString sa.cs_next_var)` by
    simp[] >>
  `type_memory_bytes cenv vtyp < dimword (:256)` by simp[] >>
  drule_all annassign_setup_body_gas_path_mem >>
  disch_then (qx_choose_then `salloc` strip_assume_tac) >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  drule annassign_admissible_type >> strip_tac >>
  `tyv' = tyv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tyv' = tyv` SUBST_ALL_TAC >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[annassign_admissible_rhs, forced_expr_admissible_raw] >>
  `gas_outcome T (cx_tops cx) (ctx,func) (eval_expr cx e) (es,salloc)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func c cx e es sA sB salloc ee tv vv t /\
      vv_store_bound cx (expr_type e) (lowered_value_type c e) ee tv vv t /\
      t.vs_current_bb = sB.cs_current_bb /\
      t.vs_inst_idx = LENGTH sB.cs_current_insts /\
      alloca_history func t /\ salloc.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
     simp[expr_vv_sim_mem_def] >> disch_then irule >> simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sB.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         mk_inst_def, is_terminator_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sA x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     drule emit_inst_extends >> simp[]) >>
  irule annassign_raw_rhs_outcome_mem >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  qexists_tac `tyv` >>
  qpat_assum `evaluate_type (get_tenv cx) vtyp = SOME tyv`
    (fn th => simp[PULL_EXISTS, th]) >>
  rpt gen_tac >> strip_tac >>
  `!tail. eval_expr cx e
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL (Value v), ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `v = default_value tyv` by
    (first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs tv es1. _` drule >> simp[]) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by
    simp[bind_def, read_result_def, return_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  `FLOOKUP t.vs_allocas st.cs_next_id =
     SOME (w2n w, type_memory_bytes cenv vtyp)` by metis_tac[] >>
  `val_in_memory tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w t).vs_memory /\
   val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
    (irule memory_length_word_layout >> simp[mstore_mem_word_at_same] >>
     metis_tac[]) >>
  `memory_value_rel tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w t).vs_memory` by
    metis_tac[val_in_memory_memory_value_rel,
              vyperTypeDefaultsTheory.default_value_has_type_thm] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `w2n w + 32 <= t.vs_alloca_next` by decide_tac >>
  `eval_operand (Lit 0w) t = SOME 0w` by simp[eval_operand_def] >>
  drule_all annassign_word_mstore_path_mem >> strip_tac >>
  qabbrev_tac `u = mstore (w2n w) 0w t
                  with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `ee' = ee with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` >>
  `not_local_ptr c ee.scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func c cx ee' u` by
    (simp[Abbr `u`, Abbr `ee'`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_declare_store >> simp[] >>
     qexists_tac `mk_inst st.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes cenv vtyp))] [p]` >>
     gvs[mk_inst_def]) >>
  `!x. lookup_var x u = lookup_var x t` by
    simp[Abbr `u`, lookup_var_def, mstore_def, LET_THM] >>
  `sb.cs_current_bb = sB.cs_current_bb` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    gvs[Abbr `u`, mstore_def, LET_THM] >>
  qexistsl_tac [`ee'`, `u`] >>
  conj_tac
  >- (qpat_x_assum `v = default_value tyv` SUBST_ALL_TAC >>
      simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      simp[Abbr `ee'`]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `compile_expr _ _ _ sA = _`
       (strip_assume_tac o MATCH_MP (cj 1 compile_expr_grows)) >>
     qpat_x_assum `emit_void MSTORE _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     qpat_x_assum `emit_inst ALLOCA _ _ _ = _`
       (strip_assume_tac o MATCH_MP emit_inst_extends) >>
     gvs[]) >>
  `!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
          lookup_var x u = SOME w'` by
    metis_tac[] >>
  `cenv_top_ext cenv c ee'.scopes` by
    (simp[Abbr `ee'`] >> irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl_tac [`id`, `sa`, `st`, `vtyp`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `return_buf_frame d c sb u` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  simp[stmt_lands_def]
QED
