(* Memory-safe literal ranges: allocation/entry boundary, counted loop,
   and transport of the final frame back to the original fragment. *)
Theory stmtForRangeLitMemory
Ancestors
  stmtSimDefs exprSimMemDefs stmtLowering compileEnv loweringStateRelDefs vyperInterpreter
  vyperState stmtForRangeMemoryLoop stmtForRangeMemoryParts stmtForRangeMemoryStart
  stmtForRangeMemoryRound stmtLoweringMono
  stmtSimForParts stmtSimProps stmtSimForLoop loweringSlice loweringPosts vyperValue
  exprLoweringProps stmtSimDeclPath venomExecSemantics venomInst
  venomState finite_map list fragExec

Theorem compile_for_range_lit_frag_mem:
  !P d ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es tyv.
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    word_memory_type tyv /\ 32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P (es with gas_obs := []) /\
    (!st0 c st1 ex inc ei j.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts))
      (eval_stmt cx
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  `eval_stmt cx
    (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound stmts) =
    eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))` by
    (simp[FUN_EQ_THM, Once evaluate_def, eval_iterator_range_lit,
       bind_def, ignore_bind_def, lift_option_type_def, lift_option_def,
       return_def, check_def, assert_def, compatible_bound_def]) >>
  rw[stmt_frag_mem_def] >>
  fs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, pairTheory.pair_case_eq] >>
  Cases_on `compile_stmt cenv lctx ty
    (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound stmts) sa` >>
  Cases_on `q` >> gvs[] >>
  drule compile_for_range_lit_parts >>
  disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >>
  qabbrev_tac `aa = mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv fty))] [p]` >>
  `not_local_ptr cenv es.scopes p` by
    (qpat_assum `p = _` SUBST1_TAC >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `MEM aa (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb _ = _`
       (mp_then Any mp_tac lookup_block_fn_insts) >> simp[]) >>
  `not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes ev` by
    (conj_tac
     >- (qpat_assum `cv = _` SUBST1_TAC >>
         irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `ev = _` SUBST1_TAC >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `?cc w. gas_path_mem ctx func s0 0 (OK cc) /\
     cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
     stmt_state_rel ctx func cenv cx es cc /\
     lookup_var cv cc = SOME (i2w n1) /\ lookup_var ev cc = SOME (i2w n2) /\
     lookup_var p cc = SOME w /\
     FLOOKUP cc.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_bytes cenv fty) /\
     return_buf_frame d cenv sa cc /\ ret_pc_ok cenv sa cc /\
     alloca_history func cc /\ s0.vs_alloca_next <= cc.vs_alloca_next /\
     (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
     (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0)` by
    (irule for_range_lit_start_mem >>
     simp[] >> conj_tac
     >- (map_every (fn q => qpat_assum q SUBST1_TAC) [`p = _`, `cv = _`, `ev = _`] >>
         simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
         rpt strip_tac >> gvs[] >> decide_tac) >>
     qexistsl_tac [`entry_lbl`, `sa.cs_next_id + 2`, `sa.cs_next_id + 3`,
       `sa.cs_next_id + 4`, `sa.cs_next_id + 1`] >> simp[]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved bc sb0` by
    (drule_all declare_local_reserved >> strip_tac >>
     irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[]) >>
  `sa.cs_next_var + 4 <= sj.cs_next_var` by
    (qpat_assum `!c lc sa sb. compile_stmts _ _ _ _ _ = _ ==> _`
       (qspecl_then [`bc`, `InLoop exit_lbl incr_lbl`, `sb0`, `sb1`] mp_tac) >> simp[]) >>
  suspend "loop"
QED

Resume compile_for_range_lit_frag_mem[loop]:
  `for_code func cenv bc ty stmts id tyv p (type_memory_bytes cenv fty) aa cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl (sa.cs_next_id + 5) (sa.cs_next_id + 6)
    (sa.cs_next_id + 7) bbb sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2)
    sb0 sb1 sj` by
    (simp[for_code_def, Abbr `aa`, mk_inst_def, block_is_terminated_def] >>
     simp[is_terminator_def, not_fresh_at_def] >>
     gen_tac >> rpt conj_tac >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY :: scs) p` by
    (rpt strip_tac >> irule local_ptrs_reserved_not_live >>
     conj_tac
     >- (qexistsl_tac [`id`, `type_memory_bytes cenv fty`] >> simp[lookup_scopes_def]) >>
     qexists_tac `sb0` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> dv /\ x <> cv /\ x <> nv` by
    (map_every (fn q => qpat_assum q SUBST1_TAC) [`dv = _`, `cv = _`, `nv = _`] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  `!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
     stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
       (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
       (ei with scopes := (FEMPTY |+ (id, <|assignable := F; type := tyv;
          value := IntV (n1 + &j); popped := []|>)) :: ei.scopes)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl_tac [`sa`, `sa with cs_next_var := sa.cs_next_var + 1`] >> simp[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(0 + j)))) (Num (n2-n1)))) (es,cc)
     (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
       s.vs_inst_idx = 0 /\ ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ee s /\
       return_buf_frame d cenv sa s /\ alloca_history func s /\
       cc.vs_alloca_next <= s.vs_alloca_next /\
       (!x v. not_fresh_at sa x /\ lookup_var x cc = SOME v ==> lookup_var x s = SOME v) /\
       (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b))
     (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (irule for_loop_mem >>
     ntac 4 (conj_tac >- simp[]) >>
     conj_tac >- (qexists_tac `lctx` >> simp[]) >>
     ntac 3 (conj_tac >- simp[]) >>
     qexists_tac `P` >> qhdtm_assum `for_code` (irule_at Any) >>
     qexistsl_tac [`w`, `n2`] >> simp[Abbr `aa`, mk_inst_def] >>
     rpt strip_tac >>
     qpat_x_assum `!ei j gs r2 es2 sc rest. _` irule >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "finish"
QED

Resume compile_for_range_lit_frag_mem[finish]:
  qpat_x_assum `gas_outcome T _ _ _ _ _ _` mp_tac >> simp[] >>
  disch_then (mp_then Any mp_tac for_outcome_zero_prefix_mem) >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >>
  disch_then (mp_then Any mp_tac for_outcome_consequence_mem) >>
  simp[] >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[stmt_lands_def, cenv_top_ext_def] >>
  conj_tac >- simp[block_is_terminated_def] >>
  Cases_on `d` >- gvs[return_buf_frame_def] >>
  rename1 `SOME desc` >> PairCases_on `desc` >>
  gvs[return_buf_frame_def] >>
  `sa.cs_next_var <= r.cs_next_var` by
    (drule (SIMP_RULE std_ss [cs_mono_def] (cj 1 compile_stmt_cs_mono)) >> simp[]) >>
  gvs[not_fresh_at_def] >> gen_tac >> disch_tac >>
  qpat_x_assum `!n. sa.cs_next_var <= n ==> _` irule >> decide_tac
QED

Finalise compile_for_range_lit_frag_mem
