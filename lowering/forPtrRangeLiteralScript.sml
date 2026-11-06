(* Literal-range consumer of the checked allocation, initialization and loop
   boundaries.  No additional source or ghost invariant is defined here. *)
Theory forPtrRangeLiteral
Ancestors forPtrRangeEntry forPtrAllocationGhost forPtrRangeLoop
  stmtSimForParts stmtSimFor stmtSimDeclCompose stmtSimProps
  stmtSimDefs loweringPosts stmtLowering exprLoweringProps
  vyperInterpreter vyperState vyperValue vyperValueOperation
  gasSummaryComposePtr stmtFragPtr integer_word bodyPtrDefs compileEnv exprSimWordArgs
  forPtrRangeSource gasContext gasOutcomeInitialObsPtr
  stmtSimForLoop localPtrsProps loweringSlice emitHelperProps venomInst exprSimProps
  venomExecSemantics venomState fragExec fragGasPathPtr ptrSafeRun ptrDiscipline list rich_list finite_map
Libs monadsyntax intLib

Theorem for_ptr_literal_source_action[local]:
  evaluate_type (get_tenv cx) fty = SOME tyv /\
  n1 <= n2 /\ Num (n2 - n1) <= bound ==>
  eval_stmt cx
    (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
       bound stmts) =
  eval_for cx tyv id stmts
    (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       lift_option_type_def, lift_option_def, return_def, raise_def,
       eval_iterator_range_lit, check_def, assert_def, compatible_bound_def]
QED

Theorem compile_for_range_frag_ptr:
  !d PG P ctx func cx lctx RetQ cenv ty id fty e1 n1 e2 n2 bound stmts es tyv.
    eval_expr cx e1 es = (INL (Value (IntV n1)), es) /\
    eval_expr cx e2 es = (INL (Value (IntV n2)), es) /\
    (!s. lower_value compile_expr cenv fty e1 s = (Lit (i2w n1), s)) /\
    (!s. lower_value compile_expr cenv fty e2 s = (Lit (i2w n2), s)) /\
    (?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
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
       stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with <|scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
            gas_obs := []|>)) /\
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
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  rpt gen_tac >> strip_tac >> gvs[eval_expr_int_lit] >>
  rewrite_tac[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all for_ptr_literal_source_action >> disch_then (fn th => fs[th]) >>
  gvs[lower_value_int_lit] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty
    (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
      bound stmts) sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = ((), sb)` >>
  drule compile_for_range_lit_parts >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  suspend "layout"
QED

Resume compile_for_range_frag_ptr[layout]:
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
   cv <> ev /\ cv <> p /\ ev <> p` by (fs[] >> rw[] >> fs[]) >>
  `!n. sa.cs_next_var <= n ==>
    (!scs. not_local_ptr cenv scs (STRING #"%" (toString n))) /\
    (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString n))` by
    (gen_tac >> disch_tac >> conj_tac
     >- (gen_tac >> irule reserved_fresh_not_local >> metis_tac[]) >>
     simp[not_fresh_at_def]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs ev) /\
   (!scs. not_local_ptr cenv scs dv) /\ (!scs. not_local_ptr cenv scs nv) /\
   (!scs. not_local_ptr cenv scs p)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `ev = _` SUBST1_TAC >>
     qpat_assum `dv = _` SUBST1_TAC >> qpat_assum `nv = _` SUBST1_TAC >>
     qpat_assum `p = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `sa` >> fs[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb _ = _`
       (mp_then Any mp_tac lookup_block_fn_insts) >> simp[]) >>
  `for_code func cenv bc ty stmts id tyv p sz A cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl (sa.cs_next_id + 5)
      (sa.cs_next_id + 6) (sa.cs_next_id + 7) bbb sj.cs_next_id
      (sj.cs_next_id + 1) (sj.cs_next_id + 2) sb0 sb1 sj` by
    (simp[for_code_def, Abbr `A`] >>
     conj_tac >- simp[block_is_terminated_def, mk_inst_def, is_terminator_def] >>
     simp[not_fresh_at_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> x <> p /\ x <> cv /\ x <> ev /\ x <> dv /\ x <> nv` by
    (rw[not_fresh_at_def] >> fs[] >>
     qpat_x_assum `sb0.cs_next_var <= sb1.cs_next_var` mp_tac >> fs[]) >>
  suspend "allocation"
QED

Resume compile_for_range_frag_ptr[allocation]:
  `get_instruction
    <|bb_label := sa.cs_current_bb; bb_instructions :=
      sa.cs_current_insts ++ [A; mk_inst (sa.cs_next_id + 1) JMP [Label entry_lbl] []]|>
    s0.vs_inst_idx = SOME A` by simp[get_instruction_def, EL_APPEND_EQN] >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var p) q)` by metis_tac[] >>
  `?u a.
    step_inst_base A s0 = OK u /\
    stmt_state_rel ctx func cenv cx es u /\ lookup_var p u = SOME a /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n a,sz) /\
    u.vs_current_bb = s0.vs_current_bb /\ u.vs_inst_idx = s0.vs_inst_idx /\
    ~u.vs_halted /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0
      (step_prov PG G0 A u) (step_taint A s0 u tn0)
      (OK (u with vs_inst_idx := SUC s0.vs_inst_idx)) /\
    ptr_covers (step_prov PG G0 A u) (step_taint A s0 u tn0) p u sz /\
    (!name lo z. local_region cenv es.scopes s0 name lo z ==>
      regions_disjoint (w2n a) sz lo z) /\
    (!x. x <> p ==> lookup_var x u = lookup_var x s0 /\
      FLOOKUP (step_prov PG G0 A u) x = FLOOKUP G0 x /\
      op_taint (step_taint A s0 u tn0) (Var x) = op_taint tn0 (Var x))` by
    (simp[NoAsms, Abbr `A`] >>
     irule for_range_alloca_entry_path_ptr >> simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx es (step_prov PG G0 A u) (step_taint A s0 u tn0) u` by
    (simp[Abbr `A`] >> irule for_alloca_ghost_inv >> simp[] >> metis_tac[]) >>
  suspend "initialization"
QED

Resume compile_for_range_frag_ptr[initialization]:
  qabbrev_tac `Ga = step_prov PG G0 A u` >>
  qabbrev_tac `ta = step_taint A s0 u tn0` >>
  qabbrev_tac `cc = jump_to cond_lbl
    (update_var ev (i2w n2) (update_var cv (i2w n1) (jump_to entry_lbl u)))` >>
  qabbrev_tac `Gc = DRESTRICT (DRESTRICT Ga (COMPL {cv})) (COMPL {ev})` >>
  qabbrev_tac `tc = ta with t_var := (ta.t_var |+ (cv,{})) |+ (ev,{})` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG Ga ta
    (u with vs_inst_idx := SUC s0.vs_inst_idx) 0 Ga ta
    (OK (jump_to entry_lbl u))` by
    (simp[NoAsms, jump_to_def] >> irule (SRULE [jump_to_def] (Q.INST
       [`s` |-> `u with vs_inst_idx := SUC s0.vs_inst_idx`]
       (SPEC_ALL for_range_jump_path_ptr))) >>
     simp[get_instruction_def, EL_APPEND_EQN, jump_to_def] >> metis_tac[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG Ga ta (jump_to entry_lbl u) 0 Gc tc
    (OK cc)` by
    (simp[Abbr `cc`, Abbr `Gc`, Abbr `tc`] >>
     irule (SRULE [wordsTheory.WORD_SUB_ADD2]
       (Q.INST [`a` |-> `i2w n1`, `b` |-> `i2w n2 - i2w n1`]
         (SPEC_ALL for_range_literal_entry_path_ptr))) >>
     simp[jump_to_def] >> metis_tac[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 Gc tc (OK cc)` by
    (rev_dxrule gas_path_ptr_then >> disch_then dxrule >> simp[] >> strip_tac >>
     gvs[] >> dxrule gas_path_ptr_then >> disch_then drule >> simp[]) >>
  `ghost_inv d cenv cx es Gc tc cc` by
    (simp[NoAsms, Abbr `cc`, Abbr `Gc`, Abbr `tc`] >>
     irule (SRULE [] for_range_literal_entry_ghost) >>
     simp[stmtFragPtrTheory.ghost_inv_jump_to, jump_to_def] >> metis_tac[]) >>
  suspend "entry_state"
QED

Resume compile_for_range_frag_ptr[entry_state]:
  `stmt_state_rel ctx func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to]) >>
  `lookup_var cv cc = SOME (i2w n1) /\ lookup_var ev cc = SOME (i2w n2) /\
    FLOOKUP Gc cv = NONE /\ FLOOKUP Gc ev = NONE /\
    op_taint tc (Var cv) = {} /\ op_taint tc (Var ev) = {} /\
    ptr_covers Gc tc p cc sz /\
    (!x. x <> cv /\ x <> ev ==>
      lookup_var x cc = lookup_var x (jump_to entry_lbl u) /\
      FLOOKUP Gc x = FLOOKUP Ga x /\ op_taint tc (Var x) = op_taint ta (Var x))` by
    (irule for_range_literal_entry_frame >>
     simp[Abbr `cc`, Abbr `Gc`, Abbr `tc`] >>
     (conj_tac >- (qexists_tac `cond_lbl` >> simp[])) >>
     qpat_x_assum `ptr_covers Ga ta p u sz` mp_tac >>
     simp[ptr_covers_def, jump_to_def, lookup_var_def] >>
     gvs[lookup_var_def]) >>
  `(!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x cc = SOME v) /\
   (!x. not_fresh_at sa x ==> FLOOKUP Gc x = FLOOKUP G0 x /\
      op_taint tc (Var x) = op_taint tn0 (Var x))` by
    (simp[jump_to_def, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `lookup_var p cc = SOME a /\
   FLOOKUP cc.vs_allocas sa.cs_next_id = SOME (w2n a,sz) /\
   cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted` by
    (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  `!name lo z. local_region cenv es.scopes cc name lo z ==>
     regions_disjoint (w2n a) sz lo z` by
    (rpt strip_tac >>
     `local_ptrs_rel func cenv es.scopes s0` by fs[stmt_state_rel_def, state_rel_def] >>
     `local_region cenv es.scopes s0 name lo z` by
       (irule local_region_frame >> metis_tac[]) >> metis_tac[]) >>
  suspend "loop"
QED

Resume compile_for_range_frag_ptr[loop]:
  qabbrev_tac `vs = GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))` >>
  qabbrev_tac `Inv = \j ei G tn s.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j <= Num (n2-n1) /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx ei s /\ ghost_inv d cenv cx ei G tn s /\
    lookup_var cv s = SOME (i2w (n1 + &j)) /\
    lookup_var ev s = SOME (i2w n2) /\ lookup_var p s = SOME a /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas A.inst_id = SOME (w2n a,sz) /\
    (!name lo z. local_region cenv ei.scopes s name lo z ==>
      regions_disjoint (w2n a) sz lo z) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))` >>
  qabbrev_tac `Done = \ei G tn t.
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx ei t /\ ghost_inv d cenv cx ei G tn t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x t = SOME v) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))` >>
  `Inv 0 (es with gas_obs := []) Gc tc cc` by
    (gvs[Abbr `Inv`, Abbr `A`, stmt_state_rel_gas_obs, ghost_inv_gas_obs,
         mk_inst_def, jump_to_def, lookup_var_def] >> first_assum ACCEPT_TAC) >>
  suspend "loop_outcome"
QED

Resume compile_for_range_frag_ptr[loop_outcome]:
  drule (Q.INST [`P` |-> `\ei. P ei /\ lookup_scopes id ei.scopes = NONE`]
    (SPEC_ALL for_range_loop_ptr)) >>
  disch_then (drule_at (Pat `Inv _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`st` |-> `sa`] o SPEC_ALL) >>
  (impl_tac >-
    (reverse conj_tac >- simp[gas_admissible_gas_obs] >>
     suspend "loop_static")) >>
  simp[DROP_0] >> strip_tac >> suspend "finish"
QED

Resume compile_for_range_frag_ptr[loop_static]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!st0 c st1 ex inc ei j. _` irule >>
      gvs[Abbr `vs`] >> qexists_tac `sa` >> simp[]) >>
  conj_tac >- simp[Abbr `Inv`, SF CONJ_ss] >>
  conj_tac >- simp[Abbr `Done`] >>
  conj_tac
  >- (simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >>
      drule for_body_outer_preserves >>
      disch_then (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
      simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [] >> rpt strip_tac >> irule not_local_ptr_name_update >>
      qexistsl_tac [`cenv`, `id`] >> simp[] >>
      qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  simp[Abbr `vs`] >> conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  rpt gen_tac >> disch_tac >> simp[] >> irule i2w_counter_ne >> simp[]
QED

Resume compile_for_range_frag_ptr[finish]:
  fs[gas_outcome_ptr_initial_obs] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_outcome_ptr_prefix) >>
  disch_then drule >> strip_tac >>
  drule gas_outcome_ptr_conseq >>
  disch_then irule >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[Abbr `Done`] >>
      simp[cenv_top_ext_refl, stmt_lands_def, block_is_terminated_def]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

Finalise compile_for_range_frag_ptr
