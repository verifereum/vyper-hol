(* Checked Range compilation after both lower_value calls, with the body
   intervals taken from the same real/shadow compilations. *)
Theory bodyForRangeCheckedCodeMods
Ancestors
  bodyFullForRange stmtSimForRange stmtSimForArrayParts stmtSimForLoop
  stmtSimProps stmtLoweringMono stmtLowering stmtFragPtr fragExec compileEnv emitHelper
  gasShadow gasShadowState gasShadowCompileStmtBase gasShadowStmtEnv
  exprLoweringProps localPtrsProps vyperValue loweringStateRelDefs gasShadowCompileBase

val _ = Parse.hide "body";

(* Record the exact initial body state: its block stack includes the three
   blocks emitted by the checked prelude, not just the current MSTORE. *)
Theorem checked_range_suffix[local]:
  cenv.ce_alloca_locals /\
  for_range_checked_code cenv lctx ty id typ bound body op1 op2 st = ((),sf) ==>
  let p = STRING #"%" (toString st.cs_next_var);
      cv = STRING #"%" (toString (st.cs_next_var + 1));
      rv = STRING #"%" (toString (st.cs_next_var + 2));
      g1 = STRING #"%" (toString (st.cs_next_var + 3));
      z1 = STRING #"%" (toString (st.cs_next_var + 4));
      g2 = STRING #"%" (toString (st.cs_next_var + 5));
      z2 = STRING #"%" (toString (st.cs_next_var + 6));
      ev = STRING #"%" (toString (st.cs_next_var + 7));
      dv = STRING #"%" (toString (st.cs_next_var + 8));
      en = fresh_label_output "for_entry" st.cs_next_label;
      co = fresh_label_output "for_cond" (st.cs_next_label + 1);
      bo = fresh_label_output "for_body" (st.cs_next_label + 2);
      inc = fresh_label_output "for_incr" (st.cs_next_label + 3);
      ex = fresh_label_output "for_exit" (st.cs_next_label + 4);
      ainst = mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p];
      pre = <|bb_label := st.cs_current_bb; bb_instructions :=
                st.cs_current_insts ++ [ainst; mk_inst (st.cs_next_id + 1) JMP [Label en] []]|>;
      entry = <|bb_label := en; bb_instructions :=
                [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
                 mk_inst (st.cs_next_id + 3) SUB [op2;op1] [rv];
                 mk_inst (st.cs_next_id + 4) (if is_signed_type typ then SGT else GT) [op1;op2] [g1];
                 mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
                 mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
                 mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
                 mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
                 mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
                 mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
                 mk_inst (st.cs_next_id + 11) JMP [Label co] []]|>;
      cond = <|bb_label := co; bb_instructions :=
                [mk_inst (st.cs_next_id + 12) EQ [Var cv; Var ev] [dv];
                 mk_inst (st.cs_next_id + 13) JNZ [Var dv; Label ex; Label bo] []]|>
  in
    ?bc b0 b1 bj ib.
      declare_local cenv id typ st = (bc,st with cs_next_var := st.cs_next_var + 1) /\
      b0 = st with <|cs_next_var := st.cs_next_var + 9;
                     cs_next_id := st.cs_next_id + 15;
                     cs_next_label := st.cs_next_label + 5;
                     cs_current_bb := bo;
                     cs_current_insts := [mk_inst (st.cs_next_id + 14) MSTORE [Var p;Var cv] []];
                     cs_blocks := cond::entry::pre::st.cs_blocks|> /\
      compile_stmts bc (InLoop ex inc) ty body b0 = ((),b1) /\
      emit_jmp_if_not_terminated inc b1 = ((),bj) /\
      ib = <|bb_label := inc; bb_instructions :=
              [mk_inst bj.cs_next_id ADD [Var cv;Lit 1w] [STRING #"%" (toString bj.cs_next_var)];
               mk_inst (bj.cs_next_id + 1) ASSIGN [Var (STRING #"%" (toString bj.cs_next_var))] [cv];
               mk_inst (bj.cs_next_id + 2) JMP [Label co] []]|> /\
      sf = bj with <|cs_next_var := bj.cs_next_var + 1;
                     cs_next_id := bj.cs_next_id + 3;
                     cs_current_bb := ex; cs_current_insts := [];
                     cs_blocks := [ib; <|bb_label := bj.cs_current_bb;
                                         bb_instructions := bj.cs_current_insts|>] ++ bj.cs_blocks|>
Proof
  strip_tac >>
  namedCases_on `declare_local cenv id typ st` ["bc u"] >>
  drule_all declare_local_ptr >> strip_tac >>
  `(if is_signed_type typ then emit_op SGT [op1;op2] else emit_op GT [op1;op2]) =
     emit_op (if is_signed_type typ then SGT else GT) [op1;op2]` by
    (Cases_on `is_signed_type typ` >> simp[]) >>
  qpat_x_assum `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[for_range_checked_code_def, compile_range_bound_checks_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
       comp_get_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_jmp_if_not_terminated _ b1 = ((),bj)` >>
  disch_then (SUBST1_TAC o SYM) >>
  qexistsl_tac [`b1`,`bj`] >> simp[] >>
  qpat_assum `compile_stmts _ _ _ _ _ = _`
    (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC,listTheory.APPEND])
QED

Theorem checked_suffix_extends[local]:
  t.cs_blocks = [b; <|bb_label := s.cs_current_bb;
                      bb_instructions := s.cs_current_insts|>] ++ s.cs_blocks ==>
  cs_extends s t
Proof
  strip_tac >> simp[cs_extends_def] >> qexists_tac `[b; _]` >> simp[]
QED

Theorem checked_shadow_declare[local]:
  gas_shadow_state st shst /\
  declare_local cenv id typ st = (bc,u) /\
  declare_local (gas_shadow_env T cenv) id typ shst = (shbc,shu) ==>
  shbc = gas_shadow_env T bc
Proof
  strip_tac >>
  mp_tac (Q.INST [`sd` |-> `T`, `ty` |-> `typ`]
    gas_shadow_compiles_env_declare_local) >>
  simp[gas_shadow_compiles_env_def, PULL_FORALL] >>
  disch_then (qspecl_then [`st`,`shst`] mp_tac) >> simp[]
QED

Theorem checked_blocks_lookup[local]:
  fn_has_code s t func /\ t.cs_blocks = new ++ s.cs_blocks ==>
  EVERY (\bb. lookup_block bb.bb_label func.fn_blocks = SOME bb) new
Proof
  strip_tac >> drule emitted_blocks_append >> strip_tac >>
  fs[fn_has_code_def, listTheory.EVERY_MEM]
QED

(* The endpoints, their emitted operands and both suffix intervals are
   fixed by the caller. Only the declared-body witnesses are chosen here. *)
Theorem range_checked_code_mods:
  stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) a = (cenv,b) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (For id typ (Range e1 e2) bound body)) sha = (gas_shadow_env T cenv,shb) /\
  ~(?u i v j. e1 = Literal u (IntL i) /\ e2 = Literal v (IntL j)) /\
  lower_value compile_expr cenv typ e1 a = (op1,m) /\
  lower_value compile_expr cenv typ e2 m = (op2,st) /\
  lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) sha = (op1,shm) /\
  lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) shm = (op2,shst) /\
  gas_shadow_state st shst /\
  fn_has_code st b func /\ fn_has_code shst shb shadow_func /\
  cenv.ce_alloca_locals /\ local_ptrs_reserved cenv a /\
  fn_inst_ids_distinct func /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  is_int_type typ /\ evaluate_type tenv typ = SOME tyv ==>
  let p = STRING #"%" (toString st.cs_next_var);
      cv = STRING #"%" (toString (st.cs_next_var + 1));
      rv = STRING #"%" (toString (st.cs_next_var + 2));
      g1 = STRING #"%" (toString (st.cs_next_var + 3));
      z1 = STRING #"%" (toString (st.cs_next_var + 4));
      g2 = STRING #"%" (toString (st.cs_next_var + 5));
      z2 = STRING #"%" (toString (st.cs_next_var + 6));
      ev = STRING #"%" (toString (st.cs_next_var + 7));
      dv = STRING #"%" (toString (st.cs_next_var + 8));
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label;
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1);
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2);
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3);
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4);
      sz = type_memory_bytes cenv typ;
      ainst = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]
  in
    cs_extends a st /\ a.cs_next_var <= st.cs_next_var /\ a.cs_next_id <= st.cs_next_id /\
    cs_extends st b /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions :=
              st.cs_current_insts ++ [ainst; mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
    lookup_block entry_lbl func.fn_blocks =
      SOME <|bb_label := entry_lbl; bb_instructions :=
              [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
               mk_inst (st.cs_next_id + 3) SUB [op2;op1] [rv];
               mk_inst (st.cs_next_id + 4) (if is_signed_type typ then SGT else GT) [op1;op2] [g1];
               mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
               mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
               mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
               mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
               mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
               mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
               mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []]|> /\
    ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev;dv] /\
    (!x. MEM x [p;cv;rv;g1;z1;g2;z2;ev;dv] ==> ~not_fresh_at st x) /\
    ~not_fresh_at a dv /\ b.cs_current_bb = exit_lbl /\ b.cs_current_insts = [] /\
    ?bc body_cenv b0 b1 j shb0 shb1 bbb.
      declare_local cenv id typ st = (bc,st with cs_next_var := st.cs_next_var + 1) /\
      cs_extends st b0 /\ cs_extends a b0 /\
      a.cs_next_id <= b0.cs_next_id /\ a.cs_next_var <= b0.cs_next_var /\
      b0.cs_next_var = st.cs_next_var + 9 /\ b0.cs_next_var <= b.cs_next_var /\
      (!x. not_fresh_at a x ==> not_fresh_at b0 x) /\
      b0.cs_current_insts = [mk_inst (st.cs_next_id + 14) MSTORE [Var p;Var cv] []] /\
      for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv
        (STRING #"%" (toString j.cs_next_var)) cond_lbl exit_lbl body_lbl incr_lbl
        (st.cs_next_id + 12) (st.cs_next_id + 13) (st.cs_next_id + 14) bbb
        j.cs_next_id (j.cs_next_id + 1) (j.cs_next_id + 2) b0 b1 j /\
      j.cs_next_var = b1.cs_next_var /\
      cs_extends shst shb0 /\ cs_extends shb1 shb /\
      stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body b0 = (body_cenv,b1) /\
      stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
        (MAP gas_shadow_stmt body) shb0 = (gas_shadow_env T body_cenv,shb1) /\
      gas_shadow_state b0 shb0 /\ gas_shadow_state b1 shb1 /\
      fn_has_code b0 b1 func /\ fn_has_code shb0 shb1 shadow_func
Proof
  pure_rewrite_tac [range_full_outer_env] >> strip_tac >>
  `!e u i. gas_shadow_expr e = Literal u (IntL i) ==> e = Literal u (IntL i)` by
    (Cases >> simp[gas_shadow_expr_def]) >>
  `~(?u i v j. gas_shadow_expr e1 = Literal u (IntL i) /\
              gas_shadow_expr e2 = Literal v (IntL j))` by metis_tac[] >>
  `for_range_checked_code cenv lctx ret_ty id typ bound body op1 op2 st = ((),b)` by
    (qpat_assum `compile_stmt cenv _ _ _ a = _` (SUBST1_TAC o SYM) >>
     sym_tac >> irule compile_stmt_for_range_checked >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `m` >> simp[]) >>
  `for_range_checked_code (gas_shadow_env T cenv) lctx ret_ty id typ bound
     (MAP gas_shadow_stmt body) op1 op2 shst = ((),shb)` by
    (qpat_assum `compile_stmt (gas_shadow_env T cenv) _ _ _ sha = _` (SUBST1_TAC o SYM) >>
     sym_tac >> irule compile_stmt_for_range_checked >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `shm` >> simp[]) >>
  `(gas_shadow_env T cenv).ce_alloca_locals` by simp[gas_shadow_env_def] >>
  qpat_assum `for_range_checked_code cenv _ _ _ _ _ _ _ _ st = _`
    (mp_then Any mp_tac (GEN_ALL checked_range_suffix)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`bc`,`b0`,`b1`,`j`,`ib`] strip_assume_tac o
              CONV_RULE (TOP_DEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))) >>
  qpat_assum `for_range_checked_code (gas_shadow_env T cenv) _ _ _ _ _ _ _ _ shst = _`
    (mp_then Any mp_tac (GEN_ALL checked_range_suffix)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`shbc`,`shb0`,`shb1`,`shj`,`shib`] strip_assume_tac o
              CONV_RULE (TOP_DEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))) >>
  `shbc = gas_shadow_env T bc` by (drule_all checked_shadow_declare >> simp[]) >>
  qpat_x_assum `shbc = _` SUBST_ALL_TAC >>
  `st.cs_next_label = shst.cs_next_label` by fs[gas_shadow_state_def] >>
  `gas_shadow_state b0 shb0` by
    (qpat_assum `b0 = _` (SUBST1_TAC o SYM) >>
     qpat_assum `shb0 = _` (SUBST1_TAC o SYM) >>
     qpat_assum `gas_shadow_state st shst` (strip_assume_tac o REWRITE_RULE [gas_shadow_state_def]) >>
     simp[gas_shadow_state_def, gas_shadow_block_def, listTheory.LIST_REL_APPEND,
          gas_shadow_inst_def, venomInstTheory.mk_inst_def] >>
     irule listTheory.LIST_REL_APPEND_suff >> simp[gas_shadow_inst_def]) >>
  `cs_extends st b0` by
    (qpat_assum `b0 = _` (SUBST1_TAC o SYM) >> simp[cs_extends_def] >>
     qexists_tac `[_;_;_]` >> simp[]) >>
  `cs_extends shst shb0` by
    (qpat_assum `shb0 = _` (SUBST1_TAC o SYM) >> simp[cs_extends_def] >>
     qexists_tac `[_;_;_]` >> simp[]) >>
  qpat_assum `emit_jmp_if_not_terminated _ b1 = _`
    (mp_then Any strip_assume_tac array_body_backedge) >>
  qpat_assum `emit_jmp_if_not_terminated _ shb1 = _`
    (mp_then Any strip_assume_tac array_body_backedge) >>
  `cs_extends j b` by
    (irule checked_suffix_extends >> qexists_tac `ib` >> simp[]) >>
  `cs_extends shj shb` by
    (irule checked_suffix_extends >> qexists_tac `shib` >> simp[]) >>
  `cs_extends shb1 shb` by (irule cs_extends_trans >> qexists_tac `shj` >> simp[]) >>
  `cs_extends b1 b` by (irule cs_extends_trans >> qexists_tac `j` >> simp[]) >>
  qpat_assum `compile_stmts bc _ _ body b0 = _`
    (mp_then Any strip_assume_tac (REWRITE_RULE [cs_mono_def] (cj 2 compile_stmt_cs_mono))) >>
  `cs_extends st b1` by (irule cs_extends_trans >> qexists_tac `b0` >> simp[]) >>
  `cs_extends st j` by (irule cs_extends_trans >> qexists_tac `b1` >> simp[]) >>
  `cs_extends st b` by (irule cs_extends_trans >> qexists_tac `j` >> simp[]) >>
  `fn_has_code b0 b1 func` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`b`,`st`] >> simp[]) >>
  `fn_has_code b1 j func` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`b`,`st`] >> simp[]) >>
  `fn_has_code j b func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_assum `st.cs_next_label = shst.cs_next_label` (fn eq =>
    qpat_x_assum `compile_stmts _ _ _ (MAP gas_shadow_stmt body) shb0 = _`
      (assume_tac o PURE_REWRITE_RULE [SYM eq])) >>
  drule_all range_body_pair_containment >>
  disch_then (qx_choose_then `body_cenv` strip_assume_tac) >>
  `cs_extends b0 b` by
    (irule cs_extends_trans >> qexists_tac `b1` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code st b0 func` by
    (qpat_assum `cs_extends st b0` (mp_then (Pos hd) (drule_all_then strip_assume_tac) fn_has_code_split) >>
     first_assum ACCEPT_TAC) >>
  `b0.cs_blocks = TAKE 3 b0.cs_blocks ++ st.cs_blocks` by simp[] >>
  qpat_assum `b0.cs_blocks = _`
    (mp_then Any (drule_then mp_tac) (GEN_ALL checked_blocks_lookup)) >>
  simp[] >> strip_tac >>
  `b.cs_blocks = [ib; <|bb_label := j.cs_current_bb;
                         bb_instructions := j.cs_current_insts|>] ++ j.cs_blocks` by simp[] >>
  qpat_assum `b.cs_blocks = _`
    (mp_then Any (drule_then mp_tac) (GEN_ALL checked_blocks_lookup)) >>
  simp[] >> strip_tac >>
  `?bbb. lookup_block b0.cs_current_bb func.fn_blocks = SOME bbb /\
         isPREFIX b0.cs_current_insts bbb.bb_instructions` by
    (irule fn_has_code_start >> qexists_tac `b1` >> simp[]) >>
  rename1 `lookup_block b0.cs_current_bb func.fn_blocks = SOME bbb` >>
  qpat_assum `lower_value _ _ _ e1 a = _` (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 m = _` (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  `cs_extends a st` by (irule cs_extends_trans >> qexists_tac `m` >> simp[]) >>
  `cs_extends a b0` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `a.cs_next_var <= st.cs_next_var /\ a.cs_next_id <= st.cs_next_id` by decide_tac >>
  `!x. not_fresh_at a x ==> not_fresh_at b0 x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  qpat_assum `declare_local cenv id typ st = _` (mp_then Any (drule_then strip_assume_tac) declare_local_ptr) >>
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `local_ptrs_reserved bc b0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `st with cs_next_var := st.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> goal_assum (drule_at Any) >> qexistsl_tac [`id`,`typ`] >> simp[]) >>
  `32 <= type_memory_bytes cenv typ /\ type_memory_size tyv = 32 /\ word_memory_type tyv` by
    (qpat_x_assum `is_int_type typ` mp_tac >>
     qpat_x_assum `evaluate_type tenv typ = SOME tyv` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `typ` >> simp[] >> rename1 `BaseT bt` >>
     Cases_on `bt` >> simp[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def] >>
     rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def, loweringSliceTheory.word_memory_type_def]) >>
  `b0.cs_next_var = st.cs_next_var + 9` by simp[] >>
  `st.cs_next_var + 9 <= b1.cs_next_var` by decide_tac >>
  simp[ASCIInumbersTheory.toString_inj] >>
  conj_tac >- simp[not_fresh_at_def, DISJ_IMP_THM, FORALL_AND_THM, ASCIInumbersTheory.toString_inj] >>
  conj_tac >- simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  qexistsl_tac [`body_cenv`,`b0`,`b1`,`j`,`shb0`,`shb1`,`bbb`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (simp[] >> decide_tac) >>
  conj_tac >- (simp[] >> decide_tac) >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  reverse conj_tac >-
    (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qpat_x_assum `cs_extends shb1 shb` mp_tac >> simp[]) >>
     conj_tac >- (qpat_x_assum `stmts_env bc _ _ body b0 = _` mp_tac >> simp[]) >>
     conj_tac >- (qpat_x_assum `stmts_env _ _ _ (MAP gas_shadow_stmt body) shb0 = _` mp_tac >> simp[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[for_code_def] >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))]
          [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st.cs_current_bb func.fn_blocks = SOME _` (irule_at Any) >> simp[]) >>
  `!n scs. st.cs_next_var <= n ==> not_local_ptr cenv scs (STRING #"%" (toString n))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj, block_is_terminated_def,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  conj_tac >-
    (qpat_x_assum `lookup_block b0.cs_current_bb func.fn_blocks = SOME bbb` mp_tac >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `isPREFIX b0.cs_current_insts bbb.bb_instructions` mp_tac >>
     Cases_on `bbb.bb_instructions` >>
     simp[venomInstTheory.get_instruction_def, venomInstTheory.mk_inst_def]) >>
  qpat_x_assum `compile_stmts bc _ _ body b0 = ((),b1)` mp_tac >>
  simp[venomInstTheory.mk_inst_def]
QED
