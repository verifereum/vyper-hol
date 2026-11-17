(* Static and compiler boundaries for the full Range body case. *)
Theory bodyFullForRange
Ancestors
  bodyFullPreds bodyFullForFacts bodySimDeclCases bodySim
  stmtSimForParts stmtSimForRange exprLoweringProps freshWrites
  loweringStateRelDefs loweringPosts stmtLowering compileEnv
  supportedStmts supportedStmtTraverse supportedExprTraverse
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState vyperAST gasShadow
  ASCIInumbers integer list finite_map

val _ = Parse.hide "body";

Theorem range_full_body_ih:
  !cx tyv id body n1 N.
    body_for_full_ok cx tyv id body
      (GENLIST (\j. Value (IntV (n1 + &j))) N) /\ 0 < N ==>
    body_stmts_full_ok cx body
Proof
  rpt gen_tac >> Cases_on `N` >> simp[GENLIST_CONS, body_for_full_ok_def,
    read_result_def, return_def]
QED

Theorem range_full_outer_env:
  (stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) n body) sa =
     (cenv', sb) <=>
   cenv' = cenv /\
   compile_stmt cenv lctx ret_ty (For id typ (Range e1 e2) n body) sa =
     ((), sb)) /\
  (stmt_env cenv lctx ret_ty
     (gas_shadow_stmt (For id typ (Range e1 e2) n body)) ssa = (scenv', ssb) <=>
   scenv' = cenv /\
   compile_stmt cenv lctx ret_ty
     (For id typ (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) n
       (MAP gas_shadow_stmt body)) ssa = ((), ssb))
Proof
  simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
       gas_shadow_iterator_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt conj_tac >> pairarg_tac >> simp[EQ_SYM_EQ]
QED

(* Finite projections at exactly the enclosing For; no source invariant is
   strengthened here. Endpoint support remains in its literal/checked gate. *)
Theorem range_full_static_pre:
  supported_stmt tops bindings (For id typ (Range e1 e2) n body) /\
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (For id typ (Range e1 e2) n body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) n body)) ==>
  env' = env /\ assignable_type env.type_defs typ /\ is_int_type typ /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  expr_type e1 = typ /\ expr_type e2 = typ /\
  expr_writes_ok (\_. F) e1 /\ expr_writes_ok (\_. F) e2 /\
  expr_static_calls e1 /\ expr_static_calls e2 /\
  id NOTIN FDOM env.var_types /\
  IS_SOME (type_stmts (extend_local env id typ F) ret_ty body) /\
  supported_type_namespace typ /\ supported_iterator tops typ (Range e1 e2) n /\
  supported_stmts tops bindings body /\
  ~supported_stmts_expr_exists expr_internal_call_root body /\
  stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\
  type_memory_bytes cenv typ < 2 ** 64 /\
  alloc_limits_expr cenv e1 /\ alloc_limits_expr cenv e2 /\
  ~supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) e1 /\
  ~supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) e2 /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e1 ==>
      occurs_abi_decode_target target tops) /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e2 ==>
      occurs_abi_decode_target target tops) /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_expr e1) /\
  call_evaluation_safe cx (int_calls_expr e2) /\
  call_evaluation_safe cx (int_calls_stmts body)
Proof
  strip_tac >>
  drule type_stmt_for_projection >> strip_tac >>
  drule supported_stmt_for_projection >> strip_tac >>
  drule supported_loop_body_contract >> strip_tac >>
  drule body_for_exprs_ok >> strip_tac >>
  gvs[well_typed_iterator_def] >>
  qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
  simp[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       supported_iterator_exists_def, allocLimitsTheory.alloc_limits_stmt_def,
       allocLimitsTheory.alloc_limits_iterator_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[int_calls_stmt_def, int_calls_iterator_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  gvs[supported_stmt_expr_exists_def, supported_iterator_exists_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

(* Enriched elimination interfaces for the two actual compiler shapes. The
   original code equations are retained, together with ages at body entry.
   Source and shadow compiler states are deliberately independent. *)
Theorem range_full_compiler_geometry:
  (!cenv lctx ty id fty a1 n1 a2 n2 bound stmts sa cenv' sb
       ssa scenv' ssb func.
    stmt_env cenv lctx ty
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
        bound stmts) sa = (cenv', sb) /\
    stmt_env cenv lctx ty
      (gas_shadow_stmt
        (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
          bound stmts)) ssa = (scenv', ssb) /\
    cenv.ce_alloca_locals /\ fn_has_code sa sb func /\
    (!c lc s t. compile_stmts c lc ty stmts s = ((), t) ==> cs_extends s t) ==>
    cenv' = cenv /\ scenv' = cenv /\
    compile_stmt cenv lctx ty
      (For id fty
        (Range (gas_shadow_expr (Literal a1 (IntL n1)))
               (gas_shadow_expr (Literal a2 (IntL n2))))
        bound (MAP gas_shadow_stmt stmts)) ssa = ((), ssb) /\
    ?p cv ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl bc sb0 sb1 sj nv.
      p = STRING #"%" (toString sa.cs_next_var) /\
      cv = STRING #"%" (toString (sa.cs_next_var + 1)) /\
      ev = STRING #"%" (toString (sa.cs_next_var + 2)) /\
      dv = STRING #"%" (toString (sa.cs_next_var + 3)) /\
      entry_lbl = fresh_label_output "for_entry" sa.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (sa.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (sa.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (sa.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (sa.cs_next_label + 4) /\
      declare_local cenv id fty sa =
        (bc, sa with cs_next_var := sa.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = sa.cs_next_var + 4 /\ cs_extends sa sb0 /\
      sa.cs_next_id <= sb0.cs_next_id /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block sa.cs_current_bb func.fn_blocks =
        SOME <|bb_label := sa.cs_current_bb; bb_instructions :=
          sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv fty))] [p];
           mk_inst (sa.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <|bb_label := entry_lbl; bb_instructions :=
          [mk_inst (sa.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
           mk_inst (sa.cs_next_id + 3) ADD
             [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
           mk_inst (sa.cs_next_id + 4) JMP [Label cond_lbl] []]|> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <|bb_label := cond_lbl; bb_instructions :=
          [mk_inst (sa.cs_next_id + 5) EQ [Var cv; Var ev] [dv];
           mk_inst (sa.cs_next_id + 6) JNZ
             [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
        get_instruction bbb 0 =
          SOME (mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
        sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
        sj.cs_current_insts = sb1.cs_current_insts ++
          [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
        fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <|bb_label := incr_lbl; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
           mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
           mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
      sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
      not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
      sa.cs_next_var <= sb0.cs_next_var /\
      (!x. not_fresh_at sa x ==> not_fresh_at sb0 x)) /\
  (!cenv lctx ty id fty e1 e2 bound stmts sa cenv' sb ssa scenv' ssb
       op1 s1 op2 st func.
    stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts) sa = (cenv', sb) /\
    stmt_env cenv lctx ty (gas_shadow_stmt (For id fty (Range e1 e2) bound stmts))
      ssa = (scenv', ssb) /\
    lower_value compile_expr cenv fty e1 sa = (op1, s1) /\
    lower_value compile_expr cenv fty e2 s1 = (op2, st) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    cenv.ce_alloca_locals /\ fn_has_code sa sb func /\
    (!c lc s t. compile_stmts c lc ty stmts s = ((), t) ==> cs_extends s t) ==>
    cenv' = cenv /\ scenv' = cenv /\
    compile_stmt cenv lctx ty
      (For id fty (Range (gas_shadow_expr e1) (gas_shadow_expr e2)) bound
        (MAP gas_shadow_stmt stmts)) ssa = ((), ssb) /\
    ?p cv rv g1 z1 g2 z2 ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl
       bc sb0 sb1 sj nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      rv = STRING #"%" (toString (st.cs_next_var + 2)) /\
      g1 = STRING #"%" (toString (st.cs_next_var + 3)) /\
      z1 = STRING #"%" (toString (st.cs_next_var + 4)) /\
      g2 = STRING #"%" (toString (st.cs_next_var + 5)) /\
      z2 = STRING #"%" (toString (st.cs_next_var + 6)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 7)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 8)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc, st with cs_next_var := st.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (st.cs_next_id + 14) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 9 /\ cs_extends st sb0 /\
      st.cs_next_id <= sb0.cs_next_id /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks =
        SOME <|bb_label := st.cs_current_bb; bb_instructions :=
          st.cs_current_insts ++
          [mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv fty))] [p];
           mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []]|> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <|bb_label := entry_lbl; bb_instructions :=
          [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
           mk_inst (st.cs_next_id + 3) SUB [op2; op1] [rv];
           mk_inst (st.cs_next_id + 4)
             (if is_signed_type fty then SGT else GT) [op1; op2] [g1];
           mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
           mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
           mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
           mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
           mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
           mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
           mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []]|> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <|bb_label := cond_lbl; bb_instructions :=
          [mk_inst (st.cs_next_id + 12) EQ [Var cv; Var ev] [dv];
           mk_inst (st.cs_next_id + 13) JNZ
             [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
        get_instruction bbb 0 =
          SOME (mk_inst (st.cs_next_id + 14) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
        sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
        sj.cs_current_insts = sb1.cs_current_insts ++
          [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
        fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <|bb_label := incr_lbl; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
           mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
           mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []]|> /\
      sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\ cs_extends st sb /\
      not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
      sa.cs_next_var <= sb0.cs_next_var /\ sa.cs_next_id <= sb0.cs_next_id /\
      (!x. not_fresh_at sa x ==> not_fresh_at sb0 x))
Proof
  conj_tac
  >- (rpt gen_tac >> simp[range_full_outer_env] >> strip_tac >>
      drule_all compile_for_range_lit_parts >>
      disch_then (qx_choosel_then
        [`p`, `cv`, `ev`, `dv`, `entry_lbl`, `cond_lbl`, `body_lbl`, `incr_lbl`,
         `exit_lbl`, `bc`, `sb0`, `sb1`, `sj`, `nv`] strip_assume_tac) >>
      simp[] >>
      qexistsl_tac [`sb0`, `sb1`, `sj`] >>
      gvs[not_fresh_at_def]) >>
  rpt gen_tac >> simp[range_full_outer_env] >> strip_tac >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  `cs_extends sa st` by metis_tac[cs_extends_trans] >>
  drule_all (SRULE [] compile_stmt_for_range_checked) >> strip_tac >>
  `for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 st = ((), sb)` by
    metis_tac[] >>
  drule_all for_range_checked_parts >>
  disch_then (qx_choosel_then
    [`p`, `cv`, `rv`, `g1`, `z1`, `g2`, `z2`, `ev`, `dv`, `entry_lbl`,
     `cond_lbl`, `body_lbl`, `incr_lbl`, `exit_lbl`, `bc`, `sb0`, `sb1`, `sj`, `nv`]
    strip_assume_tac) >>
  simp[] >>
  qexistsl_tac [`sb0`, `sb1`, `sj`] >>
  gvs[not_fresh_at_def] >> decide_tac
QED

(* ===== Initialization: virtual allocation cut ===== *)

Theorem range_alloc_buffer_code:
  compile_alloc_buffer n st = (buf,cut) /\
  lookup_block st.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions :=
      st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString st.cs_next_var)]] ++ tail|> ==>
  fn_has_code st cut func
Proof
  strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]
QED
