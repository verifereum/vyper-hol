(*
 * Statement simulation: Raise and Assert with a reason read from an
 * immutable (#637)
 *
 * A reason that compile_expr hands out as a pointer into code (an
 * immutable string, reason_code_vv) reaches the Error(string) encoder of
 * compile_revert_with_reason as a LocatedValue, which the encoder's
 * unwrap_value copies into a buffer of its own (compile_ensure_in_memory:
 * an ALLOCA, then per word a DLOAD from the data section and an MSTORE,
 * compile_imm_copy_to_memory).  The function bodies are runtime code
 * (body_inv), so the copy reads with DLOAD, which is defined at every
 * offset.  As for stmtSimReasonStorage, the REVERT's data is not compared,
 * so only definedness matters.
 *
 * TOP-LEVEL:
 *   compile_raise_code_reason_frag   — raise with such a reason
 *   compile_assert_code_reason_frag  — assert with such a reason
 *
 * Helper: code_copy_frag,
 *   code_alloc_frag, unwrap_code_reason_defined_frag,
 *   unwrap_code_reason_var, code_reason_tail_known,
 *   compile_revert_code_reason_frag, reason_code_expr_revert_frag,
 *   reason_code_expr_revert_forced_frag
 *)

Theory stmtSimReasonCode
Ancestors
  list rich_list finite_map
  fragExec varsExt freshWrites exprSim exprSimUnwrap exprSimCopy exprSimStorageCopy
  exprOperandVar stmtSim stmtSimIf stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage exprReasonOperand immutableCopyExecution
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv moduleLoweringProps
  vyperInterpreter vyperState venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The copy out of code ===== *)

(* The copy runs and keeps every variable bound before it. *)
Theorem code_copy_frag[local]:
  !ctx imm src dst n sa sb sbase a b R.
    compile_imm_copy_to_memory F imm src dst n 0 sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. !x w. not_fresh_at sa x /\ lookup_var x sbase = SOME w ==>
                 lookup_var x s = SOME w) R
Proof
  rpt strip_tac >> drule code_copy_insts >> strip_tac >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[IS_PREFIX_APPEND3] >>
  irule frag_exec_run_inst_seq_drop_fresh >> fs[same_blocks_def] >>
  disj1_tac >>
  qspecl_then [`sa`, `sbase`] assume_tac fresh_vars_wrt_drop_fresh >>
  `eval_operand src (drop_fresh sa sbase) = SOME a /\
   eval_operand dst (drop_fresh sa sbase) = SOME b` by
    simp[eval_operand_drop_fresh] >>
  drule_all immutable_runtime_copy_execution >> strip_tac >>
  fs[immutable_execution_frame_def] >>
  qexists_tac `s'` >> conj_tac >- gvs[] >>
  qx_gen_tac `t` >> strip_tac >> qx_genl_tac [`x`, `w`] >> strip_tac >>
  `eval_operand (Var x) (drop_fresh sa sbase) = SOME w` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) s' = SOME w` by
    metis_tac[immutable_operand_frame_def] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Theorem code_alloc_frag[local]:
  !ctx n sa buf sb sbase R.
    compile_alloc_buffer n sa = (buf,sb) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand buf.buf_operand s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >>
  qspecl_then [`sa.cs_next_id`, `n2w n`,
               `STRING #"%" (toString sa.cs_next_var)`, `sbase`]
    strip_assume_tac loweringHaltTheory.step_alloca_frame >>
  rename1 `step_inst_base _ sbase = OK t` >>
  disj1_tac >> qexists_tac `t` >>
  gvs[run_inst_seq_def, GSYM mk_inst_def, control_moves_keep_vars,
      eval_operand_def] >> metis_tac[]
QED

(* unwrap_value of a pointer into code, at runtime: a buffer, then the
   copy.  The buffer's operand ends defined and every variable bound
   before keeps its value. *)
Theorem unwrap_code_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x w. not_fresh_at sa x /\ lookup_var x sbase = SOME w ==>
                  lookup_var x s = SOME w)) R
Proof
  rpt gen_tac >> simp[reason_code_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `cs_extends sa sm` by
    (gvs[cs_extends_def, same_blocks_def] >> qexists_tac `[]` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    simp[not_fresh_at_def] >>
  drule_then (qspecl_then [`ctx`, `sbase`, `R`] assume_tac) code_alloc_frag >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  reverse conj_tac
  >- (drule code_copy_insts >> strip_tac >>
      irule cs_extends_same_block >> fs[same_blocks_def] >>
      metis_tac[IS_PREFIX_APPEND3]) >>
  qx_gen_tac `t` >> strip_tac >>
  `eval_operand p.ptr_operand t = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  rename1 `eval_operand (Var bx) t = SOME bw` >>
  drule code_copy_frag >>
  disch_then (qspecl_then [`ctx`, `t`, `a`, `bw`, `R`] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >>
  strip_tac >> drule frag_exec_weaken >> disch_then irule >> simp[] >>
  rpt strip_tac
  >- (qexists_tac `bw` >> fs[eval_operand_def] >> first_x_assum irule >>
      fs[]) >>
  metis_tac[]
QED

Theorem unwrap_code_reason_var:
  !cenv ty p sa op sb.
    reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) ==>
    ?x. op = Var x
Proof
  rpt gen_tac >> simp[reason_code_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >> gvs[]
QED

(* ===== The encoder ===== *)

Theorem code_reason_tail_known[local]:
  !hs sm t u x w.
    reason_known hs t /\ EVERY (not_fresh_at sm) hs /\
    (!y v. not_fresh_at sm y /\ lookup_var y t = SOME v ==>
           lookup_var y u = SOME v) /\
    eval_operand (Var x) u = SOME w ==>
    reason_known (x::hs) u
Proof
  simp[reason_known_def, EVERY_MEM, eval_operand_def] >> metis_tac[]
QED

Theorem compile_revert_code_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = sbase) (\s. F) R
Proof
  rpt strip_tac >> drule compile_revert_reason_split_certificate >>
  strip_tac >>
  `frag_exec ctx sa sm (\s. s = sbase)
    (\s. reason_known hs s /\
      (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
      s.vs_labels = sbase.vs_labels) R` by
    (irule reason_head_frag >> simp[] >> metis_tac[]) >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  conj_tac
  >- (qx_gen_tac `t` >> strip_tac >>
      `eval_operand p.ptr_operand t = SOME a` by
        (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
      `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
        (rpt strip_tac >> irule not_fresh_at_mono >>
         qexists `sa` >> simp[]) >>
      `frag_exec ctx sm sn (\s. s = t)
        (\s. (?w. eval_operand op s = SOME w) /\
          (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
                 lookup_var x s = SOME w)) R` by
        (irule unwrap_code_reason_defined_frag >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule frag_exec_then >> disch_then irule >> simp[] >>
      reverse conj_tac
      >- (irule unwrap_value_extends >> goal_assum (drule_at Any)) >>
      qx_gen_tac `u` >> strip_tac >>
      drule_all unwrap_code_reason_var >> strip_tac >> gvs[] >>
      rename1 `eval_operand (Var x) u = SOME w` >>
      first_x_assum (qspec_then `x::hs` mp_tac) >>
      simp[reason_operand_def] >> strip_tac >>
      `reason_known (x::hs) u` by
        (irule code_reason_tail_known >> simp[] >>
         qexistsl_tac [`sm`, `t`] >> simp[]) >>
      `frag_exec ctx sn sb (reason_known (x::hs)) (\s. F) R` by
        (irule reason_prefix_revert_frag >> simp[] >> metis_tac[]) >>
      drule frag_exec_weaken >> disch_then irule >> simp[]) >>
  irule cs_extends_trans >> qexists `sn` >> simp[] >>
  irule unwrap_value_extends >> goal_assum (drule_at Any)
QED

(* Only a value reaches the reason encoder; the expression's own Halt
   remains an expression exit. *)
Theorem reason_code_expr_revert_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    ~cenv.ce_is_ctor /\
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    eval_expr cx r es = (res1, es1) /\ expr_vv_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\
    (!tv t. res1 = INL tv ==> R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sm sb` by
    (drule compile_revert_reason_split_certificate >> strip_tac >>
     drule unwrap_value_extends >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  `!t p. vv = LocatedValue t p ==>
     !x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >>
     qspecl_then [`cenv`, `expr_type r`, `r`, `sa`, `vv`, `sm`] mp_tac
       (cj 1 compiler_compile_var) >>
     gvs[vv_operand_def]) >>
  `?t p. vv = LocatedValue t p` by metis_tac[reason_code_vv_def] >>
  gvs[] >>
  reverse (Cases_on `res1`)
  >- (rename1 `INR ex` >>
      drule compile_expr_extends >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `LocatedValue t p`,
                              `INR ex`, `es1`, `s0`] mp_tac) >>
      simp[] >> strip_tac >>
      irule frag_exec_exit_prefix >> qexists `sm` >> simp[] >>
      irule frag_exec_conseq >>
      qpat_x_assum `frag_exec ctx sa sm _ _ _` (irule_at Any) >>
      simp[]) >>
  irule reason_expr_revert_frag_general >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  qexists_tac `\s. ?w. eval_operand p.ptr_operand s = SOME w` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[vv_holds_def]) >>
  irule frag_exec_pointwise >> simp[] >>
  rpt strip_tac >> irule compile_revert_code_reason_frag >>
  simp[] >> metis_tac[]
QED

Theorem reason_code_expr_revert_forced_frag[local]:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    ~cenv.ce_is_ctor /\
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_code_vv vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (do raw <- eval_expr cx r; read_result cx raw od) es = (res1, es1) /\
    expr_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\
    (!tv t. res1 = INL tv ==> R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) R
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx r es` >> rename1 `_ = (raw, est)` >>
  `est = es1` by
    (qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[read_result_state]) >> gvs[] >>
  `expr_vv_res_ok raw` by
    (qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `raw` >> simp[] >> strip_tac >>
     gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
     rename1 `read_result cx captured es1` >> Cases_on `captured` >>
     gvs[expr_vv_res_ok_def, read_result_def, raise_def, expr_res_ok_def]) >>
  `!rr. expr_exit raw rr ==> R rr` by
    (rpt strip_tac >> Cases_on `raw` >> gvs[] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> strip_tac >> gvs[] >>
     metis_tac[expr_exit_exception_transport]) >>
  reverse (Cases_on `?v. res1 = INL v`)
  >- (`cs_extends sm sb` by
        (drule compile_revert_reason_split_certificate >> strip_tac >>
         drule unwrap_value_extends >> strip_tac >>
         metis_tac[cs_extends_trans]) >>
      drule compile_expr_extends >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `vv`, `raw`, `es1`, `s0`] mp_tac) >>
      simp[] >> strip_tac >>
      `!tv s. raw = INL tv /\
         vv_post ctx func cenv cx r es sa sm s0 es1 tv vv s ==> F` by
        (rpt strip_tac >> gvs[vv_post_def] >>
         Cases_on `vv` >> gvs[reason_code_vv_def, vv_holds_def,
                              immutable_holds_def] >>
         qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
         simp[bind_def] >> metis_tac[]) >>
      irule frag_exec_exit_prefix >> qexists `sm` >> simp[] >>
      irule frag_exec_conseq >>
      qpat_x_assum `frag_exec ctx sa sm _ _ _` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  irule reason_code_expr_revert_frag >> simp[] >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
  metis_tac[]
QED

(* ===== The statements ===== *)

(* raise r, at runtime, for a reason r that is not a string literal and
   whose value compile_expr hands out as a pointer into code: r's
   fragment, whose errors exit, then the Error(string) encoder, whose
   unwrap_value copies the value into memory, and its REVERT. *)
Theorem compile_raise_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    ~cenv.ce_is_ctor /\
    eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    metis_tac[compile_reason_message_expr] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qpat_assum `compile_reason_message _ _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `compile_expr cenv (expr_type r) r sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
              (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `_ = (u, sf)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sfin func` >>
  drule_all eval_raise_reason_cases >>
  disch_then (qx_choose_then `r1` assume_tac) >>
  qspecl_then [`r1`, `res`, `RetQ`, `es'`] mp_tac raise_reason_exits >>
  impl_tac >- fs[] >> strip_tac >>
  `frag_exec ctx sa sfin (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. F) (stmt_exit RetQ es' res)` by
    (irule (INST_TYPE [alpha |-> ``:type``]
              reason_code_expr_revert_forced_frag) >> simp[] >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     qexistsl_tac [`es'`, `type_memory_bytes cenv (expr_type r)`, `r1`,
                   `expr_type r`] >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `s0`] mp_tac) >> simp[]
QED

(* assert e, r for a reason r as compile_raise_code_reason_frag has it:
   the condition and a JNZ to the ok block, where the code ends, and a fail
   block with r's fragment, the encoder and its REVERT.  r's judgment is
   at the source state after a false condition. *)
Theorem compile_assert_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    ~cenv.ce_is_ctor /\
    eval_stmt cx (Assert e (AssertReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r))) es res es'
Proof
  rpt strip_tac >> irule compile_assert_reason_frag_general >> simp[] >>
  rpt strip_tac >>
  `eval_stmt cx (Raise (RaiseReason r)) es1 = (res, es')` by
    metis_tac[eval_assert_reason_false] >>
  drule_all eval_raise_reason_cases >>
  disch_then (qx_choose_then `rr` assume_tac) >>
  qspecl_then [`rr`, `res`, `RetQ`, `es'`] mp_tac raise_reason_exits >>
  impl_tac >- fs[] >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:type``]
           reason_code_expr_revert_forced_frag) >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
  qexistsl_tac [`type_memory_bytes cenv (expr_type r)`, `expr_type r`] >>
  simp[] >> first_x_assum irule >> goal_assum (drule_at Any)
QED
