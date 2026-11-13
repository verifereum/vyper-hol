(*
 * Statement simulation: Raise and Assert with a reason read from an
 * immutable (#637)
 *
 * A reason that compile_expr hands out as a pointer into code (an
 * immutable string, reason_code_vv) reaches the Error(string) encoder of
 * compile_revert_with_reason as a LocatedValue, which the encoder's
 * unwrap_value copies into a buffer of its own (compile_ensure_in_memory:
 * an ALLOCA, then per word a load and an MSTORE,
 * compile_imm_copy_to_memory).  Runtime code loads with DLOAD from the
 * data section; the constructor with ILOAD from the immutables' region,
 * whose base stmt_state_rel holds at 0 (immutable_base_zero).  Either load
 * is defined at every offset and reads no gas.  As for
 * stmtSimReasonStorage, the REVERT's data is not compared, so only
 * definedness matters.
 *
 * TOP-LEVEL:
 *   compile_raise_code_reason_shared_frag   — raise with such a reason
 *   compile_assert_code_reason_shared_frag  — assert with such a reason
 *   compile_raise_code_reason_frag, compile_assert_code_reason_frag
 *     — their runtime specialisations
 *
 * Helper: code_copy_frag,
 *   code_alloc_frag, unwrap_code_reason_defined_frag,
 *   unwrap_ctor_code_reason_defined_frag, unwrap_code_reason_var,
 *   code_reason_tail_known, compile_revert_code_reason_frag,
 *   compile_revert_ctor_code_reason_frag, compile_revert_code_reason_path
 *)

Theory stmtSimReasonCode
Ancestors
  exprSimUnwrapProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map
  fragExec varsExt freshWrites  exprSimUnwrap exprSimCopy exprSimStorageCopy
  exprOperandVar  stmtSimReason stmtSimReasonExpr
  gasOutcome gasSummary gasCount fragGasPath fragGasMode fragGasSeq
  stmtSimReasonStorage exprReasonOperand immutableCopyExecution
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv loweringStateRelDefs moduleLoweringProps
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

(* Constructor copy uses the reserved immutable base supplied by the frame. *)
Theorem unwrap_ctor_code_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    cenv.ce_is_ctor /\ immutable_base_zero cenv sbase /\
    (!base x. cenv.ce_imm_alloca = SOME base /\ base = Var x ==>
       not_fresh_at sa x) /\
    reason_code_vv (LocatedValue ty p) /\
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
  >- (drule code_ctor_copy_insts >> strip_tac >>
      irule cs_extends_same_block >> fs[same_blocks_def] >>
      metis_tac[IS_PREFIX_APPEND3]) >>
  qx_gen_tac `t` >> strip_tac >>
  `eval_operand p.ptr_operand t = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `sbase` >>
     simp[] >> metis_tac[]) >>
  rename1 `eval_operand (Var bx) t = SOME bw` >>
  drule copy_ctor_frag >>
  disch_then (qspecl_then [`ctx`, `t`, `a`, `bw`, `R`] mp_tac) >>
  impl_tac
  >- (fs[copy_old_operand_def, immutable_base_zero_def] >> metis_tac[]) >>
  strip_tac >> drule frag_exec_weaken >> disch_then irule >> simp[] >>
  rpt strip_tac
  >- (qexists_tac `bw` >> fs[eval_operand_def] >> first_x_assum irule >> fs[]) >>
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

Theorem compile_revert_ctor_code_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    cenv.ce_is_ctor /\ immutable_base_zero cenv sbase /\
    (!base x. cenv.ce_imm_alloca = SOME base /\ base = Var x ==>
       not_fresh_at sa x) /\
    reason_code_vv (LocatedValue ty p) /\
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
      `immutable_base_zero cenv t` by
        (irule immutable_base_zero_frame >> qexists_tac `sbase` >>
         simp[] >> metis_tac[]) >>
      `!base x. cenv.ce_imm_alloca = SOME base /\ base = Var x ==>
         not_fresh_at sm x` by
        (rpt strip_tac >> irule not_fresh_at_mono >>
         qexists `sa` >> simp[] >> metis_tac[]) >>
      `frag_exec ctx sm sn (\s. s = t)
        (\s. (?w. eval_operand op s = SOME w) /\
          (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
                 lookup_var x s = SOME w)) R` by
        (irule unwrap_ctor_code_reason_defined_frag >>
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

(* ===== Counted paths ===== *)

Theorem code_copy_run[local]:
  !imm src dst n sa sb s a b.
    compile_imm_copy_to_memory F imm src dst n 0 sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
               lookup_var x t = SOME w)
Proof
  rpt strip_tac >> drule code_copy_insts >> strip_tac >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
              ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  qspecl_then [`sa`, `s`] assume_tac fresh_vars_wrt_drop_fresh >>
  `eval_operand src (drop_fresh sa s) = SOME a /\
   eval_operand dst (drop_fresh sa s) = SOME b` by
    simp[eval_operand_drop_fresh] >>
  drule_all immutable_runtime_copy_execution >> strip_tac >>
  fs[immutable_execution_frame_def] >>
  rename1 `run_inst_seq _ (drop_fresh sa s) = OK clean` >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
                   (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME w` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) clean = SOME w` by
    metis_tac[immutable_operand_frame_def] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Theorem code_alloc_run[local]:
  !n sa buf sb s.
    compile_alloc_buffer n sa = (buf,sb) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        (?w. eval_operand buf.buf_operand t = SOME w) /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  qspecl_then [`sa.cs_next_id`, `n2w n`,
               `STRING #"%" (toString sa.cs_next_var)`, `s`]
    strip_assume_tac loweringHaltTheory.step_alloca_frame >>
  rename1 `step_inst_base _ s = OK t` >>
  qexists_tac `t` >> simp[run_inst_seq_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem unwrap_runtime_code_reason_run[local]:
  !cenv ty p sa op sb s a.
    ~cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand s = SOME a ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        (?w. eval_operand op t = SOME w) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
               lookup_var x t = SOME w)
Proof
  rpt gen_tac >> simp[reason_code_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ _ = ((),sb)` >>
  drule storage_copy_alloc_layout >> strip_tac >>
  drule code_copy_insts >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    metis_tac[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    simp[not_fresh_at_def] >>
  `emitted_insts sm sb = is` by
    (pure_rewrite_tac [emitted_insts_def] >>
     qpat_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[DROP_LENGTH_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac
  >- (simp[EVERY_APPEND, mk_inst_def, is_terminator_def] >>
      fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
      gvs[is_terminator_def]) >>
  drule_then (qspec_then `s` strip_assume_tac) code_alloc_run >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `eval_operand p.ptr_operand t = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  drule code_copy_run >>
  disch_then (qspecl_then [`t`, `a`, `w`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  qexists_tac `u` >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  conj_tac
  >- (qexists_tac `w` >>
      gvs[eval_operand_def] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* unwrap_value of a pointer into code, in the constructor: a buffer, then
   the copy with ILOAD from the immutables' region, whose base the frame
   holds at 0. *)
Theorem unwrap_ctor_code_reason_run[local]:
  !cenv ty p sa op sb s a.
    cenv.ce_is_ctor /\ reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand s = SOME a /\
    immutable_base_zero cenv s /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        (?w. eval_operand op t = SOME w) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
               lookup_var x t = SOME w)
Proof
  rpt gen_tac >> simp[reason_code_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ _ = ((),sb)` >>
  drule storage_copy_alloc_layout >> strip_tac >>
  drule code_ctor_copy_insts >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    metis_tac[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    simp[not_fresh_at_def] >>
  `emitted_insts sm sb = is` by
    (pure_rewrite_tac [emitted_insts_def] >>
     qpat_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[DROP_LENGTH_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac
  >- (simp[EVERY_APPEND, mk_inst_def, is_terminator_def] >>
      fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
      gvs[is_terminator_def]) >>
  drule_then (qspec_then `s` strip_assume_tac) code_alloc_run >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `eval_operand p.ptr_operand t = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     simp[] >> metis_tac[]) >>
  drule copy_ctor_run >>
  disch_then (qspecl_then [`t`, `a`, `w`] mp_tac) >>
  impl_tac
  >- (fs[copy_old_operand_def, immutable_base_zero_def] >> metis_tac[]) >>
  strip_tac >> fs[copy_runtime_frame_def] >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  qexists_tac `u` >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  conj_tac
  >- (qexists_tac `w` >> gvs[eval_operand_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* The copy out of code, at runtime (DLOAD) or in the constructor (ILOAD). *)
Theorem unwrap_code_reason_run[local]:
  !cenv ty p sa op sb s a.
    reason_code_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand s = SOME a /\
    (cenv.ce_is_ctor ==>
       immutable_base_zero cenv s /\
       !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        (?w. eval_operand op t = SOME w) /\
        (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
               lookup_var x t = SOME w)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `cenv.ce_is_ctor`
  >- (qspecl_then [`cenv`, `ty`, `p`, `sa`, `op`, `sb`, `s`, `a`] mp_tac
        unwrap_ctor_code_reason_run >> simp[]) >>
  qspecl_then [`cenv`, `ty`, `p`, `sa`, `op`, `sb`, `s`, `a`] mp_tac
    unwrap_runtime_code_reason_run >> simp[]
QED

Theorem code_reason_head_run[local]:
  !h hs sa s.
    reason_prefix [] h hs /\
    EVERY (\i. EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) h ==>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) h /\
    ?t. run_inst_seq h s = OK t /\ reason_known hs t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >- (drule reason_prefix_counted >> simp[]) >>
  `reason_known [] s` by simp[reason_known_def] >>
  drule_all reason_prefix_sound >> strip_tac >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> fs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem code_reason_path_certificate[local]:
  !func cenv ty p mt ms sa sb s a.
    reason_code_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    fn_has_code sa sb func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand s = SOME a /\
    (cenv.ce_is_ctor ==>
       immutable_base_zero cenv s /\
       !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?pre ds es is id off len t bb.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (pre ++ is ++ [mk_inst id REVERT [off;len] []])
        (DROP s.vs_inst_idx bb.bb_instructions) /\
      EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                  ~is_terminator i.inst_opcode) pre /\
      run_inst_seq pre s = OK t /\ reason_known ds t /\
      reason_prefix ds is es /\ reason_operand es off /\ reason_operand es len
Proof
  rpt strip_tac >> drule compile_revert_reason_split_certificate >> strip_tac >>
  drule_all code_reason_head_run >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `eval_operand p.ptr_operand t = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `cenv.ce_is_ctor ==>
     immutable_base_zero cenv t /\
     !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    (strip_tac >> fs[] >> conj_tac
     >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
         simp[] >> metis_tac[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >>
     simp[] >> metis_tac[]) >>
  drule_all unwrap_code_reason_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sn) t = OK u` >>
  drule_all unwrap_code_reason_var >> strip_tac >> gvs[] >>
  rename1 `eval_operand (Var x) u = SOME w` >>
  `reason_known (x::hs) u` by
    (irule code_reason_tail_known >> simp[] >>
     qexistsl_tac [`sm`, `t`] >> simp[]) >>
  qpat_x_assum `!ds. _` (qspec_then `x::hs` mp_tac) >>
  simp[reason_operand_def] >> strip_tac >>
  `run_inst_seq (h ++ emitted_insts sm sn) s = OK u` by
    (qpat_assum `run_inst_seq h s = OK t`
      (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  qexistsl_tac [`h ++ emitted_insts sm sn`, `x::hs`, `es`, `k`, `id`,
                `off`, `len`, `u`] >> simp[EVERY_APPEND] >>
  gvs[fn_has_code_def, same_blocks_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[IS_PREFIX_APPEND] >> metis_tac[]
QED

(* The encoder with its copy out of code reads no gas: a counted path of
   zero GAS reads to its REVERT, from any state where the pointer's
   operand is defined and, in the constructor, the immutables' base is 0. *)
Theorem compile_revert_code_reason_path:
  !ctx func cenv ty p mt ms sa sb s a.
    reason_code_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    fn_has_code sa sb func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand s = SOME a /\
    (cenv.ce_is_ctor ==>
       immutable_base_zero cenv s /\
       !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path ctx func s 0 (Abort Revert_abort t)
Proof
  rpt strip_tac >> drule_all code_reason_path_certificate >> strip_tac >>
  drule_all reason_revert_path >> simp[]
QED

(* ===== The statements ===== *)

(* raise r for a reason r that is not a string literal and whose value
   compile_expr hands out as a pointer into code: r's judgment, then the
   Error(string) encoder, whose unwrap_value copies the value into memory,
   and its REVERT.  At runtime the copy reads with DLOAD; in the
   constructor with ILOAD, from the immutables' region, whose base
   stmt_state_rel holds at 0. *)
Theorem compile_raise_code_reason_shared_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  rpt strip_tac >> irule compile_raise_reason_path_frag >> simp[] >>
  rpt strip_tac >>
  `reason_code_vv vv` by metis_tac[] >>
  `?vt p. vv = LocatedValue vt p` by metis_tac[reason_code_vv_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >>
     qspecl_then [`cenv`, `expr_type r`, `r`, `sa`, `vv`, `sm`] mp_tac
       (cj 1 compiler_compile_var) >>
     gvs[vv_operand_def]) >>
  `cenv.ce_is_ctor ==>
     immutable_base_zero cenv t /\
     !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    (strip_tac >> conj_tac >- fs[vv_post_def, stmt_state_rel_def] >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     metis_tac[local_ptrs_reserved_imm_base, cj 1 compile_expr_grows]) >>
  gvs[vv_post_def, vv_holds_def] >>
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_code_reason_path) >>
  qpat_x_assum `compile_revert_with_reason _ _ _ _ _ = _` (irule_at Any) >>
  simp[]
QED

Theorem compile_raise_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    ~cenv.ce_is_ctor /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  rpt strip_tac >> irule compile_raise_code_reason_shared_frag >> simp[] >> metis_tac[]
QED

(* assert e, r for a reason r as compile_raise_code_reason_shared_frag has
   it: its fail block is that raise, judged where the condition reads false
   under any gas readings. *)
Theorem compile_assert_code_reason_shared_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
                (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
              expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  rpt strip_tac >> irule compile_assert_reason_frag_general >> simp[] >>
  rpt strip_tac >> irule compile_raise_code_reason_shared_frag >> simp[] >>
  metis_tac[]
QED

Theorem compile_assert_code_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    ~cenv.ce_is_ctor /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
                (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
              expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_code_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  rpt strip_tac >> irule compile_assert_code_reason_shared_frag >> simp[] >> metis_tac[]
QED
