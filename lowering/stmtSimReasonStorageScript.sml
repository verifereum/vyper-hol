(*
 * Statement simulation: Raise and Assert with a reason read from storage
 * or transient storage (#637)
 *
 * A reason that compile_expr hands out as a pointer into storage or
 * transient storage (a string state variable, or a string inside one)
 * reaches the Error(string) encoder of compile_revert_with_reason as a
 * LocatedValue, which the encoder's unwrap_value copies into a buffer of
 * its own (compile_ensure_in_memory: an SLOAD or TLOAD for one word, the
 * word copy loop otherwise) before the rest of the encoder runs.  As for
 * the reasons in stmtSimReasonExpr, the REVERT's data is not compared, so
 * only definedness matters: the copy reads and writes words and loops a
 * fixed number of times, whatever storage holds (exprSimStorageCopy).
 *
 * TOP-LEVEL:
 *   reason_storage_vv                   — the reason's value_vv: a pointer
 *                                         into storage or transient storage
 *   compile_raise_storage_reason_frag   — raise with such a reason
 *   compile_assert_storage_reason_frag  — assert with such a reason
 *
 * Helper: unwrap_storage_reason_defined_frag, unwrap_storage_reason_var,
 *   storage_reason_tail_known, compile_revert_storage_reason_frag,
 *   compile_revert_storage_reason_path
 *)

Theory stmtSimReasonStorage
Ancestors
  exprSimUnwrapProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  exprSimUnwrap exprSimHyps loweringSlice
  exprSimStorageCopy exprOperandVar stmtSimReasonStoragePath venomInstProps
  stmtSimReason stmtSimReasonExpr storageCopyGasPath
  gasOutcome gasSummary gasCount fragGasPath fragGasMode fragGasSeq
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv moduleLoweringProps
  vyperInterpreter vyperState vyperValue vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* The reason's value_vv is a pointer to a value of a type that is not a
   word type (a string) in storage or transient storage. *)
Definition reason_storage_vv_def:
  reason_storage_vv vv <=>
    ?t p. vv = LocatedValue t p /\ ~is_word_type t /\
          (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)
End


Theorem unwrap_storage_reason_defined_frag:
  !ctx cenv ty p sa op sb sbase a R.
    reason_storage_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt gen_tac >>
  simp[reason_storage_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def] >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:bool``] ensure_storage_memory_defined_frag) >>
  goal_assum (drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem unwrap_storage_reason_var:
  !cenv ty p sa op sb.
    reason_storage_vv (LocatedValue ty p) /\
    unwrap_value cenv (LocatedValue ty p) sa = (op,sb) ==>
    ?x. op = Var x
Proof
  rpt gen_tac >> simp[reason_storage_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, ensure_storage_memory_layout,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >> gvs[]
QED

Theorem storage_reason_tail_known:
  !hs sm t u x w.
    reason_known hs t /\ EVERY (not_fresh_at sm) hs /\
    (!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y t) /\
    eval_operand (Var x) u = SOME w ==>
    reason_known (x::hs) u
Proof
  simp[reason_known_def, EVERY_MEM, eval_operand_def] >> metis_tac[]
QED

Theorem compile_revert_storage_reason_frag:
  !ctx cenv ty p mt ms sa sb sbase a R.
    reason_storage_vv (LocatedValue ty p) /\
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
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists `sa` >> simp[]) >>
      `frag_exec ctx sm sn (\s. s = t)
        (\s. (?w. eval_operand op s = SOME w) /\
          (!x. not_fresh_at sm x ==> lookup_var x s = lookup_var x t) /\
          s.vs_labels = t.vs_labels) R` by
        (irule unwrap_storage_reason_defined_frag >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule frag_exec_then >> disch_then irule >> simp[] >>
      reverse conj_tac
      >- (irule unwrap_value_extends >> goal_assum (drule_at Any)) >>
      qx_gen_tac `u` >> strip_tac >>
      drule_all unwrap_storage_reason_var >> strip_tac >> gvs[] >>
      rename1 `eval_operand (Var x) u = SOME w` >>
      first_x_assum (qspec_then `x::hs` mp_tac) >>
      simp[reason_operand_def] >> strip_tac >>
      `reason_known (x::hs) u` by
        (irule storage_reason_tail_known >> simp[] >>
         qexistsl_tac [`sm`, `t`] >> simp[]) >>
      `frag_exec ctx sn sb (reason_known (x::hs)) (\s. F) R` by
        (irule reason_prefix_revert_frag >> simp[] >> metis_tac[]) >>
      drule frag_exec_weaken >> disch_then irule >> simp[]) >>
  irule cs_extends_trans >> qexists `sn` >> simp[] >>
  irule unwrap_value_extends >> goal_assum (drule_at Any)
QED

Theorem storage_reason_head_path[local]:
  same_blocks sa sm /\ sm.cs_current_insts = sa.cs_current_insts ++ h /\
  reason_prefix [] h hs /\
  EVERY (\i. EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) h /\
  fn_has_code sa sm func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (OK t) /\ reason_known hs t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  `reason_known [] s` by simp[reason_known_def] >>
  drule_all reason_prefix_sound >> strip_tac >>
  rename1 `run_inst_seq h s = OK r` >>
  drule reason_prefix_counted >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) h /\
   FILTER (\i. i.inst_opcode = GAS) h = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `r.vs_current_bb = s.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
                       run_inst_seq_preserves_field)) >>
     qexists_tac `h` >> simp[] >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  `gas_path ctx func s 0 (OK (r with vs_inst_idx := s.vs_inst_idx + LENGTH h))` by
    (qspec_then `h` mp_tac tuple_run_inst_seq_gas_path >>
     qpat_assum `FILTER _ h = []` (fn th => rewrite_tac[th, LENGTH]) >>
     disch_then irule >> simp[] >>
     gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND, DROP_APPEND]) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx + LENGTH h` >>
  simp[] >> conj_tac
  >- (gvs[reason_known_def, lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~MEM x (FLAT (MAP (\i. i.inst_outputs) h))` by
        (gvs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      gvs[lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (drule gas_path_normal >> simp[]) >> gvs[same_blocks_def]
QED

Theorem unwrap_storage_reason_defined_path[local]:
  reason_storage_vv (LocatedValue ty p) /\
  unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
  fn_has_code sa sb func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  eval_operand p.ptr_operand s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (OK t) /\
      (?w. eval_operand op t = SOME w) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_labels = s.vs_labels /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[reason_storage_vv_def] >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def] >> strip_tac >>
  irule ensure_storage_memory_defined_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem storage_reason_tail_path[local]:
  same_blocks sn sb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (k ++ [mk_inst id REVERT [off;len] []]) /\
  fn_has_code sn sb func /\ reason_prefix ds k es /\
  reason_operand es off /\ reason_operand es len /\ reason_known ds s /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  fs[fn_has_code_def] >> rename1 `lookup_block _ _ = SOME bb` >>
  irule reason_revert_path >> simp[] >>
  qexistsl_tac [`bb`, `ds`, `es`, `id`, `k`, `len`, `off`, `[]`, `s`] >>
  simp[run_inst_seq_def] >>
  gvs[same_blocks_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  `LENGTH sn.cs_current_insts - (LENGTH k + LENGTH sn.cs_current_insts) = 0 /\
   LENGTH sn.cs_current_insts - (LENGTH k + (LENGTH sn.cs_current_insts + 1)) = 0`
    by decide_tac >> simp[]
QED

(* The encoder with its copy out of storage or transient storage reads no
   gas: a counted path of zero GAS reads to its REVERT, from any state
   where the pointer's operand is defined.  Every instruction it emits is
   total, and the copy loop's counter reaches its bound (mod 2^256)
   whatever the buffer's address. *)
Theorem compile_revert_storage_reason_path:
  !ctx func cenv ty p mt ms sa sb s a.
    reason_storage_vv (LocatedValue ty p) /\
    compile_revert_with_reason cenv (LocatedValue ty p) mt ms sa = ((),sb) /\
    fn_has_code sa sb func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand p.ptr_operand s = SOME a /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path ctx func s 0 (Abort Revert_abort t)
Proof
  rpt strip_tac >> drule compile_revert_reason_split_certificate >> strip_tac >>
  `cs_extends sm sn` by
    (irule unwrap_value_extends >> goal_assum (drule_at Any)) >>
  `cs_extends sm sb` by
    (irule cs_extends_trans >> qexists_tac `sn` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all storage_reason_head_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `reason_known hs t` >>
  `eval_operand p.ptr_operand t = SOME a` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  drule_all unwrap_storage_reason_defined_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand op u = SOME w` >>
  drule_all unwrap_storage_reason_var >> strip_tac >> gvs[] >>
  rename1 `eval_operand (Var x) u = SOME w` >>
  first_x_assum (qspec_then `x::hs` mp_tac) >>
  simp[reason_operand_def] >> strip_tac >>
  `reason_known (x::hs) u` by
    (irule storage_reason_tail_known >> simp[] >>
     qexistsl_tac [`sm`, `t`] >> simp[]) >>
  drule_all (SRULE [APPEND_ASSOC] storage_reason_tail_path) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func u 0 (Abort Revert_abort v)` >>
  qexists_tac `v` >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
  qexists_tac `t` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
  qexists_tac `u` >> simp[]
QED

(* raise r, for a reason r that is not a string literal and whose value
   compile_expr hands out as a pointer into storage or transient storage:
   r's judgment, then the encoder, whose unwrap_value copies the value
   into memory, and its REVERT. *)

(* Why it holds.  On a value, vv_post's vv_holds gives the pointer's
   operand defined (eval_operand p.ptr_operand = SOME w).  The encoder's
   instructions before unwrap_value (an ALLOCA, an MSTORE, an ADD, an
   ALLOCA) run with defined operands; unwrap_value's
   compile_ensure_in_memory allocates a buffer and copies (SLOAD or TLOAD
   then MSTORE for one word; for more, compile_word_copy_loop, whose
   counter runs from 0 until it equals n2w word_count); the rest of the
   encoder runs to its REVERT as in compile_revert_reason_certificate.
   None of it reads gas, and no storage invariant is needed. *)
Theorem compile_raise_storage_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  rpt strip_tac >> irule compile_raise_reason_path_frag >> simp[] >>
  rpt strip_tac >>
  `reason_storage_vv vv` by metis_tac[] >>
  `?vt p. vv = LocatedValue vt p` by metis_tac[reason_storage_vv_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >>
     qspecl_then [`cenv`, `expr_type r`, `r`, `sa`, `vv`, `sm`] mp_tac
       (cj 1 compiler_compile_var) >>
     gvs[vv_operand_def]) >>
  gvs[vv_post_def, vv_holds_def] >>
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_storage_reason_path) >>
  qpat_x_assum `compile_revert_with_reason _ _ _ _ _ = _` (irule_at Any) >>
  simp[]
QED

(* assert e, r for a reason r as compile_raise_storage_reason_frag has it:
   its fail block is that raise, judged where the condition reads false. *)
Theorem compile_assert_storage_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
                (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
              expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_storage_vv vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  rpt strip_tac >> irule compile_assert_reason_frag_general >> simp[] >>
  rpt strip_tac >> irule compile_raise_storage_reason_frag >> simp[] >>
  metis_tac[]
QED
