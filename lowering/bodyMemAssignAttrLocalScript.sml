(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a local struct (S1's body_assign_attr_local). *)
Theory bodyMemAssignAttrLocal
Ancestors
  bodyMemoryPreds bodyFieldMemoryProps bodyDeclMemoryCounted
  exprSimVVFrame exprOperandVar emitHelperProps gasSummary fragGasMode
  venomState venomInst venomExecSemantics compileEnv emitHelper fragExec
  words ASCIInumbers exprLoweringProps stmtSimAssignAttr
  gasExemptCert stmtSimForced vyperInterpreter vyperState vyperExprNoControl
  stmtSimDefs exprSimDefs gasOutcome loweringPosts gasContext exprSimMemorySource

Theorem assign_attr_local_add_exact_mem[local]:
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  lookup_var p s = SOME w /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s with vs_inst_idx := LENGTH sn.cs_current_insts))
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s)` by
    (irule buffer_emit_add_run >> qexistsl_tac [`dst`, `Var p`] >>
     simp[eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    metis_tac[attr_add_prefix_mem_ok] >>
  `same_blocks sm sn /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
         fresh_var_def, emit_def, same_blocks_def, mk_inst_def,
         is_terminator_def]) >>
  drule_all body_decl_cursor_path >>
  simp[gas_marked_path_def]
QED

Theorem assign_attr_local_add_post_mem[local]:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  lookup_var p s = SOME w /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  alloca_history func s ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    alloca_history func q /\ ~q.vs_halted /\
    q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_memory = s.vs_memory /\
    local_ptrs_reserved cenv sn /\
    sm.cs_next_var <= sn.cs_next_var /\
    (?out. dst = Var out /\ not_fresh_at sn out) /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  drule_all assign_attr_local_add_exact_mem >> strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `alloca_inv s` by gvs[loweringPostsTheory.vv_post_def,
                       stmt_state_rel_def] >>
  `run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s)` by
    (irule buffer_emit_add_run >> qexistsl_tac [`dst`, `Var p`] >>
     simp[eval_operand_def]) >>
  drule_all attr_add_history >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[] >> conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, update_var_def,
      eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[not_fresh_at_def] >>
  irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Theorem assign_attr_local_admissible_run_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  !gs. eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      (es with gas_obs := gs) =
    vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld]))
      (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  Cases_on `eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs)` >>
  rename1 `_ = (res, ee)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  drule eval_assign_attr_local >>
  impl_tac >- gvs[stmt_res_ok_def] >>
  strip_tac >> Cases_on `r` >>
  gvs[vyperStateTheory.bind_def, pairTheory.UNCURRY]
QED

Theorem assign_attr_local_admissible_rhs_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >> gvs[]
     >- metis_tac[read_result_no_control]
     >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ee`, `gs`] >>
     drule assign_attr_local_admissible_run_mem_src >>
     disch_then (qspec_then `gs` SUBST1_TAC) >>
     simp[Once vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assign_attr_local_admissible_raw_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >> irule forced_expr_admissible_raw >>
  metis_tac[assign_attr_local_admissible_rhs_mem_src]
QED

Theorem assign_attr_local_marked_exec_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec memory (ctx,func)
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (es,s0) marks res ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (es,s0) marks res ee r
Proof
  strip_tac >> drule assign_attr_local_admissible_run_mem_src >>
  strip_tac >> gvs[gas_marked_exec_def]
QED

Theorem assign_attr_local_continuation_success_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v, ee) ==>
  ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    write_place cx (MemoryPlace id [AttrSubscript fld]) v ee =
      (INL (), ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs)` >> rename1 `_ = (res, ff)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  drule eval_assign_attr_local >>
  impl_tac >- gvs[stmt_res_ok_def] >> strip_tac >>
  gvs[vyperStateTheory.bind_def, pairTheory.UNCURRY] >>
  `!m. res <> INR (Error (TypeError m))` by gvs[stmt_res_ok_def] >>
  drule_all write_place_attr_local >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem assign_attr_local_continuation_all_tails_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := prefix ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    !tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  `!tail. ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    write_place cx (MemoryPlace id [AttrSubscript fld]) v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
        with gas_obs := tail)` by
    (gen_tac >> drule assign_attr_local_continuation_success_mem_src >>
     disch_then (qspecl_then [`v`, `prefix ++ tail`, `ee with gas_obs := tail`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  pop_assum (fn th => assume_tac th >> mp_tac (Q.SPEC `[]` th)) >>
  strip_tac >> qexistsl_tac [`pre`, `env`, `entry`, `rest`, `vals`, `old`] >>
  gvs[] >> gen_tac >>
  first_x_assum (qspec_then `tail` strip_assume_tac) >> gvs[]
QED

Theorem assign_attr_local_exempt_mem_src[local]:
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_expr cx e) (return ()))
    (es, s0) marks (err, ee) (leaf, fin) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (return ()))
    (es, s0) marks (err, ee) (leaf, fin)
Proof
  strip_tac >>
  `ignore_bind
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (return ()) =
   vyperState$bind (eval_expr cx e)
     (\pv. ignore_bind
       (vyperState$bind (eval_target_place cx (AttributeTarget (NameTarget id) fld))
         (\p. vyperState$bind (read_result cx pv) (write_place cx p)))
       (return ()))` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem body_assign_attr_local_mem:
  !cx id fld e sid fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  cheat
QED
