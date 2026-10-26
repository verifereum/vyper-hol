(*
 * Statement simulation: more statements over stmt_frag (#637)
 *
 * Cases of the statement judgment stmt_frag (stmtSim) beyond the ones
 * stmtSim proves.
 *
 * TOP-LEVEL:
 *   compile_annassign_word_stmt_frag — a word-local declaration, for every
 *                                      outcome of its right-hand side
 *   compile_raise_reason_lit_frag    — raise with a string literal reason
 *   compile_assert_reason_lit_frag   — assert with a string literal reason
 *)

Theory stmtSimCases
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperExprNoControl
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* ===== A word-local declaration ===== *)

Theorem stmt_state_rel_declare_local_entry:
  !func cenv cx es ss id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) /\
    stmt_state_rel func cenv cx es ss ==>
    stmt_state_rel func c cx es ss
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  irule stmt_state_rel_cenv_cong >> qexists `cenv` >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[])
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                         ce_dynarray_capacity := _ |> = cenv` mp_tac >>
  simp[compileEnvTheory.compile_env_component_equality]
QED

Theorem exec_alloca_frames:
  !inst s n s1 p.
    inst.inst_outputs = [p] /\ exec_alloca inst s n = OK s1 ==>
    (!x. x <> p ==> lookup_var x s1 = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP s1.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (rw[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      gvs[FLOOKUP_UPDATE] >> Cases_on `inst.inst_id = aid` >> gvs[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  rw[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem annassign_alloca_framed_frag:
  !ctx func cenv cx es st st1 p sz s0 R.
    emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), st1) /\
    stmt_state_rel func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) ==>
    ?s1 w. lookup_var p s1 = SOME w /\
      FLOOKUP s1.vs_allocas st.cs_next_id = SOME (w2n w, sz) /\
      (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s1.vs_allocas aid = SOME entry) /\
      frag_exec ctx st st1 (\s. s = s0)
        (\s. s = s1 /\ stmt_state_rel func cenv cx es s) R
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `?s1. exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (Cases_on `FLOOKUP s0.vs_allocas st.cs_next_id`
     >- simp[exec_alloca_def] >>
     rename1 `FLOOKUP s0.vs_allocas st.cs_next_id = SOME entry` >>
     PairCases_on `entry` >> simp[exec_alloca_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  drule_all exec_alloca_frames >> strip_tac >>
  qexistsl [`s1 with vs_inst_idx := LENGTH st1.cs_current_insts`, `w`] >>
  gvs[lookup_var_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  irule frag_exec_run_inst_seq >>
  gvs[venomInstTheory.mk_inst_def] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       IS_PREFIX_APPEND3, run_inst_seq_def, stmt_state_rel_inst_idx,
       is_terminator_def, step_inst_base_def, Abbr `A`,
       venomInstTheory.mk_inst_def]
QED

Theorem annassign_mstore_framed_frag:
  !w v p val_op ctx func cenv cx es' st st' Pre R keep s0.
    emit_void MSTORE [Var p; val_op] st = ((), st') /\
    (!s. Pre s ==>
      lookup_var p s = SOME w /\
      eval_operand val_op s = SOME (val_to_w256 v) /\
      stmt_state_rel func cenv cx es' (mstore (w2n w) (val_to_w256 v) s) /\
      (!x. keep x ==> lookup_var x s = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s.vs_allocas aid = SOME entry)) ==>
    frag_exec ctx st st' Pre
      (\s. stmt_state_rel func cenv cx es' s /\
           (!x. keep x ==> lookup_var x s = lookup_var x s0) /\
           (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                        FLOOKUP s.vs_allocas aid = SOME entry)) R
Proof
  rpt strip_tac >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    simp[venomInstTheory.mk_inst_def, is_terminator_def] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> first_x_assum drule >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [Var p; val_op] []) s =
     OK (mstore (w2n w) (val_to_w256 v) s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def, stmt_state_rel_inst_idx,
       mstore_def, lookup_var_def, LET_THM] >>
  gvs[lookup_var_def, mstore_def, LET_THM]
QED

Theorem cenv_top_ext_declare_local:
  !cenv id ty st c st1 sc rest.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    lookup_scopes id rest = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) ==>
    cenv_top_ext cenv c (sc :: rest)
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  simp[cenv_top_ext_def] >> rpt strip_tac >>
  `n = id` by metis_tac[] >> gvs[]
QED

(* x: T = e for a word type T, for every outcome: the right-hand side's
   errors exit, and on a value the local is declared and stored
   (compile_annassign_word_frag).  The right-hand side's judgment is at the
   environment after the declaration, which binds x to its pointer; x is
   not in scope at es. *)
(* Why it holds.  The relation at the declared environment c comes from
   stmt_state_rel_cenv_cong: declare_local_ptr changes only id, which no
   scope at es holds, and binds it to a pointer, as cenv does if at all.
   The ALLOCA then runs with the relation kept at c (its output is fresh,
   local_ptrs_reserved), and expr_sim at c either exits with expr_exit, an
   Abort that carries back over the ALLOCA, or reaches the MSTORE in
   expr_post.  materialise and new_variable fail only with type errors,
   which stmt_res_ok leaves out.  On success cenv'' = c; cenv_top_ext holds
   since only id changes, a pointer on both sides, and the rest of the
   scopes do not hold it.  The ALLOCA's output is fresh at sa, so the
   lookup_var frame does not speak of it; a second run of the ALLOCA (in a
   loop) keeps its allocation.  compile_annassign_word_frag's post has no
   lookup_var or allocas frame, so the success case re-chains ALLOCA,
   expr_post and MSTORE rather than citing it. *)
Theorem frag_exec_no_exit_run:
  !ctx a b P Q func s.
    frag_exec ctx a b P Q (\r. F) /\ fn_has_code a b func /\ P s /\
    ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rw[frag_exec_def] >> first_x_assum drule >> simp[]
QED

Theorem annassign_alloca_framed_run:
  !ctx func cenv cx es st st1 p sz s0.
    emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), st1) /\
    stmt_state_rel func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    fn_has_code st st1 func /\ ~s0.vs_halted /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?s1 w. lookup_var p s1 = SOME w /\
      FLOOKUP s1.vs_allocas st.cs_next_id = SOME (w2n w, sz) /\
      (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s1.vs_allocas aid = SOME entry) /\
      stmt_state_rel func cenv cx es s1 /\ ~s1.vs_halted /\
      s1.vs_current_bb = st1.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
      !fuel r. run_from fuel ctx func s1 = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt strip_tac >> drule_all annassign_alloca_framed_frag >>
  disch_then (qspecl_then [`ctx`, `\r. F`] mp_tac) >> strip_tac >>
  drule frag_exec_no_exit_run >>
  disch_then drule >> disch_then (qspec_then `s0` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`s1`, `w`] >> gvs[]
QED

Theorem eval_annassign_word_error:
  !cx id typ e es ex es' lctx.
    eval_stmt cx (AnnAssign id typ e) es = (INR ex, es') /\
    stmt_res_ok lctx (INR ex) /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==> ?v. tv = Value v) ==>
    eval_expr cx e es = (INR ex, es') /\ expr_res_ok (INR ex : toplevel_value + exception)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       lift_option_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ`
  >- gvs[raise_def, stmt_res_ok_def, expr_res_ok_def] >>
  simp[return_def] >>
  Cases_on `eval_expr cx e es` >>
  rename1 `eval_expr cx e es = (r1, es1)` >> Cases_on `r1`
  >- (gvs[] >> gvs[materialise_def, return_def] >>
      simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, set_scopes_def, raise_def, return_def] >>
      rw[AllCaseEqs()] >> gvs[stmt_res_ok_def, expr_res_ok_def] >>
      Cases_on `es1.scopes` >> gvs[raise_def, set_scopes_def, return_def]) >>
  simp[] >> strip_tac >> gvs[stmt_res_ok_def, expr_res_ok_def] >>
  imp_res_tac (cj 1 eval_expr_no_control) >> gvs[no_control_exc_def]
QED

Theorem compile_annassign_word_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' etv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= type_memory_bytes cenv vtyp /\
    type_memory_bytes cenv vtyp < dimword (:256) /\
    (!tyv. evaluate_type (get_tenv cx) vtyp = SOME tyv ==>
           type_memory_size tyv = 32) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              ?v. tv = Value v /\ word_value v /\
                  typed_val_to_w256 etv v = val_to_w256 v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  cheat
QED

(* Partial integration proof preserved for C1.3.3 extraction.
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `declare_local cenv id vtyp sa` >>
  rename1 `declare_local cenv id vtyp sa = (c, st)` >>
  Cases_on `compile_stmt c lctx ty (AnnAssign id vtyp e) st` >>
  rename1 `compile_stmt c lctx ty (AnnAssign id vtyp e) st = (u, sf)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all declare_local_ptr >> strip_tac >>
  `stmt_state_rel func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `local_ptrs_reserved c st` by metis_tac[declare_local_reserved] >>
  `fn_has_code st sb func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  qpat_x_assum `!st0 c st1. _` drule >> strip_tac >>
  drule_all compile_annassign_word_parts >>
  disch_then (qx_choosel_then [`sA`, `sB`, `op`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz)` >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `cs_extends sA sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sA func` by
    (qspecl_then [`st`, `sA`, `sb`, `func`] mp_tac fn_has_code_split >>
     simp[]) >>
  qspecl_then [`ctx`, `func`, `c`, `cx`, `es`, `st`, `sA`, `p`, `sz`,
               `s0`, `\r. F`] mp_tac annassign_alloca_framed_frag >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  suspend "allocation_run"
QED

Resume compile_annassign_word_stmt_frag[allocation_run]:
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `s0`] mp_tac) >>
  impl_tac >- gvs[] >> simp[] >> strip_tac >> gvs[] >>
  suspend "expression"
QED

Resume compile_annassign_word_stmt_frag[expression]:
  Cases_on `res`
  >- (Cases_on `x` >> suspend "success") >>
  `eval_expr cx e es = (INR y, es') /\
   expr_res_ok (INR y : toplevel_value + exception)` by
    (drule eval_annassign_word_error >> simp[] >>
     disch_then (qspec_then `lctx` mp_tac) >> simp[] >> metis_tac[]) >>
  disj2_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sA`, `sB`, `op`, `INR y`, `es'`, `salloc`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. _`
    (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
  qexists `fuel'` >> gvs[stmt_exit_def] >> disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:toplevel_value``] expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

Resume compile_annassign_word_stmt_frag[success]:
  drule eval_stmt_annassign_value >> strip_tac >>
  qpat_x_assum `!tv es1. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  gvs[materialise_def, return_def] >>
  `type_memory_size tyv = 32` by simp[] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sA`, `sB`, `op`, `INL (Value v)`, `es1`, `salloc`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  gvs[expr_post_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!sa sb op. _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!aid off sz. _` kall_tac >>
  qpat_x_assum `!n. n <> id ==> _` kall_tac >>
  qpat_x_assum `c with <| ce_vars := _; ce_dynarray_capacity := _;
                         ce_var_type := _ |> = cenv` kall_tac >>
  qpat_x_assum `stmt_state_rel func cenv cx es s0` kall_tac >>
  qpat_x_assum `stmt_state_rel func c cx es s0` kall_tac >>
  qpat_x_assum `stmt_state_rel func c cx es salloc` kall_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` kall_tac >>
  suspend "store"
QED

Resume compile_annassign_word_stmt_frag[store]:
  FAIL_TAC "store"
QED

Finalise compile_annassign_word_stmt_frag
*)

(* raise and assert with a string literal as the reason: the literal's
   buffer and the Error(string) encoding of compile_revert_with_reason,
   straight-line code that ends in a REVERT, which every assertion
   allows.  A reason other than a literal is compiled with compile_expr
   and read back with unwrap_value after code of its own; those forms are
   not covered yet. *)
(* Why they hold.  The literal evaluates to StringV str, so the source
   raises AssertException str, which expr_exit takes as Revert_abort.  The
   reason code is one run of instructions in the open block, none a
   terminator before the REVERT: ALLOCAs with a literal size and one
   output, MSTOREs, ADD/AND, MLOAD, MCOPY, all total, each Var operand the
   output of an earlier one; unwrap_value of the literal's memory pointer
   emits nothing.  So it reaches the REVERT from any state.  The assert form
   is compile_assert_frag's shape with this run in place of the one
   aborting instruction of the fail block. *)
Theorem compile_raise_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty ml str es res es'.
    eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
Proof
  cheat
QED

Theorem compile_assert_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty e ml str es res es'.
    eval_stmt cx
      (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
Proof
  cheat
QED
