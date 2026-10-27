(*
 * Statement simulation: a word-local declaration (#637)
 *
 * AnnAssign over stmt_frag (stmtSim) for a local held in one word: the
 * right-hand side's errors exit; on a value the local's ALLOCA runs and the
 * right-hand side's typed word is stored, which lays the value out
 * (stmtSimDeclStore's store_lays_out): a word_value, or an address or bytesN
 * value of the declared type.
 *
 * TOP-LEVEL:
 *   compile_annassign_stmt_frag       — a one-word local's declaration, for
 *                                       every outcome of its right-hand
 *                                       side, storing the typed word of the
 *                                       right-hand side's value
 *   compile_annassign_word_stmt_frag  — the same for a word_value
 *   compile_annassign_typed_stmt_frag — the same for a value of the
 *                                       declared type: address and bytesN
 *)

Theory stmtSimDecl
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclStore
  loweringHalt
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperExprNoControl
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* ===== A word-local declaration ===== *)

Theorem stmt_state_rel_declare_local_entry[local]:
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

Theorem exec_alloca_frames[local]:
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

Theorem annassign_alloca_framed_frag[local]:
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

Theorem annassign_mstore_framed_frag[local]:
  !w wd p val_op ctx func cenv cx es' st st' Pre R keep s0.
    emit_void MSTORE [Var p; val_op] st = ((), st') /\
    (!s. Pre s ==>
      lookup_var p s = SOME w /\
      eval_operand val_op s = SOME wd /\
      stmt_state_rel func cenv cx es' (mstore (w2n w) wd s) /\
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
     OK (mstore (w2n w) wd s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def, stmt_state_rel_inst_idx,
       mstore_def, lookup_var_def, LET_THM] >>
  gvs[lookup_var_def, mstore_def, LET_THM]
QED

Theorem cenv_top_ext_declare_local[local]:
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

Theorem frag_exec_no_exit_run[local]:
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

Theorem annassign_alloca_framed_run[local]:
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

Theorem annassign_word_store_run[local]:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a op st st' wd.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME wd /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ type_memory_size tyv = 32 /\
    val_in_memory tyv v (w2n w) (mstore (w2n w) wd s).vs_memory /\
    val_wf tyv v ==>
    ?t. stmt_state_rel func cenv cx
          (es with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv; value := v|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel func cenv cx es'` >>
  `stmt_state_rel func cenv cx es' (mstore (w2n w) wd s)` by
    (simp[Abbr `es'`] >> irule stmt_state_rel_declare_store >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `frag_exec ctx st st' (\t. t = s)
     (\t. stmt_state_rel func cenv cx es' t /\
          (!x. lookup_var x t = lookup_var x s) /\
          (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                       FLOOKUP t.vs_allocas aid = SOME entry)) (\r. F)` by
    (irule (SRULE [] (Q.INST [`keep` |-> `\x. T`]
       (SPEC_ALL annassign_mstore_framed_frag))) >>
     simp[] >> metis_tac[]) >>
  drule frag_exec_no_exit_run >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem eval_annassign_word_error[local]:
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

Theorem annassign_word_store_post_run[local]:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v etv tyv sc rest a.
    expr_post func cenv cx e es sa sb s0 es1 v op s /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    store_lays_out etv tyv v /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz ==>
    ?t. stmt_state_rel func cenv cx
          (es1 with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv; value := v|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz)` by metis_tac[] >>
  `val_in_memory tyv v (w2n w)
     (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory /\
   val_wf tyv v /\ type_memory_size tyv = 32` by fs[store_lays_out_def] >>
  drule_all annassign_word_store_run >>
  disch_then (qspecl_then [`ctx`, `a`] mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem annassign_word_code_parts[local]:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ is_word_type vtyp /\ ~has_length_word vtyp /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
                cs_extends a b) ==>
    ?st sA sB op p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      lower_value compile_expr c (expr_type e) e sA = (op, sB) /\
      emit_void MSTORE [Var p; op] sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\
      not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `declare_local cenv id vtyp sa` >>
  rename1 `declare_local cenv id vtyp sa = (bc, st)` >>
  Cases_on `compile_stmt bc lctx ty (AnnAssign id vtyp e) st` >>
  rename1 `compile_stmt bc lctx ty (AnnAssign id vtyp e) st = (u, sb)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `declare_local cenv id vtyp sa = (c, st)` >>
  rename1 `fn_has_code sa sf func` >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved c st` by metis_tac[declare_local_reserved] >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `!a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
            cs_extends a b` by metis_tac[] >>
  drule_all compile_annassign_word_parts >>
  disch_then (qx_choosel_then [`sA`, `sB`, `op`] strip_assume_tac) >>
  `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code st sA func` by
    (qspecl_then [`st`, `sA`, `sf`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sA sf func` by
    (qspecl_then [`st`, `sA`, `sf`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sB sf func` by
    (qspecl_then [`sA`, `sB`, `sf`, `func`] mp_tac fn_has_code_split >> simp[]) >>
  qexistsl [`sA`, `sB`, `op`] >> gvs[]
QED

Theorem annassign_word_success_run[local]:
  !ctx func cenv cx id vtyp e es es' etv sa sb sf op p sz s0 w inst.
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!tyv tv es1. evaluate_type (get_tenv cx) vtyp = SOME tyv /\
                  eval_expr cx e es = (INL tv, es1) ==>
       ?v. tv = Value v /\ store_lays_out etv tyv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME w /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\ 32 <= sz ==>
    ?t. stmt_state_rel func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_annassign_value >> strip_tac >>
  qpat_x_assum `!tyv tv es1. _ /\ _ ==> _` drule_all >> strip_tac >>
  gvs[materialise_def, return_def] >>
  `not_local_ptr cenv es1.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL (Value v)`, `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  `lookup_scopes id es1.scopes = NONE` by gvs[] >>
  drule_all annassign_word_store_post_run >>
  disch_then (qspecl_then [`ctx`, `T`] mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem expr_sim_error_run[local]:
  !ctx func cenv cx ty e es ex es' sa sb op s0.
    expr_sim ctx func cenv cx ty e es /\
    eval_expr cx e es = (INR ex, es') /\
    expr_res_ok (INR ex : toplevel_value + exception) /\
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             expr_exit (INR ex : unit + exception) r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INR ex`, `es'`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:toplevel_value``] expr_exit_INR_type] >>
  metis_tac[]
QED

Theorem annassign_word_top_ext[local]:
  !cenv c cx id vtyp e es es' sa st.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==> ?v. tv = Value v) ==>
    cenv_top_ext cenv c es'.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmt_annassign_value >> strip_tac >>
  qpat_x_assum `!tv es1. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  gvs[materialise_def, return_def] >>
  irule cenv_top_ext_declare_local >> simp[] >>
  qexistsl [`id`, `sa`, `st`, `vtyp`] >> gvs[lookup_scopes_def, AllCaseEqs()]
QED

Theorem declare_local_old_fresh[local]:
  !cenv id ty sa c st p sz.
    declare_local cenv id ty sa = (c, st) /\ cenv.ce_alloca_locals /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    !x. not_fresh_at sa x ==> x <> p /\ not_fresh_at st x
Proof
  rpt gen_tac >> strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
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
Theorem compile_annassign_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' etv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= type_memory_bytes cenv vtyp /\
    type_memory_bytes cenv vtyp < dimword (:256) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==> ?v. tv = Value v) /\
    (!tyv tv es1. evaluate_type (get_tenv cx) vtyp = SOME tyv /\
                  eval_expr cx e es = (INL tv, es1) ==>
                  ?v. tv = Value v /\ store_lays_out etv tyv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
     !a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
              cs_extends a b` by metis_tac[] >>
  drule_all annassign_word_code_parts >>
  disch_then (qx_choosel_then [`st`, `sA`, `sB`, `op`, `p`] strip_assume_tac) >>
  rename1 `declare_local cenv id vtyp sa = (c, st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
  `stmt_state_rel func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `s0.vs_current_bb = st.cs_current_bb /\
   s0.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
  drule_all annassign_alloca_framed_run >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  Cases_on `res`
  >- (Cases_on `x` >>
      qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
      `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
       FLOOKUP salloc.vs_allocas ai.inst_id =
         SOME (w2n w, type_memory_bytes cenv vtyp)` by
        simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
      drule_all annassign_word_success_run >> strip_tac >>
      drule_all annassign_word_top_ext >> strip_tac >>
      `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
        (`sA.cs_next_var = st.cs_next_var` by
           (drule emit_inst_extends >> simp[]) >>
         drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
      disj1_tac >> qexistsl [`t`, `c`] >> simp[stmt_lands_def] >>
      conj_tac
      >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
          simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
               fresh_id_def, emit_def, comp_return_def] >>
          strip_tac >> Cases_on `sB.cs_current_insts` >>
          gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
              venomInstTheory.mk_inst_def, is_terminator_def]) >>
      rpt strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
        (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx func salloc = r /\ _ ==> _`
        drule >> simp[]) >>
  `eval_expr cx e es = (INR y, es') /\
   expr_res_ok (INR y : toplevel_value + exception)` by
    (drule eval_annassign_word_error >> simp[] >>
     disch_then (qspec_then `lctx` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
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
              ?v. tv = Value v /\ word_value v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  rpt strip_tac >> irule compile_annassign_stmt_frag >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac `etv` >> simp[]) >> rpt strip_tac >>
  qpat_x_assum `!tv es1. _ ==> ?v. tv = Value v /\ word_value v` drule >>
  strip_tac >> gvs[] >>
  irule store_lays_out_word_value >> metis_tac[]
QED

(* x: T = e for a word type T, address and bytesN included, where e has
   type T and its values are of T: the stored word is e's typed word,
   which lays the value out as val_in_memory does for T. *)
Theorem compile_annassign_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' tyv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= type_memory_bytes cenv vtyp /\
    type_memory_bytes cenv vtyp < dimword (:256) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    expr_type e = vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              ?v. tv = Value v /\ value_has_type tyv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  rpt strip_tac >> gvs[] >> irule compile_annassign_stmt_frag >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac `tyv` >> gvs[]) >> rpt strip_tac >>
  qpat_x_assum `!tv es1. _ ==> ?v. tv = Value v /\ value_has_type _ v` drule >>
  strip_tac >> gvs[] >>
  irule store_lays_out_typed >> metis_tac[]
QED
