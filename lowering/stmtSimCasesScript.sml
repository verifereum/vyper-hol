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
  fragExec localPtrsProps exprSim loweringSlice stmtSim loweringHalt
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

Theorem annassign_word_store_run:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a op st st'.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME (val_to_w256 v) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ word_value v /\ type_memory_size tyv = 32 ==>
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
  `stmt_state_rel func cenv cx es' (mstore (w2n w) (val_to_w256 v) s)` by
    (simp[Abbr `es'`] >> irule stmt_state_rel_declare_word >> simp[] >>
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

Theorem annassign_word_store_post_run:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v etv tyv sc rest a.
    expr_post func cenv cx e es sa sb s0 es1 v op s /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    typed_val_to_w256 etv v = val_to_w256 v /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ word_value v /\ type_memory_size tyv = 32 ==>
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
  `eval_operand op s = SOME (val_to_w256 v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz)` by metis_tac[] >>
  drule_all annassign_word_store_run >>
  disch_then (qspecl_then [`ctx`, `a`] mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem annassign_word_code_parts:
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

Theorem annassign_word_success_run:
  !ctx func cenv cx id vtyp e es es' etv sa sb sf op p sz s0 w inst.
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    (!tyv. evaluate_type (get_tenv cx) vtyp = SOME tyv ==> type_memory_size tyv = 32) /\
    is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
       ?v. tv = Value v /\ word_value v /\ typed_val_to_w256 etv v = val_to_w256 v) /\
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
  qpat_x_assum `!tv es1. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  gvs[materialise_def, return_def] >>
  `type_memory_size tyv = 32` by simp[] >>
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

Theorem expr_sim_error_run:
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

Theorem annassign_word_top_ext:
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

Theorem declare_local_old_fresh:
  !cenv id ty sa c st p sz.
    declare_local cenv id ty sa = (c, st) /\ cenv.ce_alloca_locals /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    !x. not_fresh_at sa x ==> x <> p /\ not_fresh_at st x
Proof
  rpt gen_tac >> strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
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
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
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
      `!tv es1. eval_expr cx e es = (INL tv, es1) ==> ?v. tv = Value v` by
        (rpt strip_tac >> first_x_assum drule >> metis_tac[]) >>
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

(* Memory execution needs defined operands, not a memory-safety invariant.
   ALLOCA (including repeat executions and zero sizes) is total by
   loweringHaltTheory.step_alloca_frame. ADD, AND, MLOAD and MSTORE use
   step_ADD, step_AND, step_MLOAD and step_MSTORE; update_var's lookup
   equations give output definedness and the frame for the read steps.
   REVERT with defined operands is step_revert_behavior. *)
Theorem step_MCOPY_defined:
  !dst src sz d a n id outs s.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand sz s = SOME n ==>
    step_inst_base (mk_inst id MCOPY [dst; src; sz] outs) s =
      OK (mcopy (w2n d) (w2n a) (w2n n) s)
Proof
  simp[step_inst_base_def]
QED

Theorem lookup_var_mcopy[simp]:
  !x dst src sz s.
    lookup_var x (mcopy dst src sz s) = lookup_var x s
Proof
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem byte_chunk_head_run:
  !ptr off value sa dst sm sb s w.
    emit_op ADD [ptr; Lit off] sa = (dst, sm) /\
    emit_void MSTORE [dst; Lit value] sm = ((), sb) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       exec_write2_def, eval_operand_def, bind_outputs_def,
       lookup_var_update_var] >>
  rpt strip_tac >> simp[lookup_var_mstore, lookup_var_update_var] >>
  gvs[not_fresh_at_def]
QED

Theorem compile_store_byte_chunks_run:
  !ptr bs off sa sb s w.
    compile_store_byte_chunks ptr bs off sa = ((), sb) /\
    (!x. ptr = Var x ==> not_fresh_at sa x) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         emitted_insts_def, same_blocks_def, run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (h::bs) offset sa = ((), sb)` >>
  gvs[Once compile_store_byte_chunks_def, comp_bind_def,
      comp_ignore_bind_def, LET_THM, AllCaseEqs()] >>
  Cases_on `emit_op ADD [data_ptr; Lit (n2w offset)] sa` >>
  rename1 `emit_op ADD _ sa = (dst, sm)` >>
  Cases_on `emit_void MSTORE [dst; Lit (word_of_bytes T 0w
    (h::TAKE 31 (bs ++ REPLICATE 31 0w)))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >> gvs[] >>
  drule_all byte_chunk_head_run >> strip_tac >>
  `(!x. data_ptr = Var x ==> not_fresh_at sh x) /\
   eval_operand data_ptr t = SOME w` by
    (conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
     Cases_on `data_ptr` >> gvs[eval_operand_def]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    metis_tac[emitted_insts_append] >>
  simp[] >> conj_tac >- metis_tac[same_blocks_def] >>
  qexists `t'` >> conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sh sb` mp_tac) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sh x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  simp[]
QED

Theorem byte_literal_head_run:
  !size len sa buf sm sb s.
    compile_alloc_buffer size sa = (buf, sm) /\
    emit_void MSTORE [buf.buf_operand; Lit len] sm = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
          eval_operand buf.buf_operand t = SOME w /\ t.vs_labels = s.vs_labels /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
      emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       not_fresh_at_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (simp[run_inst_seq_def, step_inst_base_def, venomInstTheory.mk_inst_def, exec_alloca_def,
           exec_write2_def, eval_operand_def, lookup_var_update_var] >>
      rpt strip_tac >> simp[lookup_var_def, update_var_def, mstore_def,
                           FLOOKUP_UPDATE] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME alloc` >> PairCases_on `alloc` >>
  simp[run_inst_seq_def, step_inst_base_def, venomInstTheory.mk_inst_def, exec_alloca_def,
       exec_write2_def, eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> simp[lookup_var_mstore, lookup_var_update_var] >> metis_tac[]
QED

Theorem compile_bytelike_literal_run:
  !bs max_len sa buf sb s.
    compile_bytelike_literal bs max_len sa = (buf, sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
          eval_operand buf.buf_operand t = SOME w /\ t.vs_labels = s.vs_labels /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  Cases_on `compile_alloc_buffer (32 + (max_len + 31) DIV 32 * 32) sa` >>
  rename1 `compile_alloc_buffer _ sa = (b, sm)` >>
  Cases_on `emit_void MSTORE [b.buf_operand; Lit (n2w (LENGTH bs))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >>
  Cases_on `compile_store_byte_chunks b.buf_operand bs 32 sh` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u, sf)` >>
  Cases_on `u` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all byte_literal_head_run >> disch_then (qspec_then `s` strip_assume_tac) >>
  drule_all compile_store_byte_chunks_run >> strip_tac >>
  `sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    metis_tac[emitted_insts_append] >>
  simp[] >> conj_tac >- metis_tac[same_blocks_def] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl [`t'`, `w`] >> conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sh sb` mp_tac) >> simp[]) >>
  conj_tac >- (Cases_on `b.buf_operand` >> gvs[eval_operand_def]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sh x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  simp[]
QED

(* A focused definedness certificate for the reason encoder's memory code.
   Outputs may already be bound: the certificate tracks availability only. *)
Definition reason_known_def:
  reason_known ds s <=> !x. MEM x ds ==> ?w. lookup_var x s = SOME w
End

Definition reason_operand_def:
  reason_operand ds (Lit w) = T /\
  reason_operand ds (Var x) = MEM x ds /\
  reason_operand ds (Label l) = F
End

Definition reason_step_def:
  reason_step ds i <=>
    (?id sz out. i = mk_inst id ALLOCA [Lit sz] [out]) \/
    (?id opc a b out. (opc = ADD \/ opc = AND) /\
      i = mk_inst id opc [a; b] [out] /\
      reason_operand ds a /\ reason_operand ds b) \/
    (?id a out. i = mk_inst id MLOAD [a] [out] /\ reason_operand ds a) \/
    (?id a b. i = mk_inst id MSTORE [a; b] [] /\
      reason_operand ds a /\ reason_operand ds b) \/
    (?id a b c. i = mk_inst id MCOPY [a; b; c] [] /\
      reason_operand ds a /\ reason_operand ds b /\ reason_operand ds c)
End

Definition reason_prefix_def:
  reason_prefix ds [] es = (es = ds) /\
  reason_prefix ds (i::is) es =
    (reason_step ds i /\ reason_prefix (i.inst_outputs ++ ds) is es)
End

Theorem reason_operand_defined:
  !ds op s. reason_operand ds op /\ reason_known ds s ==>
    ?w. eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[reason_operand_def, eval_operand_def, reason_known_def]
QED

Theorem reason_known_update:
  !ds s out w. reason_known ds s ==>
    reason_known (out::ds) (update_var out w s)
Proof
  simp[reason_known_def, lookup_var_update_var] >> metis_tac[]
QED

Theorem reason_step_sound:
  !ds i s. reason_step ds i /\ reason_known ds s ==>
    ?t. step_inst_base i s = OK t /\
        reason_known (i.inst_outputs ++ ds) t /\ t.vs_labels = s.vs_labels
Proof
  rw[reason_step_def]
  >- (qspecl_then [`id`, `sz`, `out`, `s`] strip_assume_tac step_alloca_frame >>
      qexists `s1` >> simp[venomInstTheory.mk_inst_def, reason_known_def] >>
      rpt strip_tac >> Cases_on `x = out` >> gvs[reason_known_def]) >>
  imp_res_tac reason_operand_defined >> gvs[]
  >~ [`step_inst_base (mk_inst _ ADD _ _) _`] >-
    (irule_at Any emitHelperPropsTheory.step_ADD >>
     simp[reason_known_update, update_var_def] >> metis_tac[])
  >~ [`step_inst_base (mk_inst _ AND _ _) _`] >-
    (irule_at Any emitHelperPropsTheory.step_AND >>
     simp[reason_known_update, update_var_def] >> metis_tac[])
  >~ [`step_inst_base (mk_inst _ MLOAD _ _) _`] >-
    (irule_at Any step_MLOAD >>
     simp[reason_known_update, update_var_def] >> metis_tac[])
  >~ [`step_inst_base (mk_inst _ MSTORE _ _) _`] >-
    (irule_at Any emitHelperPropsTheory.step_MSTORE >>
     gvs[reason_known_def]) >>
  irule_at Any step_MCOPY_defined >>
  gvs[reason_known_def, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]
QED

Theorem reason_prefix_sound:
  !is ds es s. reason_prefix ds is es /\ reason_known ds s ==>
    ?t. run_inst_seq is s = OK t /\ reason_known es t /\ t.vs_labels = s.vs_labels
Proof
  Induct >> simp[reason_prefix_def, run_inst_seq_def] >> rpt strip_tac >>
  drule_all reason_step_sound >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem reason_step_simple:
  !ds i. reason_step ds i ==> i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode
Proof
  rw[reason_step_def] >> simp[venomInstTheory.mk_inst_def, is_terminator_def]
QED

Theorem reason_prefix_simple:
  !is ds es. reason_prefix ds is es ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is
Proof
  Induct >> simp[reason_prefix_def] >> metis_tac[reason_step_simple]
QED

Theorem reason_prefix_alloca_load_probe[local]:
  reason_prefix []
    [mk_inst 0 ALLOCA [Lit 0w] ["p"]; mk_inst 1 MLOAD [Var "p"] ["p"]]
    ["p"; "p"]
Proof
  simp[reason_prefix_def, reason_step_def, reason_operand_def,
       venomInstTheory.mk_inst_def]
QED

Theorem reason_prefix_mcopy_probe[local]:
  reason_prefix ["p"] [mk_inst 0 MCOPY [Var "p"; Var "p"; Lit 0w] []] ["p"]
Proof
  simp[reason_prefix_def, reason_step_def, reason_operand_def,
       venomInstTheory.mk_inst_def]
QED

Theorem compile_revert_reason_certificate:
  !cenv msg_ty buf msg_type msg_size sa sb ds.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) ==>
    ?prefix es id off len.
      emitted_insts sa sb = prefix ++ [mk_inst id REVERT [off; len] []] /\
      reason_prefix ds prefix es /\ reason_operand es off /\
      reason_operand es len /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_revert_with_reason_def, unwrap_value_def, contextTheory.base_ptr_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  qmatch_goalsub_abbrev_tac `sa.cs_current_insts ++ code` >>
  simp[emitted_insts_def, DROP_APPEND1, same_blocks_def] >>
  qexists `TAKE 31 code` >>
  simp[Abbr `code`, TAKE_def] >>
  simp[reason_prefix_def, venomInstTheory.mk_inst_def] >>
  rpt conj_tac >>
  simp[reason_step_def, venomInstTheory.mk_inst_def, reason_operand_def] >>
  Cases_on `buf.buf_operand` >> gvs[reason_operand_def]
QED

Theorem reason_prefix_revert_run:
  !is ds es s id off len.
    reason_prefix ds is es /\ reason_known ds s /\
    reason_operand es off /\ reason_operand es len ==>
    ?t. run_inst_seq (is ++ [mk_inst id REVERT [off; len] []]) s =
          Abort Revert_abort t /\ t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >> drule_all reason_prefix_sound >> strip_tac >>
  `?ow. eval_operand off t = SOME ow` by metis_tac[reason_operand_defined] >>
  `?lw. eval_operand len t = SOME lw` by metis_tac[reason_operand_defined] >>
  qpat_assum `run_inst_seq is s = OK t`
    (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst id REVERT [off; len] []]` mp_tac) >>
  simp[run_inst_seq_def] >>
  `step_inst_base (mk_inst id REVERT [off; len] []) t =
    Abort Revert_abort (revert_state (set_returndata
      (TAKE (w2n lw) (DROP (w2n ow) t.vs_memory ++ REPLICATE (w2n lw) 0w)) t))`
    by (simp[venomInstTheory.mk_inst_def] >> irule step_revert_behavior >> simp[]) >>
  simp[revert_state_def, set_returndata_def]
QED

Theorem compile_revert_reason_run:
  !cenv msg_ty buf msg_type msg_size sa sb s ds.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    reason_known ds s /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
        t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  drule_all compile_revert_reason_certificate >> strip_tac >> simp[] >>
  irule reason_prefix_revert_run >> metis_tac[]
QED

Theorem reason_prefix_revert_frag:
  !ctx sa sb ds es is id off len R.
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      (is ++ [mk_inst id REVERT [off; len] []]) /\
    reason_prefix ds is es /\ reason_operand es off /\ reason_operand es len /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R
Proof
  rpt strip_tac >>
  qabbrev_tac `sm = sa with cs_current_insts := sa.cs_current_insts ++ is` >>
  irule frag_exec_seq >> qexists `reason_known es` >> qexists `sm` >>
  conj_tac >- (simp[cs_extends_def, Abbr `sm`] >> qexists `[]` >> simp[]) >>
  conj_tac >- (simp[cs_extends_def, Abbr `sm`] >> qexists `[]` >>
              fs[same_blocks_def]) >>
  conj_tac
  >- (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is`
        by metis_tac[reason_prefix_simple] >>
      irule frag_exec_run_inst_seq >>
      simp[Abbr `sm`, emitted_insts_def, DROP_APPEND1] >>
      rpt strip_tac >> disj1_tac >>
      drule_all reason_prefix_sound >> strip_tac >> qexists `t` >>
      fs[reason_known_def, lookup_var_def])
  >- (irule frag_exec_step_abort >>
      fs[Abbr `sm`, same_blocks_def] >>
      rpt strip_tac >>
      `?ow. eval_operand off s = SOME ow` by metis_tac[reason_operand_defined] >>
      `?lw. eval_operand len s = SOME lw` by metis_tac[reason_operand_defined] >>
      qexists `0` >> simp[step_inst_non_invoke, venomInstTheory.mk_inst_def] >>
      irule_at Any step_revert_behavior >> simp[])
QED
Theorem compile_revert_reason_frag:
  !ctx cenv msg_ty buf msg_type msg_size sa sb ds R.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R
Proof
  rpt strip_tac >> drule_all compile_revert_reason_certificate >> strip_tac >>
  irule reason_prefix_revert_frag >> simp[] >> metis_tac[]
QED

Theorem compile_store_byte_chunks_simple:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def, emitted_insts_def,
         same_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (h::bs) offset sa = ((), sb)` >>
  gvs[Once compile_store_byte_chunks_def, comp_bind_def,
      comp_ignore_bind_def, LET_THM, AllCaseEqs()] >>
  Cases_on `emit_op ADD [data_ptr; Lit (n2w offset)] sa` >>
  rename1 `emit_op ADD _ sa = (dst, sm)` >>
  Cases_on `emit_void MSTORE [dst; Lit (word_of_bytes T 0w
    (h::TAKE 31 (bs ++ REPLICATE 31 0w)))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   same_blocks sa sh /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sh)` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     simp[emitted_insts_def, DROP_APPEND1, same_blocks_def,
          venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb`
    by metis_tac[emitted_insts_append] >>
  simp[] >> metis_tac[same_blocks_def, APPEND_ASSOC]
QED

Theorem compile_bytelike_literal_simple:
  !bs ml sa buf sb.
    compile_bytelike_literal bs ml sa = (buf, sb) ==>
    (?x. buf.buf_operand = Var x) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  Cases_on `compile_alloc_buffer (32 + (ml + 31) DIV 32 * 32) sa` >>
  rename1 `compile_alloc_buffer _ sa = (b, sm)` >>
  Cases_on `emit_void MSTORE [b.buf_operand; Lit (n2w (LENGTH bs))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >>
  Cases_on `compile_store_byte_chunks b.buf_operand bs 32 sh` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u, sf)` >>
  Cases_on `u` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule compile_store_byte_chunks_simple >> strip_tac >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   (?x. b.buf_operand = Var x) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sh)` by
    (gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     simp[emitted_insts_def, DROP_APPEND1, venomInstTheory.mk_inst_def,
          is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb`
    by metis_tac[emitted_insts_append] >> simp[]
QED

Theorem compile_bytelike_revert_frag:
  !ctx cenv bs ml msg_ty msg_type msg_size sa sm buf sb R.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    ~is_word_type msg_ty /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sm = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. T) (\s. F) R
Proof
  rpt strip_tac >> drule compile_bytelike_literal_simple >> strip_tac >>
  `reason_operand [x] buf.buf_operand` by simp[reason_operand_def] >>
  drule_all compile_revert_reason_certificate >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   same_blocks sa sm` by
    (drule compile_bytelike_literal_run >>
     disch_then (qspec_then `ARB` strip_assume_tac) >> simp[]) >>
  irule frag_exec_seq >> qexists `reason_known [x]` >> qexists `sm` >>
  conj_tac >- (simp[cs_extends_def] >> qexists `[]` >> fs[same_blocks_def]) >>
  conj_tac >- (simp[cs_extends_def] >> qexists `[]` >> fs[same_blocks_def] >>
              metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  conj_tac
  >- (irule frag_exec_run_inst_seq >> fs[same_blocks_def] >>
      rpt strip_tac >> disj1_tac >>
      drule compile_bytelike_literal_run >>
      disch_then (qspec_then `s` strip_assume_tac) >> qexists `t` >>
      gvs[reason_known_def, eval_operand_def, lookup_var_def]) >>
  irule compile_revert_reason_frag >> metis_tac[]
QED


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
