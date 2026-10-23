(*
 * Expression simulation in the unit context (#636, part 1)
 *
 * The judgment expr_sim: the fragment of an expression, run from
 * stmt_state_rel at the source state where the expression is evaluated,
 * either reaches its end with stmt_state_rel at the source state after it
 * and the operand holding its value, or, where the source raises a runtime
 * error or an assertion, exits with the Abort result_rel matches.
 *
 * TOP-LEVEL:
 *   expr_exit, expr_res_ok, expr_sim
 *   expr_sim_expr_frag     — expr_sim gives loweringSlice's expr_frag
 *   frag_exec_run_inst_seq_drop_fresh — a straight-line fragment, given
 *                            by its run from the state without the
 *                            temporaries fresh at its start (varsExt), as
 *                            the fresh_vars_wrt lemmas state it
 *   stmt_state_rel_vars_frame, stmt_state_rel_vars_ext,
 *   stmt_state_rel_drop_fresh — stmt_state_rel reads the variables only
 *                            through the live locals' pointers
 *   compile_literal_word_sim — bool, integer and decimal literals
 *   compile_name_word_sim  — a word local
 *   compile_env_sim        — environment reads (msg.sender, block.number,
 *                            ...), all but blockhash
 *
 * Helpers: expr_exit_INL, emit_op_frag, eval_expr_env,
 *   lower_value_env
 *
 * Values are related by val_to_w256, as in expr_frag and
 * compile_expr_correct.  For address and bytesN values that is the length
 * heuristic of val_to_w256, which is wrong for bytes20; the leaves here
 * avoid it (no bytes literals, word_value locals).
 *)

Theory exprSim
Ancestors
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs
  venomExecSemantics venomInst venomState

(* ===== The judgment ===== *)

(* The exits a source result allows: a runtime error any Abort, an
   assertion a revert, or an exceptional halt for "UNREACHABLE", as
   result_rel and external_call_result_rel relate them. *)
Definition expr_exit_def:
  (expr_exit (INR (Error (RuntimeError m))) (Abort a s) <=> T) /\
  (expr_exit (INR (AssertException str)) (Abort a s) <=>
     a = Revert_abort \/ (a = ExHalt_abort /\ str = "UNREACHABLE")) /\
  (expr_exit _ _ <=> F)
End

Theorem expr_exit_INL[simp]:
  !x r. ~expr_exit (INL x) r
Proof
  Cases_on `r` >> simp[expr_exit_def]
QED

(* The source results the judgment speaks of: a value, a runtime error or
   an assertion.  Type errors and control exceptions are left out. *)
Definition expr_res_ok_def:
  expr_res_ok (res : toplevel_value + exception) <=>
    (?v. res = INL (Value v)) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?str. res = INR (AssertException str))
End

(* The fragment of e lowered as a value of type ty, run from a state
   related at es, the source state where e is evaluated, under the code
   premises of the statement lemmas.  On a value it reaches its end
   related at the source state after e, the operand holding the value, the
   variables handed out before it and the allocations made before it kept.
   On a runtime error or an assertion it exits as expr_exit allows.  This
   is expr_frag (loweringSlice) with the failing outcomes added. *)
Definition expr_sim_def:
  expr_sim ctx func cenv cx ty e es <=>
    !sa sb op res es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      eval_expr cx e es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
        (\s. ?v. res = INL (Value v) /\
                 stmt_state_rel func cenv cx es' s /\
                 eval_operand op s = SOME (val_to_w256 v) /\
                 (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                        lookup_var x s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b))
        (expr_exit res)
End

Theorem expr_sim_expr_frag:
  !ctx func cenv cx ty e es R.
    expr_sim ctx func cenv cx ty e es ==> expr_frag ctx func cenv cx ty e es R
Proof
  rw[expr_sim_def, expr_frag_def] >>
  first_x_assum (qspecl_then [`sa`, `sb`, `op`, `INL (Value v)`, `es'`, `s0`]
                   mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                `\s. ?v'. INL (Value v) = INL (Value v') /\
                     stmt_state_rel func cenv cx es' s /\
                     eval_operand op s = SOME (val_to_w256 v') /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b)`,
                `expr_exit (INL (Value v))`] >>
  simp[expr_exit_def] >> rw[] >> gvs[]
QED

(* ===== stmt_state_rel and the variables ===== *)

(* stmt_state_rel reads the variables only through the pointers of the
   live locals. *)
Theorem stmt_state_rel_vars_frame:
  !func cenv cx es s V.
    stmt_state_rel func cenv cx es s /\
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p (s with vs_vars := V) = lookup_var p s) ==>
    stmt_state_rel func cenv cx es (s with vs_vars := V)
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes (s with vs_vars := V)` by
    (irule local_ptrs_rel_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >> conj_tac
     >- metis_tac[] >>
     rpt strip_tac >> gvs[]) >>
  `alloca_inv (s with vs_vars := V)` by
    (irule alloca_inv_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
     immutables_rel_def, logs_rel_def, contract_storage_def,
     contract_transient_def] >>
  metis_tac[]
QED

Theorem stmt_state_rel_vars_ext:
  !func cenv cx es t t'.
    stmt_state_rel func cenv cx es t /\ vars_ext t t' ==>
    stmt_state_rel func cenv cx es t'
Proof
  rw[vars_ext_def] >>
  qpat_x_assum `t' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[lookup_var_def] >> metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem stmt_state_rel_drop_fresh:
  !func cenv cx es st s.
    local_ptrs_reserved cenv st ==>
    (stmt_state_rel func cenv cx es (drop_fresh st s) <=>
     stmt_state_rel func cenv cx es s)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (irule stmt_state_rel_vars_ext >> qexists_tac `drop_fresh st s` >>
      simp[vars_ext_drop_fresh]) >>
  simp[drop_fresh_def] >> irule stmt_state_rel_vars_frame >> simp[] >>
  rpt strip_tac >> simp[GSYM drop_fresh_def] >>
  irule lookup_var_drop_fresh >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* ===== Straight-line fragments from the cleaned state ===== *)

(* frag_exec_run_inst_seq where the run is known from drop_fresh st s, as
   the fresh_vars_wrt lemmas give it, and the fragment's end is wanted in
   any state with more variables bound. *)
Theorem frag_exec_run_inst_seq_drop_fresh:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode) (emitted_insts st st') /\
    (!s. P s ==>
       (?t0. run_inst_seq (emitted_insts st st') (drop_fresh st s) = OK t0 /\
             !t. vars_ext t0 t ==>
                 Q (t with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
       (?a t0. run_inst_seq (emitted_insts st st') (drop_fresh st s) =
                 Abort a t0 /\
               !t n. vars_ext t0 t ==> R (Abort a (t with vs_inst_idx := n))))
    ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> irule frag_exec_run_inst_seq >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`emitted_insts st st'`, `drop_fresh st s`, `s`] mp_tac
    run_inst_seq_vars_ext >>
  (impl_tac >- simp[vars_ext_drop_fresh, EVERY_MEM]) >>
  simp[vars_ext_result_def] >> strip_tac >> metis_tac[]
QED

(* ===== Leaves ===== *)

(* A word local held through its pointer (loweringSlice's
   compile_name_word_frag). *)
Theorem compile_name_word_sim:
  !ctx func cenv cx ty ann id es p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `ann`, `id`, `es`,
               `expr_exit (INL (Value entry.value))`, `p`, `sz`, `entry`]
    mp_tac compile_name_word_frag >>
  asm_rewrite_tac[] >> strip_tac >>
  rw[expr_sim_def] >> gvs[] >>
  qpat_x_assum `expr_frag _ _ _ _ _ _ _ _` mp_tac >>
  rw[expr_frag_def] >>
  first_x_assum (qspecl_then [`sa`, `sb`, `op`, `entry.value`, `es`, `s0`]
                   mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                `\s. stmt_state_rel func cenv cx es s /\
                     eval_operand op s = SOME (val_to_w256 entry.value) /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b)`,
                `expr_exit (INL (Value entry.value))`] >>
  simp[]
QED

(* A bool, integer or decimal literal: a Lit, no code. *)
Theorem compile_literal_word_sim:
  !ctx func cenv cx ty ann l es.
    (?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_def] >>
  gvs[Once evaluate_def, return_def] >>
  TRY (Cases_on `b`) >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def] >>
  irule frag_exec_refl >>
  simp[eval_operand_def, val_to_w256_def]
QED

(* One instruction that computes w from the state and writes it to a fresh
   variable. *)
Theorem emit_op_frag:
  !ctx func cenv cx es opc args sa op sb s0 w R.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    opc <> INVOKE /\ ~is_terminator opc /\
    (stmt_state_rel func cenv cx es s0 ==>
     !out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. stmt_state_rel func cenv cx es s /\ eval_operand op s = SOME w /\
           (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[venomInstTheory.mk_inst_def] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> gvs[] >>
  qexists_tac `update_var out w s0` >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, stmt_state_rel_inst_idx] >>
  conj_tac >- (irule stmt_state_rel_update_var >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `out = x` >> gvs[lookup_var_def]
QED

Theorem eval_expr_env:
  !cx ann item es res es'.
    eval_expr cx (Builtin ann (Env item) []) es = (res, es') /\
    expr_res_ok res /\ item <> PrevHash ==>
    es' = es /\
    ?v. res = INL (Value v) /\
        evaluate_builtin cx es.accounts ann (Env item) [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def] >>
  simp[Once evaluate_def, return_def] >>
  Cases_on `item` >> fs[evaluate_builtin_def, return_def, raise_def] >>
  rw[] >> gvs[expr_res_ok_def]
QED

Theorem lower_value_env:
  !cenv ty ann item sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Env item) []) sa =
      (op, sb) ==>
    compile_env_var item sa = (op, sb)
Proof
  rpt gen_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def] >>
  Cases_on `compile_env_var item sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

(* An environment read (msg.sender, block.timestamp, ...), but blockhash,
   which reads the block-hash oracle, and msg.gas, which the source does
   not evaluate. *)
Theorem compile_env_sim:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rw[expr_sim_def] >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  drule lower_value_env >> strip_tac >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                `\s. stmt_state_rel func cenv cx es s /\
                     eval_operand op s = SOME (val_to_w256 v) /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b)`,
                `expr_exit (INL (Value v))`] >>
  simp[] >>
  Cases_on `item` >>
  gvs[compile_env_var_def, evaluate_builtin_def] >>
  drule emit_op_frag >> disch_then irule >>
  simp[is_terminator_def] >> rpt strip_tac >>
  simp[step_inst_base_def, exec_read0_def, venomInstTheory.mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
     val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]
QED
