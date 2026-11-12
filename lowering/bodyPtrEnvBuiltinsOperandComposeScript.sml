(* Allocation-aware scalar suffixes and observation-free outcome composition. *)
Theory bodyPtrEnvBuiltinsOperandCompose
Ancestors
  bodyPtrEnvBuiltinsOperandFrame bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsEdges
  gasSummaryComposePtr bodyPtrDefs exprLoweringProps stmtFragPtr
  compileEnv venomState venomInst venomExecSemantics list
  gasSummary fragGasPathPtr vyperInterpreter exprSimDefs

Theorem operand_scalar_suffix_run:
  lower_value compile_expr cenv ty e sa = (arg,sm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es sa sm s0 ee v arg s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  emit_op opc args sm = (op,sb) /\ fn_has_code sm sb fn /\
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!a. MEM a args ==> op_taint tn a = {}) /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx ee G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx ee s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  step_inst_base (mk_inst sm.cs_next_id opc args
    [STRING #"%" (toString sm.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s (if opc = GAS then 1 else 0) G' tn' (OK t) /\
    ghost_inv d cenv cx ee G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\
    (opc <> ADD /\ opc <> SUB ==> op_prov G' op = NONE) /\
    eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[] >>
  `ghost_kept cenv ee sm G tn s G tn` by simp[ghost_kept_refl] >>
  drule_all emit_scalar_builtin_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (drule_all operand_suffix_ghost_kept >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[]
QED

Theorem scalar_suffix_marked_compose:
  gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
    marks (INL v) ee G tn (OK t) /\
  (!tail. next v (ee with gas_obs := tail) =
    (res,fin with gas_obs := tail)) /\
  gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' (OK t') ==>
  gas_marked_exec_ptr D (ctx,fn) PG (bind source next)
    (es,s0,G0,tn0) marks res fin G' tn' (OK t')
Proof
  strip_tac >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
         |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`G`, `ee`, `t`, `tn`, `v`] >> simp[] >>
  simp[gas_marked_exec_ptr_def]
QED

Theorem scalar_suffix_summary_compose:
  gas_summary_ptr_at D (ctx,fn) PG marks source (es,s0,G0,tn0) Q
    (\res ee gt r. expr_exit res r) /\
  (!res ee G tn t.
    gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
      marks res ee G tn (OK t) /\
    Q (res : value + exception) (ee with gas_obs := []) G tn t ==>
    ?v res' fin G' tn' t'. res = INL v /\
      (!tail. next v ((ee with gas_obs := []) with gas_obs := tail) =
        (res',fin with gas_obs := tail)) /\
      gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' (OK t') /\
      Q' (res' : value + exception) (fin with gas_obs := []) G' tn' t') ==>
  gas_summary_ptr_at D (ctx,fn) PG marks (bind source next)
    (es,s0,G0,tn0) Q' (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_summary_ptr_at_marked] >> strip_tac >> gvs[]
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule_all scalar_suffix_marked_compose >> strip_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> fs[expr_exit_def]
QED

Theorem scalar_suffix_outcome_compose:
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0) Q
    (\res ee gt r. expr_exit res r) /\
  (!marks res ee G tn t.
    gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
      marks res ee G tn (OK t) /\
    Q (res : value + exception) (ee with gas_obs := []) G tn t ==>
    ?v res' fin G' tn' t'. res = INL v /\
      (!tail. next v ((ee with gas_obs := []) with gas_obs := tail) =
        (res',fin with gas_obs := tail)) /\
      gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' (OK t') /\
      Q' (res' : value + exception) (fin with gas_obs := []) G' tn' t') /\
  (!marks err ee leaf finish.
    gas_exempt_cert F tops (ctx,fn) (ignore_bind source (return ()))
      (es,s0) marks (err,ee) (leaf,finish) ==>
    gas_exempt_cert F tops (ctx,fn) (ignore_bind (bind source next) (return ()))
      (es,s0) marks (err,ee) (leaf,finish)) ==>
  gas_outcome_ptr D tops (ctx,fn) PG (bind source next)
    (es,s0,G0,tn0) Q' (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule scalar_suffix_summary_compose >> goal_assum (drule_at Any) >>
      first_x_assum (qspec_then `marks` ACCEPT_TAC)) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  first_x_assum irule >> simp[]
QED
