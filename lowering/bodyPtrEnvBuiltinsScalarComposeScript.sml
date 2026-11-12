(* Scalar suffixes retain the original protected frame. *)
Theory bodyPtrEnvBuiltinsScalarCompose
Ancestors
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsGhostCompose bodyPtrDefs
  exprLoweringProps stmtFragPtr compileEnv venomState finite_map list
  bodyPtrEnvBuiltinsEdges exprSimAccounts emitHelperProps emitHelper
  fragGasPathPtr venomInst venomExecSemantics

Theorem scalar_frame_kept_trans:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ghost_kept cenv es sm G tn s G' tn' /\
  (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
  sa.cs_next_id <= sm.cs_next_id /\
  s.vs_allocas = s0.vs_allocas /\
  local_ptrs_rel ctx cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id ==> FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w` by metis_tac[] >>
  `MAP FDOM es.scopes = MAP FDOM es.scopes` by simp[] >>
  drule_all ghost_kept_locals_trans >> simp[]
QED

Theorem emit_scalar_builtin_append:
  emit_op opc args sm = (op,sb) /\ fn_has_code sm sb fn /\
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!a. MEM a args ==> op_taint tn a = {}) /\
  gas_path_ptr D 0 ctx fn PG G0 tn0 s0 k G tn (OK s) /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel fn cenv es.scopes s0 /\
  stmt_state_rel ctx fn cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
  s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
  step_inst_base (mk_inst sm.cs_next_id opc args
    [STRING #"%" (toString sm.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) w s) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0
      (k + (if opc = GAS then 1 else 0)) G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\
    (opc <> ADD /\ opc <> SUB ==> op_prov G' op = NONE) /\
    eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas
Proof
  strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x` by metis_tac[] >>
  `ghost_kept cenv es sm G tn s G tn` by simp[ghost_kept_refl] >>
  drule_all emit_scalar_builtin_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (drule_all scalar_frame_kept_trans >> simp[]) >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `sb.cs_next_id = sm.cs_next_id + 1` by
    metis_tac[emitted_insts_emit_op] >>
  `gas_path_ptr D 0 ctx fn PG G0 tn0 s0
    (k + (if opc = GAS then 1 else 0)) G' tn' (OK t)` by
    (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  metis_tac[cs_extends_trans]
QED
