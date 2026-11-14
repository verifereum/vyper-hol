Theory readonlyInvokeCopyFwdStepsCore
Ancestors
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdEffects readonlyInvokeCopyFwdRel
  taintAgree ptrDiscipline venomState venomExecSemantics
  internalReturnCopyFwdSim finite_map words list pred_set

(* Only ghost entry indices are recomputed here.  The inherited relocation
   map, actual saved callers, current copies and suspended copies stay fixed. *)
Theorem ricf_cert_bind:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_value_agree sites p m x y /\
  u = update_var out x s /\ v = update_var out y t /\
  H = set_prov G0 [out] p /\
  un = tn0 with t_var := set_var_taint tn0.t_var [out] m /\
  Hentry = (if u.vs_prev_bb = NONE then H else entry_prov fn u H) /\
  unentry = (if u.vs_prev_bb = NONE then un else entry_taint_vars fn u un) ==>
  ricf_cert_core D ids stk PG Hentry unentry fn
    sites maps targets H un cur curs u v
Proof
  strip_tac >> gvs[] >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  simp[ricf_live_boundary_core_def, ircf_dead_def, update_var_def,
       ricf_complete_params_def] >>
  rpt conj_tac
  >- (drule_all ricf_frame_agree_update_var >>
      simp[update_var_def, ircf_dead_def, ricf_complete_params_def])
  >- gvs[ricf_live_stack_agree_def, merge_callee_state_def, update_var_def]
  >- (gvs[ircf_cross_def, update_var_def] >> metis_tac[])
  >> gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, update_var_def]
  >> metis_tac[]
QED

Theorem ricf_cert_eval_phis:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  eval_phis s ins = OK u ==>
  ?v. eval_phis t ins = OK v /\
    ricf_cert_core D ids stk PG
      (if u.vs_prev_bb = NONE then phis_prov s.vs_prev_bb G0 ins
       else entry_prov fn u (phis_prov s.vs_prev_bb G0 ins))
      (if u.vs_prev_bb = NONE then tn0 with t_var := phis_taint s.vs_prev_bb tn0 ins
       else entry_taint_vars fn u (tn0 with t_var := phis_taint s.vs_prev_bb tn0 ins))
      fn sites maps targets (phis_prov s.vs_prev_bb G0 ins)
      (tn0 with t_var := phis_taint s.vs_prev_bb tn0 ins) cur curs u v
Proof
  strip_tac >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  drule_all ricf_frame_agree_eval_phis >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  qpat_assum `eval_phis s ins = OK _`
    (mp_tac o MATCH_MP venomExecProofsTheory.eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  qpat_assum `eval_phis t ins = OK _`
    (mp_tac o MATCH_MP venomExecProofsTheory.eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  gvs[ircf_dead_def, ricf_complete_params_def] >>
  rpt conj_tac
  >- (fs[ricf_live_stack_agree_def] >>
      gvs[merge_callee_state_def])
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >> gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[]
QED

(* Canonical boundary indices; operation adapters expose their raw H/un. *)
Definition ricf_effective_prov_def:
  ricf_effective_prov fn s H =
    if s.vs_prev_bb = NONE then H else entry_prov fn s H
End

Definition ricf_effective_taint_def:
  ricf_effective_taint fn s un =
    if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un
End

Theorem ricf_cert_reconstruct:
  ricf_frame_agree D (ircf_dead ids u stk) sites
    (ricf_complete_params PG u.vs_params) H un u v /\
  ricf_live_stack_agree D ids un maps stk targets u v /\
  ircf_cross un cur u v /\ ricf_cert_crosses un curs stk u v ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn u H) (ricf_effective_taint fn u un) fn
    sites maps targets H un cur curs u v
Proof
  simp[ricf_cert_core_def, ricf_live_boundary_core_def,
       ricf_effective_prov_def, ricf_effective_taint_def]
QED

Theorem ricf_cert_exec_pure1:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_operands = [a] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
  ricf_value_agree sites p m (f x) (f y) ==>
  exec_pure1 f inst s = OK (update_var out (f x) s) /\
  exec_pure1 f inst t = OK (update_var out (f y) t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (f x) s) (set_prov G0 [out] p))
    (ricf_effective_taint fn (update_var out (f x) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn
    sites maps targets (set_prov G0 [out] p)
    (tn0 with t_var := set_var_taint tn0.t_var [out] m)
    cur curs (update_var out (f x) s) (update_var out (f y) t)
Proof
  strip_tac >> simp[exec_pure1_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_exec_pure2:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME x' /\
  eval_operand b s = SOME y /\ eval_operand b t = SOME y' /\
  ricf_value_agree sites p m (f x y) (f x' y') ==>
  exec_pure2 f inst s = OK (update_var out (f x y) s) /\
  exec_pure2 f inst t = OK (update_var out (f x' y') t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (f x y) s) (set_prov G0 [out] p))
    (ricf_effective_taint fn (update_var out (f x y) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn
    sites maps targets (set_prov G0 [out] p)
    (tn0 with t_var := set_var_taint tn0.t_var [out] m)
    cur curs (update_var out (f x y) s) (update_var out (f x' y') t)
Proof
  strip_tac >> simp[exec_pure2_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_exec_pure3:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_operands = [a;b;c] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME x' /\
  eval_operand b s = SOME y /\ eval_operand b t = SOME y' /\
  eval_operand c s = SOME z /\ eval_operand c t = SOME z' /\
  ricf_value_agree sites p m (f x y z) (f x' y' z') ==>
  exec_pure3 f inst s = OK (update_var out (f x y z) s) /\
  exec_pure3 f inst t = OK (update_var out (f x' y' z') t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (f x y z) s) (set_prov G0 [out] p))
    (ricf_effective_taint fn (update_var out (f x y z) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn
    sites maps targets (set_prov G0 [out] p)
    (tn0 with t_var := set_var_taint tn0.t_var [out] m)
    cur curs (update_var out (f x y z) s) (update_var out (f x' y' z') t)
Proof
  strip_tac >> simp[exec_pure3_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_exec_read0:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_outputs = [out] /\ ricf_value_agree sites p m (f s) (g t) ==>
  exec_read0 f inst s = OK (update_var out (f s) s) /\
  exec_read0 g inst t = OK (update_var out (g t) t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (f s) s) (set_prov G0 [out] p))
    (ricf_effective_taint fn (update_var out (f s) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn
    sites maps targets (set_prov G0 [out] p)
    (tn0 with t_var := set_var_taint tn0.t_var [out] m)
    cur curs (update_var out (f s) s) (update_var out (g t) t)
Proof
  strip_tac >> simp[exec_read0_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

Theorem ricf_cert_exec_read1:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_operands = [a] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
  ricf_value_agree sites p m (f x s) (g y t) ==>
  exec_read1 f inst s = OK (update_var out (f x s) s) /\
  exec_read1 g inst t = OK (update_var out (g y t) t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (f x s) s) (set_prov G0 [out] p))
    (ricf_effective_taint fn (update_var out (f x s) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out] m)) fn
    sites maps targets (set_prov G0 [out] p)
    (tn0 with t_var := set_var_taint tn0.t_var [out] m)
    cur curs (update_var out (f x s) s) (update_var out (g y t) t)
Proof
  strip_tac >> simp[exec_read1_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >> metis_tac[]
QED

(* The read is scalar even when its address is relocated.  gam may be the
   inherited site triples, current copies or a suspended certificate. *)
Theorem ricf_cert_mload:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ircf_cross tn0 gam s t /\ (db,sb,sz) IN gam /\ off + 32 <= sz /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [a] /\
  inst.inst_outputs = [out] /\
  eval_operand a s = SOME (n2w (db+off)) /\
  eval_operand a t = SOME (n2w (sb+off)) /\
  db+off < dimword (:256) /\ sb+off < dimword (:256) ==>
  step_inst_base inst s = OK (update_var out (mload (db+off) s) s) /\
  step_inst_base inst t = OK (update_var out (mload (sb+off) t) t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (update_var out (mload (db+off) s) s)
      (set_prov G0 [out] NONE))
    (ricf_effective_taint fn (update_var out (mload (db+off) s) s)
      (tn0 with t_var := set_var_taint tn0.t_var [out]
        (mem_word_taint tn0.t_mem (db+off)))) fn
    sites maps targets (set_prov G0 [out] NONE)
    (tn0 with t_var := set_var_taint tn0.t_var [out]
      (mem_word_taint tn0.t_mem (db+off))) cur curs
    (update_var out (mload (db+off) s) s)
    (update_var out (mload (sb+off) t) t)
Proof
  strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_read1_def] >>
  irule ricf_cert_bind >>
  simp[ricf_effective_prov_def, ricf_effective_taint_def] >>
  `ricf_value_agree sites NONE (mem_word_taint tn0.t_mem (db+off))
     (mload (db+off) s) (mload (sb+off) t)` by
    (simp_tac std_ss [ricf_value_agree_inactive] >>
     metis_tac[ricf_cross_mload]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
