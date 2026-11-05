Theory concretizeLayoutLocalHaltAbort
Ancestors concretizeLayoutLocalLog concretizeLayoutLocalValues

Theorem concretize_halt_abort_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  joint_trace vs0 C q0 es qs q /\
  EL (LENGTH es) (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (LENGTH es))
    (\s t. dead_result_rel
      <| d_stor := K (K UNIV); d_trans := K (K UNIV); d_imm := K UNIV;
         d_ret := K {} |> (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (LENGTH es)) tn un /\
  accounts_agree_except
    (D with d_stor := (\a st. if a = s.vs_call_ctx.cc_address then tn.t_stor else {}))
    s.vs_accounts t.vs_accounts /\
  transient_agree_except
    (D with d_trans := (\a st. if a = s.vs_call_ctx.cc_address then tn.t_trans else {}))
    s.vs_transient t.vs_transient /\
  imms_agree_except (D with d_imm := K tn.t_imm) s.vs_immutables t.vs_immutables /\
  LIST_REL (request_agree_except D) s.vs_requests t.vs_requests /\
  s.vs_outcomes = t.vs_outcomes /\
  MEM inst.inst_opcode
    [RETURN; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst_base inst s = r /\
  ((?p. r = Halt p) \/ (?a p. r = Abort a p)) ==>
  ?r'. step_inst_base inst t = r' /\ dead_result_rel D r r'
Proof
  cheat
QED
