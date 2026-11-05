Theory concretizeLayoutLocalState
Ancestors concretizeLayoutLocalLog concretizeLayoutLocalValues

Theorem concretize_state_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
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
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  storage_agree_except tn.t_stor (contract_storage s) (contract_storage t) /\
  storage_agree_except tn.t_trans (contract_transient s) (contract_transient t) /\
  s.vs_outcomes = t.vs_outcomes /\ dead_wf D /\ taint_within D C vs0 /\
  c < LENGTH es /\ EL c es = SOME (OriginOrdinary fuel post) /\
  MEM inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE; ISTORE; RETURNDATACOPY] /\
  step_inst_base inst s = OK post ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post =
      SND o_f (origin_set rv inst.inst_outputs NONE) /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    storage_agree_except (step_taint inst s post tn).t_stor
      (contract_storage post) (contract_storage tpost) /\
    storage_agree_except (step_taint inst s post tn).t_trans
      (contract_transient post) (contract_transient tpost) /\
    post.vs_outcomes = tpost.vs_outcomes
Proof
  cheat
QED
