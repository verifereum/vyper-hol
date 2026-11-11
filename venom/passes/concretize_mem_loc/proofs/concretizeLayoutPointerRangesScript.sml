Theory concretizeLayoutPointerRanges
Ancestors concretizeLayoutPositions frameActivationLookup
  frameRelocationRangeGeometry frameRawEndpoints frameRelocationGuardedValues
  frameRelocationLocal frameResolvedTrace frameActivationLifetime
  frameJointTransition o1PassContract unitMemInv venomExecSemantics
  venomWf venomState finite_map words list

Theorem concretize_guarded_pointer_range:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  local_rel (\u. F)
    (guarded_ptr Opaque (activation_lookup (0:num) (concretize_positions C')
      (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  ~Opaque v /\ FLOOKUP rv v = SOME ((token,aid),(b,sz)) /\
  eval_operand (Var v) s = SOME x /\ b <= w2n x /\ w2n x + len <= b+sz ==>
  ?y. eval_operand (Var v) t = SOME y /\
    w2n y = activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (token,aid) + (w2n x-b) /\
    activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (token,aid) <= w2n y /\
    w2n y + len <= activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (token,aid) + sz
Proof
  strip_tac >>
  `?d owner.
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      d owner aid (b,sz) /\
    activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (token,aid) =
      concretize_positions C' owner aid` by
    metis_tac[resolved_activation_lookup] >>
  `b+sz < dimword (:256)` by
    (drule_all joint_activation_cache_strict >> simp[]) >>
  drule_all concretize_positions_activation_numeric >> strip_tac >>
  irule guarded_pointer_range >> simp[] >> metis_tac[]
QED

val _ = if null (hyp concretize_guarded_pointer_range) then ()
        else raise Fail "concretize_guarded_pointer_range has hypotheses";
