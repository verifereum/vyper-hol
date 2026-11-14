(* Successful static prefixes have non-static shadows. Nothing requires
   the shadow to terminate after the first static fault. *)
Theory staticShadowRun
Ancestors
  staticShadowBase staticShadowFrame staticShadowPrim staticShadowDefs
  venomExecSemantics venomCallOracleDefs extCallOracle
  venomState venomInst list finite_map

Theorem static_shadow_runs:
  (!fuel C inst s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (step_inst fuel C inst s)
                             (step_inst fuel C inst sh)) /\
  (!fuel C bb s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (exec_block fuel C bb s)
                             (exec_block fuel C bb sh)) /\
  (!fuel C fn s sh.
    s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
    static_shadow_result_rel (run_blocks fuel C fn s)
                             (run_blocks fuel C fn sh))
Proof
  simp[]
QED
