(* A non-static shadow of a successful static prefix. Outcome effects are
   masked to the static frame's unchanged world. Requests are compared
   modulo their static bit, since explicit STATICCALL keeps that bit. *)
Theory staticShadowDefs
Ancestors
  venomState venomExecSemantics extCallOracle list

Definition static_shadow_def:
  static_shadow s =
    s with <|
      vs_call_ctx := s.vs_call_ctx with cc_static := F;
      vs_outcomes := MAP (\co. co with <|
        co_accounts := s.vs_accounts; co_tStorage := s.vs_transient;
        co_logs := []; co_toDelete := [] |>) s.vs_outcomes;
      vs_requests := MAP (\rq. rq with cr_static := F) s.vs_requests |>
End

Definition static_shadow_rel_def:
  static_shadow_rel s sh <=>
    sh with vs_requests := MAP (\rq. rq with cr_static := F) sh.vs_requests =
      static_shadow s
End

(* No claim is made about a shadow suffix after a static abort. *)
Definition static_shadow_result_rel_def:
  static_shadow_result_rel r r' <=>
    case r of
      OK s => ?sh. r' = OK sh /\ static_shadow_rel s sh /\
                   s.vs_call_ctx.cc_static
    | IntRet ir s => ?sh. r' = IntRet ir sh /\ static_shadow_rel s sh /\
                         s.vs_call_ctx.cc_static
    | Halt s => ?sh. r' = Halt sh /\ static_shadow_rel s sh /\
                     s.vs_call_ctx.cc_static
    | _ => T
End

Theorem static_shadow_rel_initial:
  static_shadow_rel s (static_shadow s)
Proof
  simp[static_shadow_rel_def, static_shadow_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem static_shadow_rel_update_var:
  static_shadow_rel s sh ==>
  static_shadow_rel (update_var x v s) (update_var x v sh)
Proof
  simp[static_shadow_rel_def, static_shadow_def, update_var_def,
       venom_state_component_equality]
QED

Theorem static_shadow_rel_eval_operand:
  static_shadow_rel s sh ==> eval_operand op sh = eval_operand op s
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, static_shadow_rel_def,
       static_shadow_def, venom_state_component_equality]
QED

Theorem static_shadow_rel_memory:
  static_shadow_rel s sh ==>
  static_shadow_rel (s with vs_memory := m) (sh with vs_memory := m)
Proof
  simp[static_shadow_rel_def, static_shadow_def, venom_state_component_equality]
QED

Theorem static_shadow_rel_eval_operands:
  static_shadow_rel s sh ==> eval_operands ops sh = eval_operands ops s
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  Induct_on `ops` >> simp[eval_operands_def]
QED

Theorem static_shadow_rel_fields:
  static_shadow_rel s sh ==>
  sh.vs_call_ctx = s.vs_call_ctx with cc_static := F /\
  sh.vs_outcomes = (static_shadow s).vs_outcomes /\
  sh.vs_gas_readings = s.vs_gas_readings /\
  sh.vs_accounts = s.vs_accounts /\
  sh.vs_transient = s.vs_transient /\
  sh.vs_logs = s.vs_logs /\
  sh.vs_pending_deletions = s.vs_pending_deletions
Proof
  simp[static_shadow_rel_def, static_shadow_def, venom_state_component_equality]
QED

Theorem static_shadow_rel_normal_form:
  static_shadow_rel s sh <=>
  ?rqs.
    sh = static_shadow s with vs_requests := rqs /\
    MAP (\rq. rq with cr_static := F) rqs =
    MAP (\rq. rq with cr_static := F) s.vs_requests
Proof
  simp[static_shadow_rel_def, static_shadow_def,
       venom_state_component_equality] >> metis_tac[]
QED
