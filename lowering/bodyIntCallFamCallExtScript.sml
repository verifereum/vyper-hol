(* Seam 2 joint induction, a family leaf of the call step: every other call target (external calls and send; the rest are not supported_expr). *)
Theory bodyIntCallFamCallExt
Ancestors
  bodyIntCallJointContract

(* The operand hypotheses carry the internal frame, rather than exprs_case's
   universally quantified contract.  Execute each child with the smaller
   producer hypothesis, then reuse the canonical suffix:

   ExtCall: extrequest_compile_call_split exposes target, snapshot args,
   kwargs, tuple prefix, call and return.  At each raw eval_expr landing,
   intcall_vv_post_intro recovers vv_post and intcall_expr_cont retains the
   resource frame.  The snapshot word/cell-intro, unread, joint-unwrap and
   kwarg-suffix lemmas handle the remaining operand work.  Existing layout,
   gas-selection and protected tuple-prefix lemmas feed extcall_request_ready;
   extcall_call_step and extcall_return_values_owned finish with the real
   protected set.  Send's two or three word operands use the forced-producer
   hypothesis; retain memory, allocation-map and frontier equality across the
   canonical CALL/ASSERT steps when composing send_tail_path.

   intcall_joint_res_frame and intcall_expr_cont_vv_post repackage the final
   certificate.  The global expression root and a copy of its pure induction
   would inherit unrelated aggregate/subscript admission tags. *)
Theorem intcall_extcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt args dflt. e = Call a tgt args dflt /\ !nsid. tgt <> IntCall nsid) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
