(* Introduction and gas-observation stability of deferred certificates. *)
Theory bodyIntCallFamCallIntCertificateIntro
Ancestors
  bodyIntCallJointContract bodyIntCallFamCallIntCertificates exprSimSubscriptArrayCompose exprSimWordArgs
  supportedExprTraverse

val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size))``;

val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

Theorem intcall_deferred_list_gas_obs:
  ^deferred_list fp ce ds vs rs b (es with gas_obs := gs) s <=>
  ^deferred_list fp ce ds vs rs b es s
Proof
  simp[vv_at_source_gas, vv_holds_source_gas, vv_own_source_gas]
QED

Theorem intcall_joint_res_gas_obs:
  intcall_joint_res fp ce env (es with gas_obs := gs) b s <=>
  intcall_joint_res fp ce env es b s
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def,
       compileEnvTheory.local_region_def]
QED

Theorem intcall_deferred_intro:
  supported_pure_expr fp.jc_tops e /\
  (?r. res = INL r /\
    vv_holds ce fp.jc_cx (post_value_type ce e) r vv ee u /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b ee r vv u /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b ee r vv u) /\
    (~expr_has_effect e ==> vv_storage_live fp.jc_cx vv ee u) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) u = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size)) /\
    intcall_expr_cont fp ce env es a s ee b u) ==>
  ?r. res = INL r /\ ^deferred fp ce e vv r b ee u /\
    intcall_expr_cont fp ce env es a s ee b u
Proof
  BETA_TAC >> strip_tac >>
  drule supported_pure_expr_effect_free >> strip_tac >>
  qexists `r` >> conj_tac >- simp[] >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  qexists `a` >> simp[]
QED
