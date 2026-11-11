(* The normal counted child extends the deferred prefix, not its reads. *)
Theory bodyIntCallFamCallIntTraversePost
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore
  bodyIntCallFamCallIntCertificates bodyIntCallFamCallIntCertificateIntro
  bodyIntCallFamCallIntTraverseInterfaces vyperEvalExprPreservesScopesDom

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

Theorem intcall_deferred_prefix_step:
  ^deferred_list fp ce ds vs rs b ee t /\
  ^deferred fp ce child child_vv child_r d ef u /\
  intcall_joint_res fp ce env es a s /\
  intcall_expr_cont fp ce env es a s ee b t /\
  intcall_expr_cont fp ce env ee b t ef d u /\
  a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  b.cs_next_id <= d.cs_next_id /\ b.cs_next_var <= d.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  supported_pure_expr fp.jc_tops child /\
  eval_expr fp.jc_cx child ee = (INL child_r,ef) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child ee b d t ef child_r child_vv u /\
  gas_marked_path F fp.jc_ctx fp.jc_func t n (OK u) ==>
  ^deferred_list fp ce (ds ++ [child]) (vs ++ [child_vv]) (rs ++ [child_r]) d ef u /\
  intcall_expr_cont fp ce env es a s ef d u /\
  MAP FDOM es.scopes = MAP FDOM ef.scopes
Proof
  BETA_TAC >> strip_tac >>
  `intcall_joint_res fp ce env ee b t` by
    fs[intcall_expr_cont_def] >>
  `b.cs_next_id <= b.cs_next_id /\ b.cs_next_var <= b.cs_next_var` by simp[] >>
  drule_all (BETA_RULE intcall_deferred_list_pure_child) >> disch_tac >>
  conj_tac
  >- (match_mp_tac (BETA_RULE intcall_deferred_list_snoc) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rename1 `vv_at ce fp.jc_cx (post_value_type ce child) birth d ef child_r child_vv u` >>
      qexists_tac `birth` >> asm_rewrite_tac[]) >>
  conj_tac
  >- (drule_all intcall_expr_cont_trans >> disch_then ACCEPT_TAC) >>
  drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
  simp[]
QED
