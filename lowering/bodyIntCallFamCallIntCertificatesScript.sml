(* Deferred certificates retain a separate birth state for every argument.
   The quotation abbreviations below introduce no HOL constants. *)
Theory bodyIntCallFamCallIntCertificates
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore list

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

Theorem intcall_deferred_pure_child:
  ^deferred fp ce e vv r b es s /\
  b.cs_next_id <= c.cs_next_id /\ b.cs_next_var <= c.cs_next_var /\
  c.cs_next_id <= d.cs_next_id /\ c.cs_next_var <= d.cs_next_var /\
  supported_pure_expr fp.jc_tops child /\
  eval_expr fp.jc_cx child es = (INL child_r,ee) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child es c d s ee child_r child_vv u /\
  intcall_joint_res fp ce env es c s /\
  intcall_expr_cont fp ce env es c s ee d u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) ==>
  ^deferred fp ce e vv r d ee u
Proof
  BETA_TAC >> strip_tac >>
  drule_all intcall_pure_child_value_certificate >> strip_tac >>
  qexists `a` >> simp[]
QED

Theorem intcall_deferred_list_pure_child:
  ^deferred_list fp ce ds vs rs b es s /\
  b.cs_next_id <= c.cs_next_id /\ b.cs_next_var <= c.cs_next_var /\
  c.cs_next_id <= d.cs_next_id /\ c.cs_next_var <= d.cs_next_var /\
  supported_pure_expr fp.jc_tops child /\
  eval_expr fp.jc_cx child es = (INL child_r,ee) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child es c d s ee child_r child_vv u /\
  intcall_joint_res fp ce env es c s /\
  intcall_expr_cont fp ce env es c s ee d u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s n (OK u) ==>
  ^deferred_list fp ce ds vs rs d ee u
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> first_x_assum drule >> disch_tac >>
  drule_all (BETA_RULE intcall_deferred_pure_child) >>
  disch_then ACCEPT_TAC
QED

Theorem intcall_deferred_list_empty:
  ^deferred_list fp ce [] [] [] b es s
Proof
  simp[]
QED

Theorem intcall_deferred_list_snoc:
  ^deferred_list fp ce ds vs rs b es s /\
  ^deferred fp ce e vv r b es s ==>
  ^deferred_list fp ce (ds ++ [e]) (vs ++ [vv]) (rs ++ [r]) b es s
Proof
  BETA_TAC >> strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on `i < LENGTH ds`
  >- (simp[listTheory.EL_APPEND_EQN] >> gvs[]) >>
  `i = LENGTH ds` by decide_tac >>
  `LENGTH rs = LENGTH vs` by metis_tac[] >>
  simp[listTheory.EL_APPEND_EQN] >> qexists `a` >> gvs[]
QED
