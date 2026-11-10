(* Read-only word forcing, with all old operands preserved at one endpoint. *)
Theory bodyIntCallFamCallIntWordStage
Ancestors
  bodyIntCallFamCallIntStageAllocation bodyIntCallFamCallIntStageInterface
  bodyIntCallJointCallCore bodyIntCallWindowStorage exprOperandVar
  exprLoweringProps

Theorem intcall_word_forcing_readonly:
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce cx ty (Value v) vv es s /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. (!x. q = Var x ==> not_fresh_at sa x) ==>
      eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name b sz. local_region ce scopes u name b sz <=>
                 local_region ce scopes s name b sz) /\
    locals_kept ce es s u /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (drule compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def] >>
      qexists_tac `s` >>
      simp[fragGasModeTheory.gas_marked_path_def,
           loweringPostsTheory.locals_kept_def] >>
      conj_tac >- metis_tac[fragGasPathTheory.gas_path_rules] >>
      gvs[loweringPostsTheory.vv_holds_def, vyperStateTheory.read_result_def,
          vyperStateTheory.return_def]) >>
  rename1 `LocatedValue ann p` >>
  mp_tac (Q.INST [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sa x`,
    `stv` |-> `tv`]
    (SPEC_ALL protected_word_value_frame_forcing)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  qexists_tac `u` >> gvs[]
QED

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

Theorem intcall_completed_append:
  ^completed_prefix cx start current tys flags values ops s /\
  ^completed_prefix cx start current tys' flags' values' ops' s ==>
  ^completed_prefix cx start current (tys ++ tys') (flags ++ flags')
    (values ++ values') (ops ++ ops') s
Proof
  BETA_TAC >> strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on `i < LENGTH tys` >> simp[listTheory.EL_APPEND_EQN] >>
  gvs[]
QED

(* A read-only target endpoint preserves the caller resource certificate.
   This boundary also retains every old memory window, not only allocas. *)
Theorem intcall_readonly_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!q. (!x. q = Var x ==> not_fresh_at sa x) ==>
    eval_operand q u = eval_operand q s) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
               local_region ce es.scopes s name b sz) /\
  locals_kept ce es s u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sb u` by
    (irule intcall_joint_res_frame >> simp[] >>
     conj_tac
     >- (gvs[bodyIntCallJointContractTheory.intcall_expr_res_def,
            intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
     conj_tac >- fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     qexistsl_tac [`es`, `s`, `sa`] >> simp[] >>
     fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  simp[bodyIntCallJointContractTheory.intcall_expr_cont_def]
QED

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
          ?lb size. fp.jc_staged lb size /\ lb <= off /\
                      off + len <= lb + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

(* The true-flag staging operation is exactly unwrap_value.  Source
   evaluation is already finished; all certificates refer to fixed es. *)
Theorem intcall_word_stage_endpoint:
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce fp.jc_cx ty (Value v) vv es s /\ is_word_type ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  fn_has_code sa sb fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  ^completed_prefix fp.jc_cx start sa tys flags values ops s /\
  ^deferred_list fp ce ds vs rs sa es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    ^completed_prefix fp.jc_cx start sb (tys ++ [ty]) (flags ++ [T])
      (values ++ [v]) (ops ++ [op]) u /\
    ^deferred_list fp ce ds vs rs sb es u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sa`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  drule_all intcall_word_forcing_readonly >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (irule intcall_readonly_cont >> simp[]) >>
  `^completed_prefix fp.jc_cx start sb tys flags values ops u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_memory_identity) >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> gvs[]) >>
  `^deferred_list fp ce ds vs rs sb es u` by
    (BETA_TAC >> irule (BETA_RULE intcall_deferred_memory_identity) >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> gvs[]) >>
  `^completed_prefix fp.jc_cx start sb [ty] [T] [v] [op] u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_stack_singleton) >>
     fs[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  `^completed_prefix fp.jc_cx start sb (tys ++ [ty]) (flags ++ [T])
     (values ++ [v]) (ops ++ [op]) u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_append) >>
     gvs[]) >>
  qexists_tac `u` >> gvs[]
QED
