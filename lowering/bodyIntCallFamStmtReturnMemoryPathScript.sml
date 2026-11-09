(* Attach the terminal RET without losing the memory-copy frame. *)
Theory bodyIntCallFamStmtReturnMemoryPath
Ancestors
  bodyIntCallFamStmtReturnMemoryExit bodyIntCallSharpReturn
  bodyIntCallJointContract placeMemoryCopyEffect exprSimStorageCopy
  compileEnv loweringPosts venomState venomExecSemantics

Theorem intcall_copy_return_exit:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  typed_copy_effect fp.jc_ctx fp.jc_func sa sm s t (w2n bw) cap /\
  val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory /\
  emit_inst RET [fp.jc_rpc] [] sm = ((),sb) /\
  fn_has_code sm sb fp.jc_func ==>
  gas_path fp.jc_ctx fp.jc_func s 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
  intcall_stmt_exit fp (INR (ReturnException v)) es
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >>
  `(!x. fp.jc_rpc = Var x ==> not_fresh_at sa x) /\
   (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x) /\
   (?pc. eval_operand fp.jc_rpc s = SOME pc) /\
   (!b sz. fp.jc_prot b sz ==> regions_disjoint b sz (w2n bw) cap)` by
    (fs[intcall_joint_res_def, intcall_frame_ok_def] >> metis_tac[]) >>
  drule (Q.INST [`P` |-> `fp.jc_prot`, `reserved` |-> `fp.jc_reserved`]
    (SPEC_ALL typed_copy_effect_ret_path)) >>
  disch_then (qspecl_then [`sb`, `fp.jc_rpc`, `fp`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  irule intcall_memory_exit_frame >> simp[] >>
  qexistsl_tac [`ce`, `env`, `s`, `sa`] >> simp[] >>
  fs[typed_copy_effect_def, exprSimStorageCopyTheory.copy_static_def,
     venom_state_component_equality, arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. a + len <= _ \/ _ ==> _` irule >> decide_tac) >>
  gvs[]
QED
