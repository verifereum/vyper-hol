Theory bodyIntCallStageCutsMods
Ancestors
  intCallStep exprSimSend fragExec externalEntryShape loweringHalt
  gasShadowCompile gasShadowCompileCallSupport gasShadowCompileHelpers
  gasShadowCompileContext gasShadowCompileEmit gasShadowState bodyFullShared
  venomInst venomExecSemantics emitHelper exprLowering compileEnv
  gasShadow gasShadowCompileBase

Theorem intcall_fresh_outputs_code[local]:
  !n st names out. fresh_vars n st = (names,out) ==>
    out.cs_current_bb = st.cs_current_bb /\
    out.cs_current_insts = st.cs_current_insts
Proof
  Induct >>
  simp[fresh_vars_def, comp_return_def, comp_bind_def, fresh_var_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem intcall_emit_instruction[local]:
  ((?u. emit_void INVOKE (Label lbl :: ops) st = (u,emitted)) \/
   (?n outs. emit_multi_op INVOKE (Label lbl :: ops) n st = (outs,emitted))) ==>
  ?inst. emitted.cs_current_bb = st.cs_current_bb /\
    emitted.cs_current_insts = st.cs_current_insts ++ [inst] /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)
Proof
  strip_tac
  >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
           comp_return_def, mk_inst_def, decode_invoke_def] >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `emit_multi_op _ _ _ _ = _` mp_tac >>
  simp[emit_multi_op_def, comp_bind_def] >>
  Cases_on `fresh_vars n st` >> simp[] >>
  drule intcall_fresh_outputs_code >> strip_tac >>
  simp[emit_inst_def, comp_ignore_bind_def, comp_bind_def,
       fresh_id_def, emit_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[mk_inst_def, decode_invoke_def]
QED

Theorem intcall_emit_cursor[local]:
  fn_has_code st emitted fn /\
  ((?u. emit_void INVOKE (Label lbl :: ops) st = (u,emitted)) \/
   (?n outs. emit_multi_op INVOKE (Label lbl :: ops) n st = (outs,emitted))) ==>
  ?bb inst.
    lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH st.cs_current_insts) = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops)
Proof
  rewrite_tac[GSYM AND_IMP_INTRO] >> disch_tac >>
  disch_then (strip_assume_tac o MATCH_MP intcall_emit_instruction) >>
  drule_all fn_has_code_same_block >> simp[] >> metis_tac[]
QED

Theorem intcall_expr_shadow[local]:
  gas_shadow_compiles (compile_expr ce ty e)
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))
Proof
  qspecl_then [`ce`,`ty`,`e`,`T`] mp_tac
    (CONJUNCT1 (Q.INST [`sd` |-> `T`] gas_shadow_compile_expr_env)) >>
  SIMP_TAC std_ss []
QED

Theorem intcall_stage_shadow[local]:
  gas_shadow_compiles
    (compile_stage_intcall_args compile_expr ce es flags tys)
    (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
       (MAP gas_shadow_expr es) flags tys)
Proof
  irule (SIMP_RULE std_ss []
    (Q.INST [`sh` |-> `T`] gas_shadow_compiles_stage_intcall_args_env)) >>
  simp[gas_shadow_compile_expr_env]
QED

Theorem intcall_stage_extends[local]:
  compile_stage_intcall_args compile_expr ce es flags tys s = (ops,t) ==>
  cs_extends s t
Proof
  strip_tac >>
  qspecl_then [`compile_expr`,`ce`,`es`,`flags`,`tys`,`s`] mp_tac
    compile_stage_intcall_args_labels >>
  simp[compile_expr_labels]
QED

Theorem intcall_emit_void_extends[local]:
  emit_void INVOKE ops s = (u,t) ==> cs_extends s t
Proof
  strip_tac >>
  qspecl_then [`INVOKE`,`ops`,`s`,`K T`] mp_tac emit_void_labels >> simp[]
QED

Theorem intcall_emit_multi_extends[local]:
  emit_multi_op INVOKE ops n s = (vs,t) ==> cs_extends s t
Proof
  strip_tac >>
  qspecl_then [`INVOKE`,`ops`,`n`,`s`,`K T`] mp_tac emit_multi_op_labels >> simp[]
QED

Theorem intcall_results_extends[local]:
  store_multi_results buf vs 0 s = (u,t) ==> cs_extends s t
Proof
  strip_tac >>
  qspecl_then [`buf`,`vs`,`0`,`s`,`K T`] mp_tac store_multi_results_labels >> simp[]
QED

Theorem intcall_code_intervals[local]:
  cs_extends a b /\ cs_extends b c /\ cs_extends c d /\
  cs_extends d e /\ cs_extends e z /\ fn_has_code a z fn ==>
  fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn /\
  fn_has_code d e fn /\ fn_has_code e z fn
Proof
  strip_tac >>
  `cs_extends c z` by metis_tac[cs_extends_trans] >>
  `cs_extends b z` by metis_tac[cs_extends_trans] >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  `cs_extends a d` by metis_tac[cs_extends_trans] >>
  `cs_extends a e` by metis_tac[cs_extends_trans] >>
  `cs_extends d z` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_mid,cs_extends_refl]
QED

Theorem intcall_code_intervals_no_buffer[local]:
  cs_extends a c /\ cs_extends c d /\ cs_extends d z /\ fn_has_code a z fn ==>
  fn_has_code a a fn /\ fn_has_code a c fn /\ fn_has_code c d fn /\
  fn_has_code d z fn /\ fn_has_code z z fn
Proof
  strip_tac >> irule intcall_code_intervals >> simp[cs_extends_refl]
QED

Theorem intcall_alloc_pair[local]:
  gas_shadow_state a sa /\ compile_alloc_buffer n a = (buf,b) /\
  compile_alloc_buffer n sa = (sbuf,sb) ==>
  sbuf = buf /\ gas_shadow_state b sb /\ cs_extends a b /\ cs_extends sa sb
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_alloc_buffer n) (compile_alloc_buffer n)` by
    simp[gas_shadow_compiles_alloc_buffer] >>
  drule_all gas_shadow_step >> simp[] >>
  metis_tac[compile_alloc_buffer_extends]
QED

Theorem intcall_stage_pair[local]:
  gas_shadow_state a sa /\
  compile_stage_intcall_args compile_expr ce es flags tys a = (ops,b) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr es) flags tys sa = (sops,sb) ==>
  sops = ops /\ gas_shadow_state b sb /\ cs_extends a b /\ cs_extends sa sb
Proof
  strip_tac >>
  `gas_shadow_compiles
     (compile_stage_intcall_args compile_expr ce es flags tys)
     (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
        (MAP gas_shadow_expr es) flags tys)` by simp[intcall_stage_shadow] >>
  drule_all gas_shadow_step >> simp[] >> metis_tac[intcall_stage_extends]
QED

Theorem intcall_emit_multi_pair[local]:
  gas_shadow_state a sa /\ emit_multi_op INVOKE ops n a = (vs,b) /\
  emit_multi_op INVOKE ops n sa = (svs,sb) ==>
  svs = vs /\ gas_shadow_state b sb /\ cs_extends a b /\ cs_extends sa sb
Proof
  strip_tac >>
  `gas_shadow_compiles (emit_multi_op INVOKE ops n) (emit_multi_op INVOKE ops n)` by
    simp[gas_shadow_compiles_emit_multi_op] >>
  drule_all gas_shadow_step >> simp[] >> metis_tac[intcall_emit_multi_extends]
QED

Theorem intcall_emit_void_pair[local]:
  gas_shadow_state a sa /\ emit_void INVOKE ops a = (u,b) /\
  emit_void INVOKE ops sa = (su,sb) ==>
  gas_shadow_state b sb /\ cs_extends a b /\ cs_extends sa sb
Proof
  strip_tac >>
  `gas_shadow_compiles (emit_void INVOKE ops) (emit_void INVOKE ops)` by
    simp[gas_shadow_compiles_emit_void] >>
  drule_all gas_shadow_step >> simp[] >> metis_tac[intcall_emit_void_extends]
QED

(* Code cuts only: the final implication identifies the instruction if the
   execution cursor is there, not that any execution reaches the cursor. *)
Theorem paired_intcall_stage_cuts_mods:
  let key = nsid_to_string (src,name) in
  let ds = omitted_defaults ce key (LENGTH es) in
  let tys = TAKE (LENGTH es + LENGTH ds) (ce.ce_func_param_types key) in
  let lbl = internal_fn_label (ce.ce_func_ids key) key
              (ce.ce_func_param_types key) ce.ce_is_ctor in
  let call = Call ann (IntCall (src,name)) es fallback in
  compile_expr ce ty call sa = (v,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr call) sha = (sv,shb) /\
  ce.ce_func_info key = (ret_count,rbs,flags) /\ gas_shadow_state sa sha /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  ?s2 s2a s3 sh2 sh2a sh3 sup_ops dflt_ops.
    compile_stage_intcall_args compile_expr ce es flags tys s2 = (sup_ops,s2a) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr es) flags tys sh2 = (sup_ops,sh2a) /\
    compile_stage_intcall_args compile_expr (cenv_without_defaults ce key)
      ds (DROP (LENGTH es) flags) (DROP (LENGTH es) tys) s2a = (dflt_ops,s3) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T (cenv_without_defaults ce key))
      (MAP gas_shadow_expr ds) (DROP (LENGTH es) flags)
      (DROP (LENGTH es) tys) sh2a = (dflt_ops,sh3) /\
    gas_shadow_state s2 sh2 /\ gas_shadow_state s2a sh2a /\
    gas_shadow_state s3 sh3 /\ gas_shadow_state sb shb /\ sv = v /\
    ?s4 sh4 arg_ops.
    gas_shadow_state s4 sh4 /\
    fn_has_code sa s2 fn /\ fn_has_code s2 s2a fn /\ fn_has_code s2a s3 fn /\
    fn_has_code s3 s4 fn /\ fn_has_code s4 sb fn /\
    fn_has_code sha sh2 shfn /\ fn_has_code sh2 sh2a shfn /\
    fn_has_code sh2a sh3 shfn /\ fn_has_code sh3 sh4 shfn /\ fn_has_code sh4 shb shfn /\
    (0 < ret_count ==>
     ?rbuf results u shu.
       compile_alloc_buffer (32 * ret_count) sa = (rbuf,s2) /\
       compile_alloc_buffer (32 * ret_count) sha = (rbuf,sh2) /\
       arg_ops = sup_ops ++ dflt_ops /\
       emit_multi_op INVOKE (Label lbl :: arg_ops) ret_count s3 = (results,s4) /\
       emit_multi_op INVOKE (Label lbl :: arg_ops) ret_count sh3 = (results,sh4) /\
       store_multi_results rbuf.buf_operand results 0 s4 = (u,sb) /\
       store_multi_results rbuf.buf_operand results 0 sh4 = (shu,shb) /\
       v = LocatedValue (ce.ce_func_return_type key) (base_ptr rbuf)) /\
    (ret_count = 0 /\ 0 < rbs ==>
     ?rbuf u shu.
       compile_alloc_buffer rbs sa = (rbuf,s2) /\
       compile_alloc_buffer rbs sha = (rbuf,sh2) /\
       arg_ops = rbuf.buf_operand :: (sup_ops ++ dflt_ops) /\
       emit_void INVOKE (Label lbl :: arg_ops) s3 = (u,s4) /\
       emit_void INVOKE (Label lbl :: arg_ops) sh3 = (shu,sh4) /\
       s4 = sb /\ sh4 = shb /\
       v = LocatedValue (ce.ce_func_return_type key) (base_ptr rbuf)) /\
    (ret_count = 0 /\ rbs = 0 ==>
     ?u shu.
       s2 = sa /\ sh2 = sha /\ arg_ops = sup_ops ++ dflt_ops /\
       emit_void INVOKE (Label lbl :: arg_ops) s3 = (u,s4) /\
       emit_void INVOKE (Label lbl :: arg_ops) sh3 = (shu,sh4) /\
       s4 = sb /\ sh4 = shb /\
       v = StackValue (ce.ce_func_return_type key) (Lit 0w)) /\
    (!t. t.vs_current_bb = s3.cs_current_bb /\
      t.vs_inst_idx = LENGTH s3.cs_current_insts ==>
      ?bb inst. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst /\
        inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,arg_ops))
Proof
  SIMP_TAC std_ss [LET_THM] >> strip_tac >>
  qpat_assum `compile_expr ce _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_expr_call]) >>
  disch_then (mp_then Any mp_tac compile_call_intcall_shape) >>
  simp[SimpLHS] >>
  disch_then (qx_choosel_then [`ast`,`aops`,`ast'`,`dops`,`cst`] strip_assume_tac) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (mp_tac o REWRITE_RULE [gas_shadow_expr_def,compile_expr_call]) >>
  disch_then (mp_then Any mp_tac compile_call_intcall_shape) >>
  simp[SimpLHS,gas_shadow_env_omitted_defaults,gas_shadow_env_without_defaults] >>
  disch_then (qx_choosel_then [`bst`,`shops`,`bst'`,`shdops`,`dst`] strip_assume_tac) >>
  `sv = v /\ gas_shadow_state sb shb` by
    (`gas_shadow_compiles (compile_expr ce ty (Call ann (IntCall (src,name)) es fallback))
       (compile_expr (gas_shadow_env T ce) ty
          (gas_shadow_expr (Call ann (IntCall (src,name)) es fallback)))` by
       simp[intcall_expr_shadow] >>
     drule_all gas_shadow_step >> simp[]) >>
  `gas_shadow_state ast bst /\ cs_extends sa ast /\ cs_extends sha bst` by
    (Cases_on `0 < ret_count`
     >- (fs[] >> drule_all intcall_alloc_pair >> simp[]) >>
     `ret_count = 0` by decide_tac >> Cases_on `0 < rbs`
     >- (fs[] >> drule_all intcall_alloc_pair >> simp[]) >>
     `rbs = 0` by decide_tac >> fs[cs_extends_refl]) >>
  qpat_assum `compile_stage_intcall_args _ ce es _ _ ast = _`
    (mp_then Any (drule_all_then strip_assume_tac) intcall_stage_pair) >>
  qpat_assum `compile_stage_intcall_args _ (cenv_without_defaults ce _) _ _ _ ast' = _`
    (mp_then Any (drule_all_then strip_assume_tac) intcall_stage_pair) >>
  gvs[] >>
  qexistsl_tac [`ast`,`ast'`,`cst`,`bst`,`bst'`,`dst`,`aops`,`dops`] >>
  simp[] >> Cases_on `0 < ret_count`
  >- (fs[] >> drule_all intcall_alloc_pair >> strip_tac >> fs[] >>
      qmatch_asmsub_rename_tac `emit_multi_op INVOKE _ _ cst = (outs,est)` >>
      qmatch_asmsub_rename_tac `emit_multi_op INVOKE _ _ dst = (shouts,fst')` >>
      drule_all intcall_emit_multi_pair >> strip_tac >> fs[] >>
      imp_res_tac intcall_results_extends >>
      qpat_assum `fn_has_code sa sb fn`
        (mp_then Any (drule_all_then strip_assume_tac) intcall_code_intervals) >>
      qpat_assum `fn_has_code sha shb shfn`
        (mp_then Any (drule_all_then strip_assume_tac) intcall_code_intervals) >>
      qexistsl_tac [`est`,`fst'`,`aops ++ dops`] >>
      simp[] >> rpt strip_tac >> irule intcall_emit_cursor >>
      qexists_tac `est` >> simp[] >> disj2_tac >>
      qexistsl_tac [`ret_count`,`outs`] >> simp[]) >>
  `ret_count = 0` by decide_tac >> Cases_on `0 < rbs`
  >- (fs[] >> drule_all intcall_alloc_pair >> strip_tac >> fs[] >>
      drule_all intcall_emit_void_pair >> strip_tac >>
      `cs_extends sb sb /\ cs_extends shb shb` by simp[cs_extends_refl] >>
      qpat_assum `fn_has_code sa sb fn`
        (mp_then Any (drule_all_then strip_assume_tac) intcall_code_intervals) >>
      qpat_assum `fn_has_code sha shb shfn`
        (mp_then Any (drule_all_then strip_assume_tac) intcall_code_intervals) >>
      simp[] >> rpt strip_tac >> irule intcall_emit_cursor >>
      qexists_tac `sb` >> simp[]) >>
  `rbs = 0` by decide_tac >> gvs[] >>
  drule_all intcall_emit_void_pair >> strip_tac >>
  qpat_assum `fn_has_code ast sb fn`
    (mp_then Any (drule_all_then strip_assume_tac) intcall_code_intervals_no_buffer) >>
  qpat_assum `fn_has_code bst shb shfn`
    (mp_then Any (drule_all_then strip_assume_tac) intcall_code_intervals_no_buffer) >>
  simp[] >> rpt strip_tac >> irule intcall_emit_cursor >>
  qexists_tac `sb` >> simp[]
QED
