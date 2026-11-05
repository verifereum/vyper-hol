(* Counted address/data prefix interfaces. Source list evaluation forces
   every operand; use the existing eval_exprs_cons_action bridge. *)
Theory rawCallOperandPrefixPtr
Ancestors
  rawCallShapePtr typedOperandsPtr rawCallBufferPtr gasContext exprSimWordArgs
  exprSimDefs gasSummaryComposePtr vyperState vyperInterpreter exprSimHash
  ghostPcTransportPtr typedCopyAmbientFramePtr decoderGhostFramePtr

Theorem eval_exprs_head_admissible:
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[eval_exprs_cons_action, bind_def] >> metis_tac[]
QED

Theorem eval_exprs_tail_admissible:
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := marks ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc))
    (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_gas_obs, gas_admissible_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `marks ++ gs` mp_tac) >>
  simp[eval_exprs_cons_action, bind_def] >> metis_tac[]
QED

Theorem raw_call_addr_data_values:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (do r <- eval_expr cx a; read_result cx r od) es = (INL av,es1) /\
  (do r <- eval_expr cx d; read_result cx r od) es1 = (rr,es2) ==>
  expr_sim_inv cenv cx env es1 /\ expr_sim_inv cenv cx env es2 /\
  expr_res_ok rr /\ value_has_type (BaseTV AddressT) av /\
  ?cap. expr_type d = BaseT (BytesT (Dynamic cap)) /\
    (!v. rr = INL v ==> ?bs. v = BytesV bs)
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `expr_body_pre cenv cx env d es1` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_base_result >>
  simp[] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]
QED

Theorem forced_base_marked_facts:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  body_exprs_ptr_ok cx (e::args) /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    marks (INL v) mid (OK t) ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  value_has_type (BaseTV bt) v /\ body_exprs_ptr_ok cx args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc))
    (mid with gas_obs := []) /\ ~t.vs_halted
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `(do r <- eval_expr cx e; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by fs[bind_def] >>
  drule exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >>
  simp[] >> strip_tac >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `body_exprs_ptr_ok cx args` by
    (fs[bodyPtrPredsTheory.body_exprs_ptr_ok_def, bind_def, AllCaseEqs()] >>
     metis_tac[]) >>
  fs[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  drule_all eval_exprs_tail_admissible >>
  simp[gas_admissible_gas_obs] >>
  metis_tac[fragGasPathTheory.gas_path_normal]
QED

Theorem forced_base_outcome_facts:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  body_exprs_ptr_ok cx (e::args) /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q R /\
  (!res ee G tn t. Q res ee G tn t ==> ?v. res = INL v) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\ ee.gas_obs = [] /\
      expr_sim_inv cenv cx env ee /\
      (?v. res = INL v /\ value_has_type (BaseTV bt) v) /\
      body_exprs_ptr_ok cx args /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      gas_admissible (eval_exprs cx args)
        (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) ee /\
      ~t.vs_halted) R
Proof
  strip_tac >> irule operandOutcomePtrTheory.gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?v. res = INL v` by metis_tac[] >> gvs[] >>
  drule_all forced_base_marked_facts >> simp[]
QED

Theorem body_base_operand_outcome_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (e::args) /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv dep cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\
      expr_sim_inv cenv cx env ee /\ value_has_type (BaseTV bt) v /\
      body_exprs_ptr_ok cx args /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      gas_admissible (eval_exprs cx args)
        (\res. case res of INL vs => T | INR exc => expr_res_ok (INR exc)) ee /\
      ~t.vs_halted)
    (\rr ee gt r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_sim_ptr dep ctx PG func cenv cx ty e es` by
    (fs[bodyPtrPredsTheory.body_exprs_ptr_ok_def,
        bodyPtrPredsTheory.body_expr_ptr_ok_def] >> metis_tac[]) >>
  drule eval_exprs_head_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_sim_ptr_def] >>
  disch_then (drule_all_then assume_tac) >>
  drule forced_base_outcome_facts >>
  disch_then (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`bt`, `args`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then assume_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ (\res ee G tn t. ?v. _) _` kall_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  POP_ASSUM_LIST (K all_tac) >> simp[] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_addr_data_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  fn_has_code sa s2 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do av <- bind (eval_expr cx a) (read_result cx);
        dv <- bind (eval_expr cx d) (read_result cx); return (av,dv) od)
    (es,s0,G0,tn0)
    (\rr ee G tn t. ?av bs ea ta.
      rr = INL (av,BytesV bs) /\ value_has_type (BaseTV AddressT) av /\
      ea.gas_obs = [] /\
      expr_post ctx func cenv cx a es sa s1 s0 ea av addr ta /\
      expr_post ctx func cenv cx d ea s1 s2 ta ee (BytesV bs) data t /\
      expr_sim_inv cenv cx env ee /\ body_exprs_ptr_ok cx kws /\
      t.vs_current_bb = s2.cs_current_bb /\
      t.vs_inst_idx = LENGTH s2.cs_current_insts /\ ~t.vs_halted /\
      ghost_inv dep cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type d) (BytesV bs) data G tn t /\
      ptr_buf_ok cenv d data G t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\rr ee gt r. ?exc. rr = INR exc /\ expr_exit (INR exc : value + exception) r)
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `expr_sim_inv cenv cx env es` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all body_base_operand_outcome_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "tail_cert"
  >- suspend "head_cert"
  >> suspend "head_bind"
QED

Resume raw_call_addr_data_sim_ptr[head_bind]:
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  conj_tac >- suspend "data" >>
  simp[exprSimDefsTheory.expr_exit_def] >> rpt strip_tac >>
  Cases_on `res` >> gvs[]
QED

Resume raw_call_addr_data_sim_ptr[head_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[operandOutcomePtrTheory.ignore_map_return] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
  goal_assum (drule_at Any)
QED

Resume raw_call_addr_data_sim_ptr[tail_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[operandOutcomePtrTheory.ignore_map_return] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED

Resume raw_call_addr_data_sim_ptr[data]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `stmt_state_rel ctx func cenv cx ee t` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `local_ptrs_reserved cenv s1` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `expr_body_pre cenv cx env d ee` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  qpat_x_assum `body_exprs_ptr_ok cx (a::d::kws)` kall_tac >>
  drule_all body_base_operand_outcome_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule operandOutcomePtrTheory.gas_outcome_ptr_map_return >>
  goal_assum (drule_at Any) >> conj_tac
  >- suspend "posts" >>
  simp[exprSimDefsTheory.expr_exit_def] >> rpt strip_tac >> Cases_on `res` >> gvs[]
QED

Resume raw_call_addr_data_sim_ptr[posts]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
     >- (qexists_tac `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     irule exprSimWordArgsTheory.expr_post_frame >> goal_assum (drule_at Any)) >>
  qpat_x_assum `value_has_type (BaseTV (BytesT _)) _` mp_tac >>
  Cases_on `v'` >> simp[vyperTypingTheory.value_has_type_def] >>
  strip_tac >> gvs[] >> qexistsl_tac [`ee`, `t`] >>
  simp[compileEnvTheory.is_word_type_def]
QED

Finalise raw_call_addr_data_sim_ptr

(* Header reads need live-byte cleanliness independently of site coverage. *)
Theorem raw_call_data_header_read_ready:
  ptr_mem_ok cx ty (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  op_taint tn op = {} /\ eval_operand op s = SOME w ==>
  ?x base sz. op = Var x /\ FLOOKUP G x = SOME (base,sz) /\
    base <= w2n w /\ w2n w + 32 + LENGTH bs <= base + sz /\
    ptr_covers G tn x s 32 /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
    (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==>
      i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all ptr_mem_ok_dynamic_bytes_site >> strip_tac >>
  drule_all ptr_mem_ok_dynamic_bytes_clean >> strip_tac >>
  gvs[] >> simp[bodyPtrDefsTheory.ptr_covers_def] >>
  qexists_tac `w` >> fs[venomStateTheory.eval_operand_def] >> decide_tac
QED

Theorem raw_call_mload_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n w) s) s) tn)
    (OK ((update_var out (mload (w2n w) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n w) s) s)` by
    (PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
     simp[venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
       venomStateTheory.eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id MLOAD [Var src] [out]) s` by
    (irule typedCopyPtrTheory.ptr_inst_ok_mload >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
     (step_prov PG G (mk_inst id MLOAD [Var src] [out])
       (update_var out (mload (w2n w) s) s))
     (step_taint (mk_inst id MLOAD [Var src] [out]) s
       (update_var out (mload (w2n w) s) s) tn)
     (OK ((update_var out (mload (w2n w) s) s) with
       vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MLOAD [Var src] [out]`,
       `fn` |-> `func`, `lo` |-> `0`,
       `u` |-> `update_var out (mload (w2n (w:256 word)) s) s`]
       fragGasSeqPtrTheory.straight_line_ptr_edge) >>
     gvs[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[venomStateTheory.update_var_def]
QED

Theorem raw_call_add_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id ADD [left;right] [out])
      (update_var out (a+b) s))
    (step_taint (mk_inst id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn)
    (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s =
     OK (update_var out (a+b) s)` by
    (PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
     simp[venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id ADD [left;right] [out]) s` by
    (irule typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
     (step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out (a+b) s))
     (step_taint (mk_inst id ADD [left;right] [out]) s (update_var out (a+b) s) tn)
     (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id ADD [left;right] [out]`,
       `fn` |-> `func`, `lo` |-> `0`,
       `u` |-> `update_var out ((a:256 word)+(b:256 word)) s`]
       fragGasSeqPtrTheory.straight_line_ptr_edge) >>
     gvs[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[venomStateTheory.update_var_def]
QED

(* A read-only header instruction changes only fresh registers. *)
Theorem raw_call_header_ghost_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
  un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv dep cenv cx es H un t /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >> conj_tac
  >- (fs[bodyPtrDefsTheory.ghost_inv_def,
         bodyPtrDefsTheory.return_buf_ptr_def,
         bodyPtrDefsTheory.stor_taint_ok_def,
         compileEnvTheory.local_ptrs_reserved_def] >>
      rpt conj_tac >> rpt strip_tac
      >- (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[])
      >- metis_tac[]
      >- (Cases_on `dep` >>
          fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
          PairCases_on `x` >>
          fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
          `not_fresh_at sa x` by metis_tac[] >>
          first_x_assum drule >> strip_tac >>
          fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[])
      >> metis_tac[]) >>
  simp[bodyPtrDefsTheory.ghost_kept_def]
QED

Theorem raw_call_data_prefix_frame:
  emit_op MLOAD [ptr_op] sa = (len_op,sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data_op,sm) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b < dimword (:256) /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
    eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
    eval_operand data_op t = SOME (n2w (b+32)) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> drule_all hash_data_prefix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t` >> simp[loweringPostsTheory.wb_frame_def,
    loweringPostsTheory.locals_kept_def] >> first_assum ACCEPT_TAC
QED

Theorem raw_call_emit_mload_path_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n w) s) s) tn)
    (OK ((update_var out (mload (w2n w) s) s) with
      vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]]` by
    (gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_mload_path_ptr >> simp[]
QED

Theorem raw_call_emit_add_path_ptr:
  emit_op ADD [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [out])
      (update_var out (a+b) s))
    (step_taint (mk_inst sa.cs_next_id ADD [left;right] [out]) s
      (update_var out (a+b) s) tn)
    (OK ((update_var out (a+b) s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [left;right] [out]]` by
    (gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ADD [left;right] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_add_path_ptr >> simp[]
QED

(* Saved word operands need the later stage's entry frontier, not the
   frontier before the operand was produced. *)
Theorem saved_word_operand_ptr_frame:
  wb_frame cenv es sa s t /\ ghost_kept cenv es sa G tn s H un /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  is_word_type ty /\ expr_val_rel cx ty v op s /\ op_taint tn op = {} ==>
  expr_val_rel cx ty v op t /\ op_taint un op = {}
Proof
  strip_tac >> conj_tac
  >- (fs[loweringPostsTheory.expr_val_rel_def] >>
      qexists_tac `w` >> conj_tac >- (
      irule exprBopSimPropsTheory.eval_operand_frame >>
      goal_assum (drule_at Any) >>
      fs[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >> gvs[]) >>
  Cases_on `op` >>
  gvs[ptrDisciplineTheory.op_taint_def, bodyPtrDefsTheory.ghost_kept_def] >>
  metis_tac[]
QED

Theorem raw_call_header_fresh_step_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out /\ (opc = MLOAD \/ opc = ADD) /\
  H = step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) /\
  un = step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn ==>
  ghost_inv dep cenv cx es H un (update_var out w s) /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >> (irule raw_call_header_ghost_frame >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      gvs[] >>
      simp[decoderGhostFramePtrTheory.step_prov_other_output,
        decoderGhostFramePtrTheory.step_taint_other_output,
        venomInstTheory.mk_inst_def, venomStateTheory.update_var_def,
        venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.adopt_reset_def,
    ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def,
    ptrDisciplineTheory.range_bytes_def, venomStateTheory.update_var_def,
    venomInstTheory.mk_inst_def,
    codegenRelTheory.source_memory_write_ranges_def,
    finite_mapTheory.FLOOKUP_DEF] >>
  rpt (CASE_TAC >> gvs[]) >> simp[SF CONJ_ss])
QED
