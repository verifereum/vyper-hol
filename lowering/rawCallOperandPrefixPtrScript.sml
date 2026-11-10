(* Counted address/data prefix interfaces. Source list evaluation forces
   every operand; use the existing eval_exprs_cons_action bridge. *)
Theory rawCallOperandPrefixPtr
Ancestors
  rawCallShapePtr typedOperandsPtr rawCallBufferPtr gasContext exprSimWordArgs
  exprSimDefs gasSummaryComposePtr vyperState vyperInterpreter exprSimHash
  ghostPcTransportPtr typedCopyAmbientFramePtr decoderGhostFramePtr exprOperandVar
  rawCallHeaderFramePtr rawCallDataHeaderPtr stmtSimLogArgs

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
  post_value_type cenv e = expr_type e /\
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
  qpat_x_assum `post_value_type cenv e = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
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
  `post_value_type cenv a = expr_type a` by
    (irule loweringPostsTheory.post_value_type_word >>
     fs[compileEnvTheory.is_word_type_def]) >>
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
  `post_value_type cenv d = expr_type d` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     fs[compileEnvTheory.is_bytestring_type_def]) >>
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
         fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
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


(* The header is inside the data continuation: the address-stage ghost must
   remain available until the saved address has been transported. *)
Theorem raw_call_addr_data_header_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\
  emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx [a;d])
    (es,s0,G0,tn0)
    (\rr ee G tn t. ?av bs ea ta tb b x base sz.
      rr = INL [av;BytesV bs] /\ value_has_type (BaseTV AddressT) av /\
      ea.gas_obs = [] /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      expr_post ctx func cenv cx a es sa s1 s0 ea av addr ta /\
      expr_post ctx func cenv cx d ea s1 s2 ta ee (BytesV bs) data tb /\
      wb_frame cenv ee s2 tb t /\
      expr_val_at cenv cx (expr_type d) s1 sm ee (BytesV bs) data t /\
      expr_sim_inv cenv cx env ee /\ body_exprs_ptr_ok cx kws /\
      stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es sa s0 t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
      ghost_inv dep cenv cx ee G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      expr_val_rel cx (BaseT AddressT) av addr t /\ op_taint tn addr = {} /\
      eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
      eval_operand data_op t = SOME (n2w (b+32)) /\
      op_taint tn len_op = {} /\ op_taint tn data_op = {} /\
      data = Var x /\ eval_operand data t = SOME (n2w b) /\
      FLOOKUP G x = SOME (base,sz) /\ op_prov G data_op = SOME (base,sz) /\ base <= b /\
      b + 32 + LENGTH bs <= base + sz /\ b < dimword (:256) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
      (!v. addr = Var v \/ data = Var v \/ len_op = Var v \/ data_op = Var v ==>
        not_fresh_at sm v))
    (\rr ee gt r. ?exc. rr = INR exc /\ expr_exit (INR exc : value + exception) r)
Proof
  strip_tac >>
  `eval_exprs cx [a;d] =
     do av <- bind (eval_expr cx a) (read_result cx);
        dv <- bind (eval_expr cx d) (read_result cx); return [av;dv] od` by
    (rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     simp[Once vyperInterpreterTheory.evaluate_def, bind_return, bind_assoc]) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sl /\ ci_mono sl sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND,
      exprLoweringPropsTheory.ci_mono_emit_op] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sl /\ cs_extends sl sm` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sm func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `expr_sim_inv cenv cx env es` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `post_value_type cenv a = expr_type a` by
    (irule loweringPostsTheory.post_value_type_word >>
     fs[compileEnvTheory.is_word_type_def]) >>
  drule_all body_base_operand_outcome_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "tail_cert"
  >- suspend "head_cert"
  >> suspend "head_bind"
QED

Resume raw_call_addr_data_header_sim_ptr[head_bind]:
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  conj_tac >- suspend "data" >>
  simp[exprSimDefsTheory.expr_exit_def] >> rpt strip_tac >>
  Cases_on `res` >> gvs[]
QED

Resume raw_call_addr_data_header_sim_ptr[head_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[operandOutcomePtrTheory.ignore_map_return] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
  goal_assum (drule_at Any)
QED

Resume raw_call_addr_data_header_sim_ptr[tail_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rewrite_tac[operandOutcomePtrTheory.ignore_map_return] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED

Resume raw_call_addr_data_header_sim_ptr[data]:
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
  `post_value_type cenv d = expr_type d` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     fs[compileEnvTheory.is_bytestring_type_def]) >>
  drule_all body_base_operand_outcome_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  suspend "header_bind"
QED

Resume raw_call_addr_data_header_sim_ptr[header_bind]:
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "data_tail_cert"
  >- suspend "data_head_cert"
  >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  conj_tac >- suspend "header" >>
  simp[exprSimDefsTheory.expr_exit_def] >> rpt strip_tac >>
  Cases_on `res` >> gvs[]
QED

Resume raw_call_addr_data_header_sim_ptr[data_head_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp[ignore_bind_def, return_def, bind_def] >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
  fs[ignore_bind_def]
QED

Resume raw_call_addr_data_header_sim_ptr[data_tail_cert]:
  POP_ASSUM_LIST (K all_tac) >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> fs[ignore_bind_def]
QED

Resume raw_call_addr_data_header_sim_ptr[header]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
  `(!z. addr = Var z ==> not_fresh_at s1 z) /\ (!l. addr <> Label l)` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `wb_frame cenv ee s1 t t'` by
    (irule exprSimWordArgsTheory.expr_post_frame >> goal_assum (drule_at Any)) >>
  `expr_val_rel cx (BaseT AddressT) v addr t /\ op_taint tn addr = {}` by
    (conj_tac
     >- (qpat_x_assum `expr_post _ _ _ _ a _ _ _ _ _ _ _ _` mp_tac >>
         simp[loweringPostsTheory.expr_post_def]) >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def]) >>
  `expr_val_rel cx (BaseT AddressT) v addr t' /\ op_taint tn' addr = {}` by
    (`is_word_type (BaseT AddressT)` by simp[compileEnvTheory.is_word_type_def] >>
     drule_all saved_word_operand_ptr_frame >> simp[]) >>
  suspend "header_suffix"
QED

Resume raw_call_addr_data_header_sim_ptr[header_suffix]:
  qpat_x_assum `value_has_type (BaseTV (BytesT _)) _` mp_tac >>
  Cases_on `v'` >> simp[vyperTypingTheory.value_has_type_def] >>
  strip_tac >> gvs[] >>
  rename1 `expr_post _ _ _ _ d _ _ _ _ _ (BytesV bs) _ _` >>
  `stmt_state_rel ctx func cenv cx ee' t'` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `local_ptrs_reserved cenv s2` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `?w. eval_operand data t' = SOME w` by
    (qpat_x_assum `expr_post _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
     metis_tac[]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
     SOME (BaseTV (BytesT (Dynamic n)))` by
    (qpat_assum `expr_body_pre _ _ _ d _`
       (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) data G' tn' t' /\
   op_taint tn' data = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def] >>
  drule_all raw_call_data_header_read_ready >> strip_tac >> gvs[] >>
  suspend "header_steps"
QED

Resume raw_call_addr_data_header_sim_ptr[header_steps]:
  `not_fresh_at s2 x` by
    (qpat_x_assum `lower_value _ _ _ d _ = _` mp_tac >>
     qpat_x_assum `local_ptrs_reserved cenv s1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule compile_lower_value_var >> simp[]) >>
  `mem_word_at (w2n w) t'.vs_memory = n2w (LENGTH bs) /\
   mem_bytes_at (w2n w+32) (LENGTH bs) t'.vs_memory = bs` by
    (qpat_x_assum `expr_post _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
       compileEnvTheory.is_word_type_def, valueEncodingDefsTheory.val_in_memory_def]) >>
  `?lx. len_op = Var lx` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[] >> metis_tac[]) >>
  `?dx. data_op = Var dx` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `lookup_var x t' = SOME w` by fs[venomStateTheory.eval_operand_def] >>
  drule_all raw_call_header_two_steps >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "header_posts"
QED

Resume raw_call_addr_data_header_sim_ptr[header_posts]:
  `expr_val_at cenv cx (expr_type d) s1 sm ee' (BytesV bs) (Var x) u` by
    (irule log_frame_placement >>
     simp[] >> qexistsl_tac [`ctx`, `ee'`, `func`, `t'`, `s2`] >> simp[] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     qpat_x_assum `expr_post _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def]) >>
  `!z. addr = Var z ==> not_fresh_at s2 z` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `expr_val_rel cx (BaseT AddressT) v addr u /\ op_taint un addr = {}` by
    (drule_all saved_word_operand_ptr_frame >> simp[]) >>
  `wb_frame cenv es sa s0 t'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     `wb_frame cenv es sa s0 t` by
       (irule exprSimWordArgsTheory.expr_post_frame >> goal_assum (drule_at Any)) >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (qexistsl_tac [`ee`, `s1`, `t`] >>
         fs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[]) >>
     goal_assum (drule_at Any)) >>
  suspend "header_frame_posts"
QED

Resume raw_call_addr_data_header_sim_ptr[header_frame_posts]:
  `wb_frame cenv es sa s0 u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (qexistsl_tac [`ee'`, `s2`, `t'`] >>
         fs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[]) >>
     goal_assum (drule_at Any)) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
     >- (qexists_tac `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
     qexistsl_tac [`G`, `ee`, `t`, `s1`, `tn`] >> simp[] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     irule exprSimWordArgsTheory.expr_post_frame >> goal_assum (drule_at Any)) >>
  `ghost_kept cenv es sa G0 tn0 s0 H un` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >> conj_tac
     >- (qexists_tac `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
     qexistsl_tac [`G'`, `ee'`, `t'`, `s2`, `tn'`] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[]) >>
  suspend "header_return"
QED

Resume raw_call_addr_data_header_sim_ptr[header_return]:
  `ee' with gas_obs := [] = ee'` by
    (qpat_x_assum `ee'.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[fragGasPathPtrTheory.gas_summary_ptr_at_def, vyperStateTheory.return_def] >>
  qexistsl_tac [`INL [v;BytesV bs]`, `ee'`, `H`, `un`, `OK u`] >> simp[] >>
  qexistsl_tac [`ee`, `t`, `t'`, `w2n w`] >>
  simp[wordsTheory.n2w_w2n, wordsTheory.word_add_n2w,
       venomStateTheory.mload_def] >>
  fs[valueEncodingDefsTheory.mem_word_at_def] >>
  `w + 32w = n2w (w2n w + 32)` by
    metis_tac[wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  simp[wordsTheory.w2n_lt, ptrDisciplineTheory.op_prov_def] >> rpt strip_tac >> gvs[] >>
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[stmtFragPtrTheory.not_fresh_at_mono]
QED

Finalise raw_call_addr_data_header_sim_ptr
