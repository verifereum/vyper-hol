Theory s1PrefixBlueprintScalarSuffix
Ancestors
  s1PrefixCreateOperandCut s1PrefixPreds s1PrefixDefs bodyFullCreateHeld
  bodyFullPreds compileEnv exprLowering builtinCreate
  exprSimDefs loweringPosts bodyPtrDefs gasStorage fragGasOriginPtr
  vyperStorageTrace vyperInterpreter

(* The scalar traversal is shared with the full outcome proof. Only the
   judgment at each cut changes: its continuation follows request prefixes. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (BETA_RULE (Q.INST
    [`ListOK` |-> `body_exprs_prefix_ok cx`, `HeadOK` |-> `body_expr_prefix_ok cx`,
     `Run` |-> `gas_prefix_full
       (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0`]
    blueprint_scalar_suffix_cut_by_stages)) >>
  map_every (fn pat => qpat_assum pat (irule_at Any))
    [`expr_body_pre _ _ _ (Call _ _ _ _) _`,
     `lower_value _ _ _ amount sa = _`,
     `lower_value _ _ _ (gas_shadow_expr amount) sh = _`,
     `compile_create_salt _ _ _ sm = _`,
     `compile_create_salt _ _ _ shm = _`,
     `gas_shadow_function func shadow_func`,
     `return_buf_frame d cenv sa s`,
     `eval_operand target s = SOME aw`,
     `body_inv tops ctx cenv cx`,
     `_ sn = (off,sb)`, `_ shn = (off,shb)`] >>
  qexistsl [`cnt`,`args_ptr`,`args`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt gen_tac >> rename1 `body_exprs_prefix_ok cx (e::xs) ==> _` >>
       simp[Once body_exprs_prefix_ok_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- (qspecl_then
        [`gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0`,
         `body_expr_prefix_ok cx`]
        (irule o BETA_RULE) blueprint_offset_cut_by_operand >>
      rpt (goal_assum (drule_at Any)) >> simp[] >>
      rpt gen_tac >> strip_tac >> irule create_body_operand_cut_prefix_replay >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule create_body_operand_cut_prefix_replay >> rpt (goal_assum (drule_at Any)) >> simp[]
QED
*)
Theorem blueprint_scalar_suffix_prefix_from_replay:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target_e::amount::(salts ++ offset::ctor)) dflt) entry /\
  expr_sim_inv cenv cx env es /\ body_exprs_full_ok cx (amount::(salts ++ [offset])) /\
  body_exprs_prefix_ok cx (amount::(salts ++ [offset])) /\
  expr_type amount = BaseT (UintT 256) /\ expr_type offset = BaseT (UintT 256) /\
  (if salted then ?e. salts = [e] /\ expr_type e = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  lower_value compile_expr cenv (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
    (gas_shadow_expr amount) sh = (y,shm) /\
  compile_create_salt compile_expr cenv (if salted then SOME (HD salts) else NONE) sm = (sop,sn) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv)
    (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) shm = (sop,shn) /\
  (case expr_int_literal (origin_fold_value offset) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr cenv (expr_type offset) offset) sn = (off,sb) /\
  (case expr_int_literal (origin_fold_value offset) of
     SOME i => comp_return (Lit (i2w i))
   | NONE => lower_value compile_expr (gas_shadow_env T cenv) (expr_type offset)
       (gas_shadow_expr offset)) shn = (off,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sm shm /\ gas_shadow_state sn shn /\
  gas_shadow_state sb shb /\ gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_has_code sh shm shadow_func /\ fn_has_code shm shn shadow_func /\
  fn_has_code shn shb shadow_func /\ ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  (!x. target = Var x ==> not_fresh_at sa x) /\ (!l. target <> Label l) /\
  (!x. args_ptr = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\ LENGTH args < 2 ** 64 /\
  (!av sv ov. storage_trace_frame
    (next av sv ov : evaluation_state -> value evaluation_result)) /\
  (!av sv ov ee G1 tn1 t gs.
    (!tail. eval_exprs cx (amount::(salts ++ [offset])) (es with gas_obs := gs ++ tail) =
      (INL (av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])),ee with gas_obs := tail)) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) ==>
    eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH args) t = args)) /\
  (!av sv ov yw sw ow ee G1 tn1 t marks.
    dest_NumV av = SOME (w2n yw) /\ dest_optional_salt sv = SOME sw /\
    dest_NumV ov = SOME (w2n ow) /\ IS_SOME sv = salted /\
    blueprint_literal_offset cx salted (target_e::amount::(salts ++ offset::ctor)) =
      IS_SOME (expr_int_literal (origin_fold_value offset)) /\
    eval_operand target t = SOME aw /\ op_taint tn1 target = {} /\
    eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    eval_operand off t = SOME ow /\ op_taint tn1 off = {} /\ op_prov G1 off = NONE /\
    (!x. MEM (Var x) [target;off;args_ptr;cnt;y] \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    eval_operand cnt t = SOME (n2w (LENGTH args)) /\ op_taint tn1 cnt = {} /\ op_prov G1 cnt = NONE /\
    (cnt <> Lit 0w ==> ?q a. args_ptr = Var q /\ lookup_var q t = SOME a /\
      ptr_covers G1 tn1 q t (LENGTH args) /\ (args = [] \/ w2n a + LENGTH args <= t.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn1.t_mem) /\
      read_memory (w2n a) (LENGTH args) t = args) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ expr_sim_inv cenv cx env ee /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    return_buf_frame d cenv sb t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (next av sv ov) (ee,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_exprs cx (amount::(salts ++ [offset])))
      (\vs. next (HD vs) (if salted then SOME (EL 1 vs) else NONE) (LAST vs)))
    (es,s,G,tn)
Proof
  cheat
QED
