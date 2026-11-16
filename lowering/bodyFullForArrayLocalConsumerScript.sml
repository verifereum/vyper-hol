(* Conditional assembly. All seven cuts are explicit universally closed
   antecedents, not proof dependencies on their eventual suppliers. *)
Theory bodyFullForArrayLocalConsumer
Ancestors
  bodyFullForArrayLocalContracts bodyFullForArrayLocalControl
  bodyFullForArrayLocalRecovery bodyFullForRounds bodyFullPreds bodySimFull
  bodyFullGhostFrame bodyInvNoDalloca stmtSimForArrayLoop stmtSimForParts
  stmtLowering stmtLoweringMono compileEnv codegenRel contextCodegenRel
  fragExec fragGasOriginPtrLoop ptrDiscipline venomInst venomState
  vyperInterpreter vyperTypeSystem vyperState vyperTyping vyperValue
  supportedStmts supportedStmtTraverse valueEncoding exprSimAggregateLayout
  exprSimHypsDefs loweringPosts bodyPtrDefs finite_map list words
  gasOutcomeFullCompose gasOutcomeFullGuarded gasExemptCert

val _ = Parse.hide "body";
val _ = Parse.hide "cond";

val fixed_entry_contract = ``
  compile_alloc_buffer sz sa = (buf,sb) /\ buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME
    <|bb_label := sb.cs_current_bb; bb_instructions :=
      sb.cs_current_insts ++ [mk_inst aj JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  sz < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  p <> idx /\ (!x. not_fresh_at sa x ==> x <> idx) /\
  local_ptrs_reserved cenv sa /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes name es.scopes = SOME ent /\
  ent.type = ArrayTV tv (Fixed (LENGTH vs)) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\
  eval_operand saved_base s0 = SOME array_base /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~ctx_has_dalloca ctx /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?dst cc Gentry tnentry.
    lookup_var p cc = SOME dst /\ ptr_covers Gentry tnentry p cc sz /\
    FLOOKUP cc.vs_allocas sa.cs_next_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= cc.vs_alloca_next /\
    (!nm b len. local_region cenv es.scopes cc nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    ~cc.vs_halted /\ cc.vs_current_bb = cond /\ cc.vs_inst_idx = 0 /\
    lookup_var idx cc = SOME 0w /\ FLOOKUP Gentry idx = NONE /\
    op_taint tnentry (Var idx) = {} /\
    lookup_scopes name es.scopes = SOME ent /\
    ent.type = ArrayTV tv (Fixed (LENGTH vs)) /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand saved_base cc = SOME array_base /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      expr_sim_inv cenv cx env es /\ stmt_state_rel H ctx func cenv cx es cc /\
      storage_well_formed_on cx es (FST H) /\
      return_buf_frame d cenv sa cc /\ alloca_history func cc /\
      s0.vs_alloca_next <= cc.vs_alloca_next /\ allocas_from lo cc /\
      ghost_inv_at (DF H) lo d cenv cx es Gentry tnentry cc) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x cc = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP cc.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gentry x = FLOOKUP G0 x /\
      op_taint tnentry (Var x) = op_taint tn0 (Var x)) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) []
      (OK cc,Gentry,tnentry))``;

val dynamic_prefix_contract = ``
  emit_op MLOAD [Var ap] st = (Var lv,sa) /\
  compile_alloc_buffer sz sa = (buf,sb) /\ buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME
    <|bb_label := sb.cs_current_bb; bb_instructions :=
      sb.cs_current_insts ++ [mk_inst aj JMP [Label entry] []]|> /\
  sz < dimword (:256) /\ c < dimword (:256) /\
  local_ptrs_reserved cenv st /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes name es.scopes = SOME ent /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  ent.type = ArrayTV tv (Dynamic c) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\ LENGTH vs <= c /\
  return_buf_frame d cenv st s /\ alloca_history func s /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dst t Gp tp.
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gp lv = NONE /\ op_taint tp (Var lv) = {} /\
    lookup_var p t = SOME dst /\ ptr_covers Gp tp p t sz /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= t.vs_alloca_next /\
    (!nm b len. local_region cenv es.scopes t nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d cenv sb t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\ allocas_from lo t /\
      ghost_inv_at (DF H) lo d cenv cx es Gp tp t) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)) /\
    (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==>
      FLOOKUP t.vs_allocas aid = SOME bl) /\
    (?base. lookup_var ap s = SOME base /\
      mload (w2n base) s = n2w (LENGTH vs) /\
      ptr_covers G tn ap s 32 /\ mem_word_taint tn.t_mem (w2n base) = {}) /\
    exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p])
      ((update_var lv (n2w (LENGTH vs)) s) with
        vs_inst_idx := LENGTH sa.cs_current_insts) (n2w sz : bytes32) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts) /\
    (!D. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst st.cs_next_id MLOAD [Var ap] [lv];
       mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] s Gp tp) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gp,tp))``;

val dynamic_entry_contract = ``
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\ ret_pc_ok cenv st s0 /\
  ALL_DISTINCT [lv;p;idx;g;vld] /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv;p;idx;g;vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv;p;idx;g;vld]) /\
  alloca_history func s0 /\ w2n array_base + 32 <= s0.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
  exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
    (n2w sz : bytes32) = OK sA /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn
    [mk_inst mi MLOAD [saved_base] [lv];ainst] s0 G1 tn1) /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G1 tn1
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv;Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] (jump_to entry sA) G2 tn2) ==>
  ?dst cc s1.
    exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
      (n2w sz : bytes32) = OK s1 /\ s1 = sA /\
    cc = jump_to cond (update_var vld 1w (update_var g 0w
      (update_var idx 0w (jump_to entry s1)))) /\
    array_loop_inv ctx func cenv cx st0 P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    gas_path_mem ctx func s0 0 (OK cc) /\
    alloca_history func cc /\ cc.vs_memory = s0.vs_memory /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G,tn) [] (OK cc,G2,tn2))``;

val local_body_fragment_contract = ``
  !cx id typ it n stmts tops bindings ctx shadow_ctx func shadow_func
    cenv bc env env' ret_ty RetQ ee DF lo d PG st st1.
  body_stmts_full_ok cx stmts /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (For id typ it n stmts) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ it n stmts) ==> occurs_abi_decode_target target tops) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ it n stmts) = SOME env' /\
  stmt_exprs_ok cenv (For id typ it n stmts) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ it n stmts)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  declare_local cenv id typ st = (bc,st1) /\ same_frame cenv bc /\
  expr_sim_inv bc cx (extend_local env id typ F) ee ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts)
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts))
    (eval_stmts cx stmts) ee``;

val local_body_outcome_contract = ``
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ bc (stmts_env bc lctx ret_ty stmts)
    (stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts)) source ee /\
  stmts_env bc lctx ret_ty stmts sa = (cenv',sb) /\
  stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts) shadow_sa =
    (cenv',shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sa /\
  ret_pc_ok bc sa s0 /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible source (stmt_res_ok lctx) ee /\
  return_buf_frame d bc sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func bc cx ee s0 /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d bc cx ee G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 source (ee,s0,G0,tn0)
    (\H res mid G tn t. mid.gas_obs = [] /\ ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res mid gt r.
      (!tail. stmt_exit_ptr (RetQ H) (mid with gas_obs := tail) res gt r) /\
      halt_exit H cx mid res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))``;

val local_handled_round_contract = ``
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx body)
    (((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := []),s,G,tn)
    B (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
        !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u)) /\
  ~s.vs_halted /\
  (!res ee G1 tn1 t gs.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      B H res ee G1 tn1 t) /\
    eval_stmts cx body
      ((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := gs) = (res,ee) ==>
    (res = INL () \/ res = INR BreakException \/
     res = INR ContinueException) /\
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK u,G2,tn2) /\
      Q H (INL (res = INR BreakException))
        (ee with scopes := TL ee.scopes) G2 tn2 u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od)
    (es,s,G,tn) Q
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==>
        !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u))``;

(* Literal revised entry: zero-sized element copies and fixed-only freshness
   are precisely as in LocalContracts, with no positivity/extent premise. *)
val local_round_entry_revised = ``
  body_inv tops ctx cenv cx /\
  supported_stmts tops bindings stmts /\
  aty = ArrayT typ bd /\
  id NOTIN FDOM env.var_types /\
  FLOOKUP env.var_types name = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  saved_base = Var ap /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  declare_local cenv id typ sdecl = (bc,sdecl') /\ same_frame cenv bc /\
  cenv_top_ext cenv bc (FEMPTY :: ee.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id ee.scopes = NONE /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved bc scopy /\
  ret_pc_ok cenv sa s0 /\ copy_old_operand scopy bound_op /\
  copy_old_operand sa saved_base /\
  ~ctx_has_dalloca ctx /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> idx /\ x <> dv /\ x <> ov /\ x <> ep) /\
  not_fresh_at scopy idx /\ not_fresh_at scopy p /\ not_fresh_at scopy ep /\
  p <> ov /\ p <> ep /\
  not_local_ptr cenv ee.scopes ov /\ not_local_ptr cenv ee.scopes ep /\
  ALL_DISTINCT [idx;dv;ov;ep;p] /\
  (bd = Dynamic (bound_length bd) ==> ALL_DISTINCT [idx;dv;ov;tov;ep;p]) /\
  (!x. bound_op = Var x ==> x <> dv /\ x <> ov /\
    (bd = Dynamic (bound_length bd) ==> x <> tov) /\
    x <> ep /\ x <> idx /\ x <> nv) /\
  (!x. saved_base = Var x ==> x <> dv /\ x <> ov /\
    (bd = Dynamic (bound_length bd) ==> x <> tov) /\ x <> ep) /\
  fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx;bound_op] [dv];
       mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|> /\
  lookup_block body_lbl func.fn_blocks = SOME
    <|bb_label := body_lbl; bb_instructions := sb0.cs_current_insts ++ tail_code|> /\
  scopy.cs_current_bb = body_lbl /\
  scopy.cs_current_insts =
    [mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]] ++
    (case bd of Fixed n => []
     | Dynamic n => [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
    [mk_inst j4 ADD [saved_base;
      (case bd of Fixed n => Var ov | Dynamic n => Var tov)] [ep]] /\
  (bd = Dynamic (bound_length bd) ==>
    not_fresh_at scopy tov /\ tov <> p /\ tov <> idx /\
    (!x. not_fresh_at sa x ==> x <> tov) /\
    (joff <> j3 /\ joff <> j4)) /\
  compile_iter_elem_copy cenv (Var ep) (Var p) bytes LocMemory F typ typ
    scopy = ((),sb0) /\ fn_has_code scopy sb0 func /\
  cs_extends scopy sb0 /\ scopy.cs_next_var <= sb0.cs_next_var /\
  bytes = type_memory_size tv /\ type_memory_bytes cenv typ = bytes /\
  bytes + 64 < dimword (:256) /\
  sz = type_memory_bytes cenv typ /\
  sa.cs_next_var <= scopy.cs_next_var /\
  sa.cs_next_var <= sb0.cs_next_var /\ cs_extends sa sb0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  k < LENGTH vs /\ MAP Value (DROP k vs) = Value v :: rs /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    dead_lo_ok H (DF H) lo cenv cx /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    LENGTH vs < dimword (:256) /\ lookup_var idx s = SOME (n2w k) /\
    eval_operand bound_op s = SOME (n2w (LENGTH vs)) /\
    FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
    op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
    lookup_scopes name ee.scopes = SOME ent /\
    ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand saved_base s = SOME arr_base /\
    lookup_var p s = SOME dst /\ ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= s.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes s nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) ==>
  ?ss Gs ts. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK ss,Gs,ts) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) /\
    stmt_state_rel H ctx func bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) ss /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d bc sb0 ss /\ alloca_history func ss /\
    ghost_inv_at (DF H) lo d bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) Gs ts ss /\
    ~ss.vs_halted /\ ss.vs_current_bb = sb0.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ret_pc_ok bc sb0 ss /\
    allocas_from lo ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
    lookup_var p ss = SOME dst /\ ptr_covers Gs ts p ss sz /\
    FLOOKUP ss.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= ss.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes ss nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    lookup_var idx ss = SOME (n2w k) /\
    eval_operand bound_op ss = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gs idx = NONE /\ op_prov Gs bound_op = NONE /\
    op_taint ts (Var idx) = {} /\ op_taint ts bound_op = {} /\
    lookup_scopes name ee.scopes = SOME ent /\
    ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand saved_base ss = SOME arr_base /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x ss = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP ss.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gs x = FLOOKUP G0 x /\
      op_taint ts (Var x) = op_taint tn0 (Var x))``;

fun close_contract tm = boolSyntax.list_mk_forall (free_vars tm,tm);
val consumer_cuts = map close_contract
  [fixed_entry_contract,dynamic_prefix_contract,dynamic_entry_contract,
   local_body_fragment_contract,local_body_outcome_contract,
   local_handled_round_contract,local_round_entry_revised];
val consumer_antecedent = boolSyntax.list_mk_conj consumer_cuts;

Theorem body_for_local_array_full_from_contracts:
  ^consumer_antecedent ==>
  !bd name cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (it = Array (Name (ArrayT typ bd) name) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "fixed")
    (CONJUNCTS_THEN2 (mk_asm "dynamic_prefix")
      (CONJUNCTS_THEN2 (mk_asm "dynamic_entry")
        (CONJUNCTS_THEN2 (mk_asm "body_fragment")
          (CONJUNCTS_THEN2 (mk_asm "body_outcome")
            (CONJUNCTS_THEN2 (mk_asm "handler") (mk_asm "entry"))))))) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `For id typ _ n stmts` >>
  `~ctx_has_dalloca ctx` by (drule body_inv_no_dalloca >> simp[]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  FAIL_TAC "local-consumer-runtime"
QED
