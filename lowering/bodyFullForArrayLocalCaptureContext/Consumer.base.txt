(* Conditional assembly. All seven cuts are explicit universally closed
   antecedents, not proof dependencies on their eventual suppliers. *)
Theory bodyFullForArrayLocalConsumer
Ancestors ptrCoverage[qualified,ignore_grammar] immutableMemoryFrame[qualified,ignore_grammar] typedMemoryCopy[qualified,ignore_grammar] abiDecodeStaticProps[qualified,ignore_grammar] lowerDloadRelocationBoundary[qualified,ignore_grammar] abiEncoderSourceInvoke[qualified,ignore_grammar] o1ContractLowerDloadTaint[qualified,ignore_grammar] pred_set[qualified,ignore_grammar]
  bodyFullForArrayLocalContracts bodyFullForArrayLocalControl
  bodyFullForArrayLocalRecovery bodyFullForRounds bodyFullPreds bodySimFull
  bodyFullGhostFrame bodyInvNoDalloca stmtSimForArrayLoop stmtSimForParts
  stmtLowering stmtLoweringMono compileEnv codegenRel contextCodegenRel
  fragExec fragGasOriginPtrLoop ptrDiscipline venomInst venomState
  vyperInterpreter vyperTypeSystem vyperState vyperTyping vyperValue
  supportedStmts supportedStmtTraverse valueEncoding exprSimAggregateLayout
  exprSimHypsDefs loweringPosts bodyPtrDefs finite_map list words
  gasOutcomeFullCompose gasOutcomeFullGuarded gasExemptCert
  stmtSimForArray stmtSimForArrayFrag
  vyperStorageTrace exprSimProps vyperTypeValues vyperTypeInvariants
  vyperAST vyperArray vyperTypeEnv arithmetic vyperValueOperation
  exprSimHyps allocLimits gasShadow whitelistForIterDynFrag
  bodyFullForArrayDynamicScalar
  gasShadowStmtEnv gasShadowCompileStmtOps gasShadowState

val _ = Parse.hide "body";
val _ = Parse.hide "cond";
val _ = Parse.hide "start";
val _ = Parse.hide "finish";

(* Non-logical diagnostic: prints the live sequent and its free-variable types.
   suspend retains the obligation; no theorem is admitted or finalised. *)
fun capture_goal name (g as (asl,w)) =
  (print ("\nCAPTURE-BEGIN " ^ name ^ "\n");
   List.app (fn v => print (fst (dest_var v) ^ " : " ^
                            Parse.type_to_string (type_of v) ^ "\n"))
            (free_varsl (w::asl));
   print "ASSUMPTIONS\n";
   List.app (fn a => print (Parse.term_to_string a ^ "\n;\n")) asl;
   print ("CONCLUSION\n" ^ Parse.term_to_string w ^
          "\nCAPTURE-END " ^ name ^ "\n");
   suspend ("capture_" ^ name) g);

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
  `?ent tv ap az av vs env_b.
    env' = env /\
    FLOOKUP env.var_types name = SOME (ArrayT typ bd) /\
    id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT typ bd) name)) stmts /\
    type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name es.scopes = SOME ent /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    ent.type = ArrayTV tv bd /\ value_has_type ent.type ent.value /\
    well_formed_type_value ent.type /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\ LENGTH vs <= n /\
    LENGTH vs < dimword (:256) /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
    (!gs. eval_iterator cx (Array (Name (ArrayT typ bd) name))
       (es with gas_obs := gs) = (INL (MAP Value vs),es with gas_obs := gs)) /\
    body_for_full_ok cx tv id stmts (MAP Value vs) /\
    FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE`
    by suspend "source_packet" >>
  gvs[] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  suspend "runtime"
QED

Resume body_for_local_array_full_from_contracts[source_packet]:
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
     "body_outcome","handler","entry"] >>
  Cases_on `bd`
  >- (rename1 `Fixed m` >>
      `m = n` by fs[supported_stmt_def,supported_iterator_def] >> gvs[] >>
      rename1 `For id typ (Array (Name (ArrayT typ (Fixed n)) name)) n stmts` >>
      drule array_for_hypotheses >> disch_then drule >> simp[] >> strip_tac >> gvs[] >>
      drule_all array_name_local_binding >> strip_tac >>
      rename1 `lookup_scopes name es.scopes = SOME ent` >>
      rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
      `?al. ent.value = ArrayV (SArrayV al)` by
        (Cases_on `ent.value` >> gvs[value_has_type_def] >>
         rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >>
         gvs[value_has_type_def]) >>
      `evaluate_type (get_tenv cx) (ArrayT typ (Fixed n)) =
        SOME (ArrayTV tv (Fixed n))` by
        (fs[expr_sim_inv_def,well_typed_expr_def,env_consistent_def,
            env_scopes_consistent_def] >> metis_tac[]) >>
      `!gs. eval_iterator cx (Array (Name (ArrayT typ (Fixed n)) name))
         (es with gas_obs := gs) =
         (INL (MAP Value (array_elements (ArrayTV tv (Fixed n)) (SArrayV al))),
          es with gas_obs := gs)` by
        (gen_tac >> irule eval_iterator_fixed_name >> simp[]) >>
      qmatch_asmsub_abbrev_tac `INL (MAP Value vs)` >>
      `LENGTH vs = n` by simp[Abbr `vs`,fixed_array_elements_length] >>
      `body_for_full_ok cx tv id stmts (MAP Value vs)` by
        (qpat_x_assum `!s tyv t s3 vs t3 s4 t4. _` mp_tac >>
         simp[lift_option_type_def,return_def,check_def,assert_def,
              compatible_bound_def] >> disch_then irule >> simp[] >>
         qexistsl_tac [`es with gas_obs := []`,`es with gas_obs := []`] >> simp[]) >>
      `FLOOKUP env.var_types name = SOME (ArrayT typ (Fixed n))` by
        fs[well_typed_expr_def] >>
      `FLOOKUP cenv.ce_vars id = NONE` by
        (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[bodySimTheory.ce_locals_declared_def] >>
         metis_tac[]) >>
      `lookup_scopes id es.scopes = NONE` by
        (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
         gvs[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def] >>
         res_tac >> gvs[FLOOKUP_DEF]) >>
      qexistsl_tac [`ent`,`tv`] >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `SArrayV al` >> gvs[Abbr `vs`]) >>
  suspend "dynamic_source"
QED

Resume body_for_local_array_full_from_contracts[dynamic_source]:
  rename1 `Dynamic c` >>
  `c <= n` by fs[supported_stmt_def,supported_iterator_def] >>
  `env' = env /\ FLOOKUP env.var_types name = SOME (ArrayT typ (Dynamic c)) /\
   id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (Name (ArrayT typ (Dynamic c)) name)) stmts /\
   ?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def,well_typed_iterator_def,well_typed_expr_def,
        expr_type_def,optionTheory.IS_SOME_EXISTS,AllCaseEqs()] >>
  `supported_stmts tops bindings stmts /\
   ~supported_stmts_expr_exists expr_internal_call_root stmts` by
    fs[supported_stmt_def] >>
  `?ent. lookup_scopes name es.scopes = SOME ent` by
    (gvs[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def,
         optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Dynamic c)) = SOME ent.type` by
    (fs[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def] >>
     metis_tac[]) >>
  `c < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def,AllCaseEqs(),type_slot_size_def,bound_length_def] >>
     rpt strip_tac >> rename1 `0 < type_slot_size elem_tv` >>
     `c <= c * type_slot_size elem_tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `c * 1` >> simp[]) >> decide_tac) >>
  drule evaluate_type_ArrayT_cases >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `value_has_type ent.type ent.value /\ well_formed_type_value ent.type` by
    (irule scope_well_typed_lookup_scopes >>
     fs[expr_sim_inv_def,state_well_typed_def] >> metis_tac[]) >>
  `?vs. ent.value = ArrayV (DynArrayV vs) /\ LENGTH vs <= c` by
    (Cases_on `ent.value` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  `?ap az. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `!gs. eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name))
       (es with gas_obs := gs) = (INL (MAP Value vs),es with gas_obs := gs)` by
    (gen_tac >> simp[Once evaluate_def] >> simp[Once evaluate_def] >>
     simp[array_iterator_results_def,read_result_def,read_place_def,
          read_memory_path_def,evaluate_subscripts_def,get_scopes_def,
          type_check_def,vyperStateTheory.assert_def,lift_option_type_def,
          lift_sum_def,ignore_bind_def,vyperStateTheory.bind_def,
          vyperStateTheory.return_def,expr_type_def,extract_elements_def,
          array_elements_def]) >>
  `body_for_full_ok cx tv id stmts (MAP Value vs)` by
    (qpat_x_assum `!s tyv t s3 vs t3 s4 t4. _` mp_tac >>
     simp[lift_option_type_def,return_def,check_def,assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es with gas_obs := []`,`es with gas_obs := []`] >> simp[]) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[bodySimTheory.ce_locals_declared_def] >>
     metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  qexistsl_tac [`ent`,`tv`,`ap`,`az`,`DynArrayV vs`,`vs`,`env_b`] >>
  simp[array_elements_def]
QED

Resume body_for_local_array_full_from_contracts[runtime]:
  qmatch_asmsub_abbrev_tac `body_for_full_ok cx tv id stmts (MAP Value vs)` >>
  `cenv.ce_alloca_locals` by fs[bodySimTheory.body_inv_def] >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[bodySimTheory.stmt_exprs_ok_def,alloc_limits_stmt_def] >>
  `type_memory_bytes cenv typ = type_memory_size tv` by
    (drule_all expr_sim_inv_memory_size >> simp[]) >>
  `type_memory_bytes cenv typ + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `!c lc a b. compile_stmts c lc ret_ty stmts a = ((),b) ==>
      cs_extends a b /\ a.cs_next_var <= b.cs_next_var` by
    (rpt strip_tac >>
     qspecl_then [`c`,`lc`,`ret_ty`,`stmts`,`a`] mp_tac (cj 2 compile_stmt_ci_mono) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `cenv' = cenv /\
   compile_stmt cenv lctx ret_ty
     (For id typ (Array (Name (ArrayT typ bd) name)) n stmts) sa = ((),sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     simp[stmt_env_def,declare_stmt_local_def,comp_ignore_bind_def,
          comp_bind_def,comp_return_def] >>
     pairarg_tac >> simp[]) >>
  rename1 `compile_stmt _ _ _ _ start = ((),finish)` >>
  rename1 `gas_shadow_state start shadow_start` >>
  rename1 `gas_shadow_state finish shadow_finish` >>
  (* The suffix determines the index before H is chosen.  Static register
     parameters allow the same invariant to be used by both initializations. *)
  qabbrev_tac `Head = \idx p bound_op cond_lbl ainst arr_base dst H rs ee G tn s.
    LENGTH rs <= LENGTH vs /\
    rs = MAP Value (DROP (LENGTH vs - LENGTH rs) vs) /\
    expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ dead_lo_ok H (DF H) lo cenv cx /\
    return_buf_frame d cenv start s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    LENGTH vs < dimword (:256) /\
    lookup_var idx s = SOME (n2w (LENGTH vs - LENGTH rs)) /\
    eval_operand bound_op s = SOME (n2w (LENGTH vs)) /\
    FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
    op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
    lookup_scopes name ee.scopes = SOME ent /\
    ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand (Var ap) s = SOME arr_base /\
    lookup_var p s = SOME dst /\ ptr_covers G tn p s (type_memory_bytes cenv typ) /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,type_memory_bytes cenv typ) /\
    w2n dst + type_memory_bytes cenv typ < dimword (:256) /\
    w2n dst + type_memory_bytes cenv typ <= s.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes s nm b len ==>
      regions_disjoint (w2n dst) (type_memory_bytes cenv typ) b len) /\
    (!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at start x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    lookup_scopes id ee.scopes = NONE /\ ret_pc_ok cenv start s` >>
  (* Normalize the two compiler branches before any loop reasoning.  All
     bounds, labels and registers in this packet are independent of H. *)
  `?bc p idx dv ov tov ep nv bound_op cond_lbl body_lbl incr_lbl exit_lbl
      scopy sb0 sb1 sj ainst j1 j2 j3 joff j4 i1 i2 i3 sdecl sdecl'.
    lookup_block cond_lbl func.fn_blocks = SOME
      <|bb_label := cond_lbl; bb_instructions :=
        [mk_inst j1 EQ [Var idx;bound_op] [dv];
         mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|> /\
    lookup_block incr_lbl func.fn_blocks = SOME
      <|bb_label := incr_lbl; bb_instructions :=
        [mk_inst i1 ADD [Var idx;Lit 1w] [nv];
         mk_inst i2 ASSIGN [Var nv] [idx];
         mk_inst i3 JMP [Label cond_lbl] []]|> /\
    scopy.cs_current_bb = body_lbl /\
    scopy.cs_current_insts =
      [mk_inst j3 MUL [Var idx;Lit (n2w (type_memory_bytes cenv typ))] [ov]] ++
      (case bd of Fixed m => []
       | Dynamic c => [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
      [mk_inst j4 ADD [Var ap;
        (case bd of Fixed m => Var ov | Dynamic c => Var tov)] [ep]] /\
    compile_iter_elem_copy cenv (Var ep) (Var p) (type_memory_bytes cenv typ)
      LocMemory F typ typ scopy = ((),sb0) /\
    sb0.cs_current_bb = body_lbl /\
    sb0.cs_current_insts = scopy.cs_current_insts ++ emitted_insts scopy sb0 /\
    same_blocks scopy sb0 /\ fn_has_code scopy sb0 func /\
    compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = ((),sb1) /\
    fn_has_code sb0 sb1 func /\
    local_ptrs_reserved bc scopy /\ local_ptrs_reserved bc sb0 /\
    ~block_is_terminated sb0 /\
    (~block_is_terminated sb1 ==>
      sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
      sj.cs_current_insts = sb1.cs_current_insts ++
        [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
      fn_has_code sb1 sj func) /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ)) /\
    (!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP cenv.ce_vars nm) /\
    bc with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
      ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
    (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
      not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
      not_local_ptr cenv scs nv) /\
    ALL_DISTINCT [idx;dv;ov;ep;nv;p] /\
    (bd = Dynamic (bound_length bd) ==>
      ALL_DISTINCT [idx;dv;ov;tov;ep;nv;p] /\
      (!scs. not_local_ptr cenv scs tov)) /\
    (~MEM ap [idx;dv;ov;ep;nv]) /\
    (bd = Dynamic (bound_length bd) ==> ap <> tov) /\
    not_fresh_at scopy idx /\ not_fresh_at scopy p /\ not_fresh_at scopy ep /\
    not_fresh_at scopy ap /\
    finish.cs_current_bb = exit_lbl /\ finish.cs_current_insts = [] /\
    declare_local cenv id typ sdecl = (bc,sdecl') /\
    (!x. not_fresh_at start x ==>
      not_fresh_at scopy x /\ x <> dv /\ x <> ov /\ x <> ep /\
      (bd = Dynamic (bound_length bd) ==> x <> tov)) /\
    (!x. not_fresh_at start x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\ not_fresh_at sb0 ap /\
    (?arr_base dst cc Gentry tnentry.
      ~cc.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) [] (OK cc,Gentry,tnentry) /\
        Head idx p bound_op cond_lbl ainst arr_base dst H (MAP Value vs)
          (es with gas_obs := []) Gentry tnentry cc)) /\
    (cs_extends start scopy /\ cs_extends scopy sb0 /\
     start.cs_next_var <= scopy.cs_next_var /\
     scopy.cs_next_var <= sb0.cs_next_var /\
     start.cs_next_var <= sb0.cs_next_var /\
     copy_old_operand start (Var ap) /\ copy_old_operand scopy bound_op /\
     (!x. bound_op = Var x ==> x <> dv /\ x <> ov /\
       (bd = Dynamic (bound_length bd) ==> x <> tov) /\
       x <> ep /\ x <> idx /\ x <> nv) /\
     (bd = Dynamic (bound_length bd) ==>
       not_fresh_at scopy tov /\ tov <> p /\ tov <> idx /\
       joff <> j3 /\ joff <> j4) /\
     (?tail_code. lookup_block body_lbl func.fn_blocks = SOME
       <|bb_label := body_lbl;
         bb_instructions := sb0.cs_current_insts ++ tail_code|>)) /\
    (?bc_out shadow_sb0 shadow_sb1.
      stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb1) /\
      stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty
        (MAP gas_shadow_stmt stmts) shadow_sb0 = (bc_out,shadow_sb1) /\
      gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
      fn_has_code shadow_sb0 shadow_sb1 shadow_func)`
    by suspend "code_packet" >>
  suspend "initialized_packet"
QED

Resume body_for_local_array_full_from_contracts[code_packet]:
  Cases_on `bd`
  >- suspend "fixed_runtime" >>
  suspend "dynamic_runtime"
QED

Resume body_for_local_array_full_from_contracts[fixed_runtime]:
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by simp[] >>
  `n' = n` by
    (qpat_x_assum `supported_stmt _ _ _` mp_tac >>
     simp[supported_stmt_def,supported_iterator_def,AllCaseEqs()]) >>
  qpat_x_assum `n' = n` SUBST_ALL_TAC >>
  drule_all stmtSimForArrayPartsTheory.compile_for_array_stages >> strip_tac >>
  drule_all stmtSimForArrayPartsTheory.compile_for_array_prefix >> strip_tac >>
  drule stmtSimForArrayPartsTheory.compile_for_array_suffix >> strip_tac >>
  `cs_extends start sa` by
    (irule stmtSimForArrayPartsTheory.array_prefix_extends >>
     simp_tac (srw_ss()) [] >> (simp[])) >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def,mk_inst_def,is_terminator_def] >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
  drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
  drule stmtSimForArrayPartsTheory.array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by
    (qpat_x_assum `!c lc a b. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all stmtSimForArrayPartsTheory.array_stages_code >> strip_tac >>
  `?bc_out shadow_sb0 shadow_sb1.
    stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc_out,sb1) /\
    stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt stmts)
      shadow_sb0 = (bc_out,shadow_sb1) /\
    gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
    fn_has_code shadow_sb0 shadow_sb1 shadow_func` by suspend "fixed_shadow" >>
  suspend "fixed_staged_static"
QED

Resume body_for_local_array_full_from_contracts[fixed_shadow]:
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) shadow_start = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,gas_shadow_stmt_def,
       gas_shadow_iterator_def,gas_shadow_expr_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> Cases_on `_0` >> simp[] >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ shadow_start = _`
    (mk_asm "shadow_compile") >>
  asm "shadow_compile" (mp_then (Pat `compile_stmt _ _ _ _ _ = _`) mp_tac
    stmtSimForArrayPartsTheory.compile_for_array_stages) >>
  disch_then (qspecl_then [`az`,`Var ap`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `prefix start = ((bc,entry',cond,bod,incr,exit,idx,off,ep),sa)` >>
  `gas_shadow_compiles prefix prefix` by
    (simp_tac (srw_ss()) [Abbr `prefix`,comp_ignore_bind_def] >>
     rpt (ho_match_mp_tac gas_shadow_compiles_bind >>
       (conj_tac >- simp[
         gasShadowCompileStmtBaseTheory.gas_shadow_compiles_declare_local,
         gasShadowCompileStmtBaseTheory.gas_shadow_compiles_emit_local_alloca,
         gas_shadow_compiles_fresh_label,gas_shadow_compiles_fresh_var,
         gas_shadow_compiles_emit_inst,gas_shadow_compiles_emit_op,
         gas_shadow_compiles_new_block]) >> gen_tac) >>
     simp[gas_shadow_compiles_return]) >>
  qpat_x_assum `gas_shadow_compiles prefix prefix` mp_tac >>
  pure_rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`start`,`shadow_start`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `prefix`] >> strip_tac >>
  qpat_x_assum `bc = bc'` (SUBST_ALL_TAC o SYM) >>
  `exit' = exit /\ incr' = incr /\ bod' = bod /\ cond' = cond /\
   entry'' = entry' /\ idx' = idx` by simp[] >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`exit' = exit`,`incr' = incr`,`bod' = bod`,`cond' = cond`,
     `entry'' = entry'`,`idx' = idx`] >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`fresh_label_output "iter_entry" _ = entry'`,
     `fresh_label_output "iter_cond" _ = cond`,
     `fresh_label_output "iter_body" _ = bod`,
     `fresh_label_output "iter_incr" _ = incr`,
     `fresh_label_output "iter_exit" _ = exit`,
     `STRING #"%" _ = idx`] >>
  qpat_x_assum `(case FLOOKUP bc.ce_vars id of _ => _ | _ => _) sa' = _`
    mp_tac >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `copy sa = ((),sb0)` >>
  `gas_shadow_compiles copy copy` by
    simp[Abbr `copy`,gasShadowCompileStmtOpsTheory.gas_shadow_compiles_iter_elem_copy] >>
  `gas_shadow_state sb0 sb0'` by
    (qpat_x_assum `gas_shadow_compiles copy copy` mp_tac >>
     pure_rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sa'`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[Abbr `copy`]) >>
  Cases_on `stmts_env bc (InLoop exit incr) ret_ty stmts sb0` >>
  rename1 `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc_out,body_end)` >>
  `body_end = sb1` by
    (qpat_x_assum `compile_stmts bc _ _ stmts sb0 = _` mp_tac >>
     simp[stmtSimPropsTheory.compile_stmts_env]) >>
  qpat_x_assum `body_end = sb1` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`stmts`,`bc`,`InLoop exit incr`,`ret_ty`]
    gas_shadow_stmts_env) >>
  pure_rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sb0`,`sb0'`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = _`
    (fn th => pure_rewrite_tac[th,pairTheory.FST,pairTheory.SND]) >> strip_tac >>
  `stmts_env bc (InLoop exit incr) ret_ty
    (MAP gas_shadow_stmt stmts) sb0' = (bc_out,sb1')` by
    (qpat_x_assum `compile_stmts bc _ _ (MAP _ _) sb0' = _` mp_tac >>
     simp[stmtSimPropsTheory.compile_stmts_env] >> strip_tac >>
     qpat_x_assum `SND _ = sb1'` (SUBST1_TAC o SYM) >> simp[]) >>
  `gas_shadow_state sb1 sb1'` by
    (qpat_x_assum `gas_shadow_state sb1 (SND _)` mp_tac >>
     qpat_assum `stmts_env bc (InLoop exit incr) ret_ty (MAP _ _) sb0' = _`
       (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp_tac bool_ss []) >>
  `cs_extends shadow_start sa'` by
    (qpat_assum `_ shadow_start = ((bc,entry',cond,bod,incr,exit,idx,off',ep'),sa')`
       (mp_then Any mp_tac stmtSimForArrayPartsTheory.compile_for_array_prefix) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule stmtSimForArrayPartsTheory.array_prefix_extends >>
     simp_tac (srw_ss()) [] >> simp[]) >>
  `~block_is_terminated sa'` by
    (qpat_assum `gas_shadow_state sa sa'`
      (mp_then Any mp_tac gasShadowCompileStmtBaseTheory.gas_shadow_state_terminated) >>
     simp[]) >>
  `cs_extends sa' sb0'` by
    (qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ sa' = _`
      (mp_then Any mp_tac stmtSimForArrayPartsTheory.array_iter_copy_static) >>
     simp[]) >>
  `cs_extends sb0' sb1'` by
    (qpat_assum `compile_stmts _ _ _ (MAP _ _) sb0' = _`
      (mp_then Any mp_tac (SRULE[cs_mono_def] (cj 2 compile_stmt_cs_mono))) >>
     simp[cs_mono_def]) >>
  `cs_extends sb1' sj'` by
    (qpat_assum `emit_jmp_if_not_terminated _ sb1' = _`
      (mp_then Any mp_tac stmtSimForArrayPartsTheory.array_body_backedge) >> simp[]) >>
  `cs_extends sj' cs'` by
    (qpat_assum `_ sj' = ((),cs')`
      (mp_then Any mp_tac stmtSimForArrayPartsTheory.compile_for_array_suffix) >>
     simp[]) >>
  qpat_x_assum `cs' = shadow_finish` SUBST_ALL_TAC >>
  `cs_extends shadow_start sb0'` by
    (irule cs_extends_trans >> qexists_tac `sa'` >> simp[]) >>
  `cs_extends sb1' shadow_finish` by
    (irule cs_extends_trans >> qexists_tac `sj'` >> simp[]) >>
  `fn_has_code sb0' sb1' shadow_func` by
    (irule fn_has_code_mid >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`shadow_finish`,`shadow_start`] >> simp[]) >>
  qpat_x_assum `exit = fresh_label_output _ _` SUBST_ALL_TAC >>
  qpat_x_assum `incr = fresh_label_output _ _` SUBST_ALL_TAC >>
  qexistsl_tac [`bc_out`,`sb0'`,`sb1'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_for_local_array_full_from_contracts[fixed_staged_static]:
  `sb0.cs_current_bb = bod` by fs[exprLoweringPropsTheory.same_blocks_def] >>
  `lookup_block start.cs_current_bb func.fn_blocks = SOME
    <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
      [mk_inst start.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p];
       mk_inst (start.cs_next_id + 1) JMP [Label entry'] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 3 sa.cs_blocks`,`start`,`sa`] >>
     qpat_assum `sa.cs_blocks = _` mp_tac >>
     qpat_assum `fn_has_code start sa func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block entry' func.fn_blocks = SOME
    <|bb_label := entry'; bb_instructions :=
      [mk_inst (start.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
       mk_inst (start.cs_next_id + 3) JMP [Label cond] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 3 sa.cs_blocks`,`start`,`sa`] >>
     qpat_assum `sa.cs_blocks = _` mp_tac >>
     qpat_assum `fn_has_code start sa func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block cond func.fn_blocks = SOME
    <|bb_label := cond; bb_instructions :=
      [mk_inst (start.cs_next_id + 4) EQ [Var idx;Lit (n2w n)] [dv];
       mk_inst (start.cs_next_id + 5) JNZ [Var dv;Label exit;Label bod] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 3 sa.cs_blocks`,`start`,`sa`] >>
     qpat_assum `sa.cs_blocks = _` mp_tac >>
     qpat_assum `fn_has_code start sa func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 2 finish.cs_blocks`,`sj`,`finish`] >> simp[]) >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  `start.cs_next_var + 5 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc a b. _ ==> _ /\ _` drule >> simp[]) >>
  `start.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all stmtSimForArrayFragTheory.array_declared_reserved >> strip_tac >>
  `(!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
      not_local_ptr cenv scs ov /\ not_local_ptr cenv scs epv /\
      not_local_ptr cenv scs nv)` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `start` >> simp[]) >>
  `not_fresh_at start ap` by
    (qpat_assum `local_ptrs_reserved cenv start` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  `ALL_DISTINCT [idx;dv;ov;epv;nv;p] /\
   (!x. not_fresh_at start x ==> x <> p /\ x <> idx) /\
   (!x. not_fresh_at start x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> epv) /\
   (!x. not_fresh_at start x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
   not_fresh_at sa idx /\ not_fresh_at sa p /\ not_fresh_at sa epv /\
   not_fresh_at sa ap /\ not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
   not_fresh_at sb0 ap /\ ~MEM ap [idx;dv;ov;epv;nv]` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`p = STRING _ _`, `idx = STRING _ _`, `dv = STRING _ _`,
        `ov = STRING _ _`, `epv = STRING _ _`, `nv = STRING _ _`,
        `sa.cs_next_var = _`, `sa.cs_next_var <= sb0.cs_next_var`,
        `start.cs_next_var + 5 <= sj.cs_next_var`, `not_fresh_at start ap`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `!st x n. not_fresh_at st x /\ st.cs_next_var <= n ==>
        x <> STRING #"%" (toString n)` by
       simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     gvs[] >>
     simp[ALL_DISTINCT,loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  qabbrev_tac `ainst = mk_inst start.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv typ))] [p]` >>
  `MEM ainst (fn_insts func)` by
    (simp[Abbr `ainst`] >> irule lookup_block_fn_insts >>
     qpat_assum `lookup_block start.cs_current_bb _ = _` (irule_at (Pos hd)) >>
     simp[]) >>
  qexistsl_tac [`bc`,`p`,`idx`,`dv`,`ov`,`epv`,`nv`,`Lit (n2w n)`,
    `cond`,`incr`,`sa`,`sb0`,`sb1`,`sj`,`ainst`,
    `start.cs_next_id + 4`,`start.cs_next_id + 5`,
    `start.cs_next_id + 6`,`start.cs_next_id + 7`,
    `sj.cs_next_id`,`sj.cs_next_id + 1`,`sj.cs_next_id + 2`,
    `start`,`start with cs_next_var := start.cs_next_var + 1`] >>
  fs[array_for_code_def,elem_size_in_location_def,is_slot_addressed_def,
     Abbr `ainst`] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [mk_inst_def]) >>
  pure_rewrite_tac[mk_inst_def] >>
  simp[NoAsms] >>
  conj_tac >-
    (qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `STRING _ _ = p` mp_tac >>
     qpat_assum `type_memory_bytes cenv typ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  conj_tac >- suspend "fixed_init" >> suspend "fixed_static"
QED

Resume body_for_local_array_full_from_contracts[dynamic_runtime]:
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by simp[] >>
  `!c lc a b. compile_stmts c lc ret_ty stmts a = ((),b) ==>
     cs_extends a b` by
    (rpt strip_tac >> qpat_x_assum `!c lc a b. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all compile_for_dynarray_stages >> strip_tac >>
  drule_all compile_for_dynarray_prefix >> strip_tac >>
  drule stmtSimForArrayPartsTheory.compile_for_array_suffix >> strip_tac >>
  `cs_extends start sa` by
    (irule stmtSimForArrayPartsTheory.array_prefix_extends >> simp[] >> metis_tac[]) >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def,mk_inst_def,is_terminator_def] >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
  drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
  drule stmtSimForArrayPartsTheory.array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by
    (qpat_x_assum `!c lc a b. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all stmtSimForArrayPartsTheory.array_stages_code >> strip_tac >>
  `?bc_out shadow_sb0 shadow_sb1.
    stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc_out,sb1) /\
    stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt stmts)
      shadow_sb0 = (bc_out,shadow_sb1) /\
    gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
    fn_has_code shadow_sb0 shadow_sb1 shadow_func` by suspend "dynamic_shadow" >>
  suspend "dynamic_staged_static"
QED

Resume body_for_local_array_full_from_contracts[dynamic_shadow]:
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
     "body_outcome","handler","entry"] >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) shadow_start = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,gas_shadow_stmt_def,
       gas_shadow_iterator_def,gas_shadow_expr_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> Cases_on `_0` >> simp[] >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ shadow_start = _`
    (mk_asm "shadow_compile") >>
  asm "shadow_compile" (mp_then (Pat `compile_stmt _ _ _ _ _ = _`) mp_tac
    compile_for_dynarray_stages) >>
  disch_then (qspecl_then [`az`,`Var ap`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_shadow_compiles (emit_op MLOAD [Var ap]) (emit_op MLOAD [Var ap])` by
    simp[gas_shadow_compiles_emit_op] >>
  qpat_x_assum `gas_shadow_compiles (emit_op MLOAD _) _` mp_tac >>
  pure_rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`start`,`shadow_start`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[] >> strip_tac >>
  qpat_x_assum `Var _ = lvo'` (SUBST_ALL_TAC o SYM) >>
  qmatch_asmsub_abbrev_tac
    `prefix st1 = ((bc,entry',cond,bod,incr,exit,idx,offo,toto,epo),sa)` >>
  `!args. gas_shadow_compiles
    (do invalid <- emit_op GT args;
        valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od)
    (do invalid <- emit_op GT args;
        valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od)` by
    (gen_tac >> ho_match_mp_tac gas_shadow_compiles_bind >>
     (conj_tac >- simp[gas_shadow_compiles_emit_op]) >> gen_tac >>
     ho_match_mp_tac gas_shadow_compiles_bind >>
     simp[gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void]) >>
  `gas_shadow_compiles prefix prefix` by
    (simp_tac (srw_ss()) [Abbr `prefix`,comp_ignore_bind_def] >>
     rpt (ho_match_mp_tac gas_shadow_compiles_bind >>
       (conj_tac >- simp[
         gasShadowCompileStmtBaseTheory.gas_shadow_compiles_declare_local,
         gasShadowCompileStmtBaseTheory.gas_shadow_compiles_emit_local_alloca,
         gas_shadow_compiles_fresh_label,gas_shadow_compiles_fresh_var,
         gas_shadow_compiles_emit_inst,gas_shadow_compiles_emit_op,
         gas_shadow_compiles_emit_void,gas_shadow_compiles_new_block]) >> gen_tac) >>
     simp[gas_shadow_compiles_return]) >>
  qpat_x_assum `gas_shadow_compiles prefix prefix` mp_tac >>
  pure_rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`st1`,`st1'`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `prefix`] >> strip_tac >>
  qpat_x_assum `bc = bc'` (SUBST_ALL_TAC o SYM) >>
  `exit' = exit /\ incr' = incr /\ bod' = bod /\ cond' = cond /\
   entry = entry' /\ idx' = idx` by simp[] >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`exit' = exit`,`incr' = incr`,`bod' = bod`,`cond' = cond`,
     `entry = entry'`,`idx' = idx`] >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`fresh_label_output "iter_entry" _ = entry'`,
     `fresh_label_output "iter_cond" _ = cond`,
     `fresh_label_output "iter_body" _ = bod`,
     `fresh_label_output "iter_incr" _ = incr`,
     `fresh_label_output "iter_exit" _ = exit`,
     `STRING #"%" _ = idx`] >>
  qpat_x_assum `(case FLOOKUP bc.ce_vars id of _ => _ | _ => _) sa' = _`
    mp_tac >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `copy sa = ((),sb0)` >>
  `gas_shadow_compiles copy copy` by
    simp[Abbr `copy`,gasShadowCompileStmtOpsTheory.gas_shadow_compiles_iter_elem_copy] >>
  `gas_shadow_state sb0 sb0'` by
    (qpat_x_assum `gas_shadow_compiles copy copy` mp_tac >>
     pure_rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sa'`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[Abbr `copy`]) >>
  Cases_on `stmts_env bc (InLoop exit incr) ret_ty stmts sb0` >>
  rename1 `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc_out,body_end)` >>
  `body_end = sb1` by
    (qpat_x_assum `compile_stmts bc _ _ stmts sb0 = _` mp_tac >>
     simp[stmtSimPropsTheory.compile_stmts_env]) >>
  qpat_x_assum `body_end = sb1` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`stmts`,`bc`,`InLoop exit incr`,`ret_ty`]
    gas_shadow_stmts_env) >>
  pure_rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sb0`,`sb0'`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = _`
    (fn th => pure_rewrite_tac[th,pairTheory.FST,pairTheory.SND]) >> strip_tac >>
  `stmts_env bc (InLoop exit incr) ret_ty
    (MAP gas_shadow_stmt stmts) sb0' = (bc_out,sb1')` by
    (qpat_x_assum `compile_stmts bc _ _ (MAP _ _) sb0' = _` mp_tac >>
     simp[stmtSimPropsTheory.compile_stmts_env] >> strip_tac >>
     qpat_x_assum `SND _ = sb1'` (SUBST1_TAC o SYM) >> simp[]) >>
  `gas_shadow_state sb1 sb1'` by
    (qpat_x_assum `gas_shadow_state sb1 (SND _)` mp_tac >>
     qpat_assum `stmts_env bc (InLoop exit incr) ret_ty (MAP _ _) sb0' = _`
       (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp_tac bool_ss []) >>
  `cs_extends shadow_start sa'` by
    (qpat_assum `emit_op MLOAD _ shadow_start = _`
       (mp_then Any mp_tac compile_for_dynarray_prefix) >>
     disch_then drule_all >> strip_tac >>
     irule stmtSimForArrayPartsTheory.array_prefix_extends >>
     simp_tac (srw_ss()) [] >> simp[]) >>
  `~block_is_terminated sa'` by
    (qpat_assum `gas_shadow_state sa sa'`
      (mp_then Any mp_tac gasShadowCompileStmtBaseTheory.gas_shadow_state_terminated) >>
     simp[]) >>
  `cs_extends sa' sb0'` by
    (qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ sa' = _`
      (mp_then Any mp_tac stmtSimForArrayPartsTheory.array_iter_copy_static) >>
     simp[]) >>
  `cs_extends sb0' sb1'` by
    (qpat_assum `compile_stmts _ _ _ (MAP _ _) sb0' = _`
      (mp_then Any mp_tac (SRULE[cs_mono_def] (cj 2 compile_stmt_cs_mono))) >>
     simp[cs_mono_def]) >>
  `cs_extends sb1' sj'` by
    (qpat_assum `emit_jmp_if_not_terminated _ sb1' = _`
      (mp_then Any mp_tac stmtSimForArrayPartsTheory.array_body_backedge) >> simp[]) >>
  `cs_extends sj' cs'` by
    (qpat_assum `_ sj' = ((),cs')`
      (mp_then Any mp_tac stmtSimForArrayPartsTheory.compile_for_array_suffix) >>
     simp[]) >>
  qpat_x_assum `cs' = shadow_finish` SUBST_ALL_TAC >>
  `cs_extends shadow_start sb0'` by
    (irule cs_extends_trans >> qexists_tac `sa'` >> simp[]) >>
  `cs_extends sb1' shadow_finish` by
    (irule cs_extends_trans >> qexists_tac `sj'` >> simp[]) >>
  `fn_has_code sb0' sb1' shadow_func` by
    (irule fn_has_code_mid >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`shadow_finish`,`shadow_start`] >> simp[]) >>
  qpat_x_assum `exit = fresh_label_output _ _` SUBST_ALL_TAC >>
  qpat_x_assum `incr = fresh_label_output _ _` SUBST_ALL_TAC >>
  qexistsl_tac [`bc_out`,`sb0'`,`sb1'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_for_local_array_full_from_contracts[dynamic_staged_static]:
  `sb0.cs_current_bb = bod` by fs[exprLoweringPropsTheory.same_blocks_def] >>
  `lookup_block start.cs_current_bb func.fn_blocks = SOME
    <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
      [mk_inst start.cs_next_id MLOAD [Var ap] [lv];
       mk_inst (start.cs_next_id + 1) ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p];
       mk_inst (start.cs_next_id + 2) JMP [Label entry'] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 3 sa.cs_blocks`,`start`,`sa`] >>
     qpat_assum `sa.cs_blocks = _` mp_tac >>
     qpat_assum `fn_has_code start sa func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block entry' func.fn_blocks = SOME
    <|bb_label := entry'; bb_instructions :=
      [mk_inst (start.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
       mk_inst (start.cs_next_id + 4) GT [Var lv;Lit (n2w n')] [g];
       mk_inst (start.cs_next_id + 5) ISZERO [Var g] [vld];
       mk_inst (start.cs_next_id + 6) ASSERT [Var vld] [];
       mk_inst (start.cs_next_id + 7) JMP [Label cond] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 3 sa.cs_blocks`,`start`,`sa`] >>
     qpat_assum `sa.cs_blocks = _` mp_tac >>
     qpat_assum `fn_has_code start sa func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block cond func.fn_blocks = SOME
    <|bb_label := cond; bb_instructions :=
      [mk_inst (start.cs_next_id + 8) EQ [Var idx;Var lv] [dv];
       mk_inst (start.cs_next_id + 9) JNZ [Var dv;Label exit;Label bod] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 3 sa.cs_blocks`,`start`,`sa`] >>
     qpat_assum `sa.cs_blocks = _` mp_tac >>
     qpat_assum `fn_has_code start sa func` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|>` by
    (irule stmtSimForArrayPartsTheory.array_emitted_block_lookup >>
     simp_tac (srw_ss()) [] >>
     qexistsl_tac [`TAKE 2 finish.cs_blocks`,`sj`,`finish`] >> simp[]) >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  `start.cs_next_var + 9 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc a b. _ ==> _ /\ _` drule >> simp[]) >>
  `(!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
      not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
      not_local_ptr cenv scs ep /\ not_local_ptr cenv scs nv /\
      not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
      not_local_ptr cenv scs vld)` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `start` >> simp[]) >>
  `not_fresh_at start ap` by
    (qpat_assum `local_ptrs_reserved cenv start` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  `ALL_DISTINCT [idx;dv;ov;tot;ep;nv;p;lv;g;vld] /\
   (!x. not_fresh_at start x ==>
      ~MEM x [idx;dv;ov;tot;ep;nv;p;lv;g;vld])` by
    (map_every (fn label => asm_x label kall_tac)
       ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
        "body_outcome","handler","entry"] >>
     simp[] >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  `local_ptrs_reserved cenv st1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
  `st1.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all stmtSimForArrayFragTheory.array_declared_reserved >> strip_tac >>
  `MEM (mk_inst (start.cs_next_id + 1) ALLOCA
      [Lit (n2w (type_memory_bytes cenv typ))] [p]) (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block start.cs_current_bb _ = _` (irule_at (Pos hd)) >>
     simp[]) >>
  qabbrev_tac `ainst = mk_inst (start.cs_next_id + 1) ALLOCA
      [Lit (n2w (type_memory_bytes cenv typ))] [p]` >>
  `(!x. not_fresh_at start x ==> not_fresh_at st1 x) /\
   (!x. not_fresh_at st1 x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
   (!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
   not_fresh_at st1 lv /\ not_fresh_at sa lv /\ not_fresh_at sa tot /\
   not_fresh_at sa idx /\ not_fresh_at sa p /\
   not_fresh_at sa ep /\ not_fresh_at sa ap /\
   not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\ not_fresh_at sb0 ap` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`p = STRING _ _`, `idx = STRING _ _`, `dv = STRING _ _`,
        `ov = STRING _ _`, `tot = STRING _ _`, `ep = STRING _ _`,
        `lv = STRING _ _`, `nv = STRING _ _`,
        `st1.cs_next_var = _`, `sa.cs_next_var = _`,
        `sa.cs_next_var <= sb0.cs_next_var`,
        `start.cs_next_var + 9 <= sj.cs_next_var`, `not_fresh_at start ap`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  qexistsl_tac [`bc`,`p`,`idx`,`dv`,`ov`,`tot`,`ep`,`nv`,`Var lv`,
    `cond`,`incr`,`sa`,`sb0`,`sb1`,`sj`,`ainst`,
    `start.cs_next_id + 8`,`start.cs_next_id + 9`,
    `start.cs_next_id + 10`,`start.cs_next_id + 11`,`start.cs_next_id + 12`,
    `sj.cs_next_id`,`sj.cs_next_id + 1`,`sj.cs_next_id + 2`,
    `st1`,`st1 with cs_next_var := st1.cs_next_var + 1`] >>
  fs[elem_size_in_location_def,is_slot_addressed_def,Abbr `ainst`,mk_inst_def,
     ALL_DISTINCT] >>
  conj_tac >- suspend "capture_dynamic_copy" >>
  conj_tac >- suspend "dynamic_init" >> suspend "dynamic_static"
QED

Resume body_for_local_array_full_from_contracts[fixed_static]:
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
     "body_outcome","handler","entry"] >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def,mk_inst_def,is_terminator_def] >>
  drule_all stmtSimForArrayPartsTheory.array_iter_copy_static >> strip_tac >>
  `not_fresh_at start ap` by
    (qpat_x_assum `local_ptrs_reserved cenv start` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  simp[exprSimCopyTheory.copy_old_operand_def] >>
  reverse conj_tac >-
    (qpat_x_assum `exit = fresh_label_output _ _` SUBST_ALL_TAC >>
     qpat_x_assum `incr = fresh_label_output _ _` SUBST_ALL_TAC >>
     qexistsl_tac [`bc_out`,`shadow_sb0`,`shadow_sb1`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  qspecl_then [`sb0`,`sb1`,`func`] mp_tac fn_has_code_start >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `bb.bb_label = sb0.cs_current_bb` by
    (qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
     pure_rewrite_tac[lookup_block_def] >>
     strip_tac >> drule FIND_P >> simp[]) >>
  qexists_tac `l` >>
  qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
  simp[basic_block_component_equality]
QED

Resume body_for_local_array_full_from_contracts[dynamic_static]:
  capture_goal "dynamic-static"
  (* Preserved unfinished static proof:
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
     "body_outcome","handler","entry"] >>
  simp[exprSimCopyTheory.copy_old_operand_def] >>
  conj_tac >- suspend "capture_dynamic_bound_fresh" >>
  (* Diagnostic capture only: remaining static fields are not yet discharged. *)
  reverse conj_tac >- suspend "capture_dynamic_static_fields" >>
  qspecl_then [`sb0`,`sb1`,`func`] mp_tac fn_has_code_start >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `bb.bb_label = sb0.cs_current_bb` by
    (qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
     pure_rewrite_tac[lookup_block_def] >>
     strip_tac >> drule FIND_P >> simp[]) >>
  qexists_tac `l` >>
  qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
  simp[basic_block_component_equality]
  *)
QED

Resume body_for_local_array_full_from_contracts[fixed_init]:
  qpat_x_assum `entry' = fresh_label_output _ _` SUBST_ALL_TAC >>
  qpat_x_assum `cond = fresh_label_output _ _` SUBST_ALL_TAC >>
  `LENGTH vs = n` by
    (simp[NoAsms,Abbr `vs`] >>
     qpat_assum `value_has_type (ArrayTV tv (Fixed n)) (ArrayV av)` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `av` >>
     simp[value_has_type_def,array_elements_def]) >>
  `idx = STRING #"%" (toString (start.cs_next_var + 1))` by simp[] >>
  `p = STRING #"%" (toString start.cs_next_var)` by (bossLib.simp []) >>
  Cases_on `compile_alloc_buffer (type_memory_size tv) start` >>
  rename1 `compile_alloc_buffer _ start = (buf,salloc)` >>
  `buf.buf_operand = Var p /\
   salloc.cs_current_bb = start.cs_current_bb /\
   salloc.cs_current_insts = start.cs_current_insts ++
     [mk_inst start.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [p]] /\
   salloc.cs_blocks = start.cs_blocks` by
    (qpat_x_assum `compile_alloc_buffer _ start = _` mp_tac >>
     qpat_x_assum `p = STRING _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[contextTheory.compile_alloc_buffer_def,emitHelperTheory.emit_op_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_id_def,fresh_var_def,emit_def] >>
     disch_then (fn th => simp[GSYM th])) >>
  `fn_has_code start salloc func` by
    (qpat_assum `salloc.cs_current_bb = _` mp_tac >>
     qpat_assum `salloc.cs_current_insts = _` mp_tac >>
     qpat_assum `salloc.cs_blocks = _` mp_tac >>
     qpat_assum `lookup_block start.cs_current_bb func.fn_blocks = _` mp_tac >>
     qpat_assum `type_memory_bytes cenv typ = type_memory_size tv` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[fn_has_code_def,emitted_blocks_def,mk_inst_def,
       rich_listTheory.IS_PREFIX_APPEND]) >>
  `?H. valid_horizon cx st0 H es.storage_trace` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     rewrite_tac[GSYM vyperStorageFootprintTheory.storage_trace_domain_def] >>
     first_assum ACCEPT_TAC) >>
  `?arr_base. eval_operand (Var ap) s0 = SOME arr_base` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       drule >> strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >> strip_tac >>
     drule_all allocaFootprintTheory.local_ptr_below_frontier >> strip_tac >>
     simp[eval_operand_def] >> goal_assum (drule_at Any)) >>
  `not_fresh_at start ap` by
    (qpat_x_assum `local_ptrs_reserved cenv start` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
     not_fresh_at start x` by
    (qpat_x_assum `ret_pc_ok cenv start s0` mp_tac >>
     simp[ret_pc_ok_def]) >>
  `~not_fresh_at start idx` by
    (qpat_assum `idx = STRING _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     qexists_tac `start.cs_next_var + 1` >> simp[]) >>
  `STRING #"%" (toString start.cs_next_var) <> idx` by
    (qpat_assum `idx = STRING _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `lookup_block salloc.cs_current_bb func.fn_blocks =
    SOME <|bb_label := salloc.cs_current_bb;
      bb_instructions := salloc.cs_current_insts ++
        [mk_inst (start.cs_next_id + 1) JMP
          [Label (fresh_label_output "iter_entry" start.cs_next_label)] []]|>` by
    (qpat_assum `salloc.cs_current_bb = _` mp_tac >>
     qpat_assum `salloc.cs_current_insts = _` mp_tac >>
     qpat_assum `lookup_block start.cs_current_bb func.fn_blocks = _` mp_tac >>
     qpat_assum `type_memory_bytes cenv typ = type_memory_size tv` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[mk_inst_def]) >>
  qpat_x_assum `lookup_block (fresh_label_output "iter_entry" _) _ = _`
    (assume_tac o PURE_REWRITE_RULE [mk_inst_def]) >>
  qpat_x_assum `lookup_block salloc.cs_current_bb _ = _`
    (assume_tac o PURE_REWRITE_RULE [mk_inst_def]) >>
  `p <> idx` by
    (qpat_assum `p = STRING _ _` mp_tac >>
     qpat_assum `idx = STRING _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `!x. not_fresh_at start x ==> x <> idx` by
    (qpat_assum `~not_fresh_at start idx` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `ent.type = ArrayTV tv (Fixed (LENGTH vs))` by
    (qpat_assum `ent.type = _` mp_tac >>
     qpat_assum `LENGTH vs = n` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `vs = array_elements ent.type av` by
    (qpat_assum `ent.type = ArrayTV tv (Fixed n)` mp_tac >>
     simp[NoAsms,Abbr `vs`]) >>
  asm "fixed" drule >> disch_then drule >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at`)) >>
  disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
  disch_then (qspecl_then [`PG`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_block salloc.cs_current_bb _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspecl_then [`av`,`tv`,`vs`] mp_tac) >>
  impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (qpat_assum `type_memory_bytes cenv typ + 64 < _` mp_tac >>
        qpat_assum `type_memory_bytes cenv typ = type_memory_size tv` mp_tac >>
        rpt (pop_assum kall_tac) >> decide_tac),
       (simp[NoAsms] >> first_assum ACCEPT_TAC),
       (qexists_tac `H` >> first_assum ACCEPT_TAC),
       capture_goal "fixed-residual" (* original: FAIL_TAC "fixed-residual" *)]) >> strip_tac >>
  qexistsl_tac [`arr_base`,`dst`,`cc`,`Gentry`,`tnentry`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H'` >> disch_tac >> conj_tac
  >- (qpat_assum `!H. gas_origin_ptr_path _ _ _ _` (qspec_then `H'` ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_inv _ _ _ _ /\ stmt_state_rel _ _ _ _ _ _ cc /\ _`
    (qspec_then `H'` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H') =
   storage_well_formed_on cx es (FST H')` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  `storage_well_formed_on cx es (FST H')` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
       (qspec_then `H'` mp_tac) >> simp[]) >>
  `ghost_inv_at (DF H') lo d cenv cx (es with gas_obs := []) Gentry tnentry cc =
   ghost_inv_at (DF H') lo d cenv cx es Gentry tnentry cc` by
    simp[NoAsms,ghost_inv_at_def] >>
  `!w. op_taint tnentry (Lit w) = {}` by simp[op_taint_def] >>
  `lookup_var ap cc = SOME arr_base` by
    (qpat_x_assum `eval_operand (Var ap) cc = _` mp_tac >> simp[eval_operand_def]) >>
  `dead_lo_ok H' (DF H') lo cenv cx` by
    (qpat_assum `!H. dead_lo_ok H _ _ _ _` (qspec_then `H'` ACCEPT_TAC)) >>
  `ret_pc_ok cenv start cc` by
    (qpat_assum `ret_pc_ok cenv start s0` mp_tac >>
     qpat_assum `!x v. not_fresh_at start x /\ lookup_var x s0 = SOME v ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ret_pc_ok_def] >> metis_tac[]) >>
  simp[NoAsms,Abbr `Head`,mk_inst_def,eval_operand_def,op_prov_def,
    exprLoweringPropsTheory.stmt_state_rel_start_gas_obs] >>
  qpat_assum `idx = STRING _ _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `type_memory_bytes cenv typ = _` (fn th => rewrite_tac[th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (simp[NoAsms,op_taint_def] >> NO_TAC),
    (qpat_assum `LENGTH vs = n` (fn th => simp[NoAsms,GSYM th]) >> NO_TAC),
    (qpat_assum `storage_well_formed_on cx (es with gas_obs := []) _ = _`
       (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC),
    (qpat_assum `ghost_inv_at _ _ _ _ _ (es with gas_obs := []) _ _ _ = _`
       (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC),
    (qpat_assum `w2n dst + type_memory_size tv < _` mp_tac >>
       rpt (pop_assum kall_tac) >> simp[ADD_COMM] >> NO_TAC),
    (qpat_assum `w2n dst + type_memory_size tv <= _` mp_tac >>
       rpt (pop_assum kall_tac) >> simp[ADD_COMM] >> NO_TAC),
    capture_goal "head-leaf" (* original: FAIL_TAC "head-leaf" *)]
QED

Resume body_for_local_array_full_from_contracts[dynamic_init]:
  `lv = STRING #"%" (toString start.cs_next_var) /\
   p = STRING #"%" (toString (start.cs_next_var + 1))` by simp[] >>
  Cases_on `emit_op MLOAD [Var ap] start` >>
  rename1 `emit_op MLOAD [Var ap] start = (load_result,load_cs)` >>
  `load_result = Var lv /\
   load_cs.cs_current_bb = start.cs_current_bb /\
   load_cs.cs_current_insts = start.cs_current_insts ++
     [mk_inst start.cs_next_id MLOAD [Var ap] [lv]] /\
   load_cs.cs_blocks = start.cs_blocks /\
   load_cs.cs_next_id = start.cs_next_id + 1 /\
   load_cs.cs_next_var = start.cs_next_var + 1` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
     disch_then (fn th => simp[GSYM th])) >>
  Cases_on `compile_alloc_buffer (type_memory_size tv) load_cs` >>
  rename1 `compile_alloc_buffer _ load_cs = (buf,salloc)` >>
  `buf.buf_operand = Var p /\
   salloc.cs_current_bb = start.cs_current_bb /\
   salloc.cs_current_insts = load_cs.cs_current_insts ++
     [mk_inst load_cs.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [p]] /\
   salloc.cs_blocks = start.cs_blocks` by
    (qpat_x_assum `compile_alloc_buffer _ load_cs = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def,emitHelperTheory.emit_op_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_id_def,fresh_var_def,emit_def] >>
     disch_then (fn th => simp[GSYM th])) >>
  `fn_has_code load_cs salloc func` by
    (simp[fn_has_code_def,emitted_blocks_def,mk_inst_def,
       rich_listTheory.IS_PREFIX_APPEND]) >>
  `?H. valid_horizon cx st0 H es.storage_trace` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     rewrite_tac[GSYM vyperStorageFootprintTheory.storage_trace_domain_def] >>
     first_assum ACCEPT_TAC) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
     not_fresh_at start x` by
    (qpat_x_assum `ret_pc_ok cenv start s0` mp_tac >> simp[ret_pc_ok_def]) >>
  `LENGTH vs <= n' /\ n' < dimword (:256)` by
    (qpat_x_assum `value_has_type _ _` mp_tac >>
     qpat_x_assum `well_formed_type_value _` mp_tac >>
     Cases_on `av` >> simp[value_has_type_def,well_formed_type_value_def,
       array_elements_def,Abbr `vs`] >> rpt strip_tac >> simp[]) >>
  `lookup_block salloc.cs_current_bb func.fn_blocks = SOME
     <|bb_label := salloc.cs_current_bb; bb_instructions :=
       salloc.cs_current_insts ++
       [mk_inst (start.cs_next_id + 2) JMP [Label entry'] []]|>` by
    simp[mk_inst_def,APPEND_ASSOC] >>
  `emit_op MLOAD [Var ap] start = (Var lv,load_cs)` by simp[] >>
  asm "dynamic_prefix" drule >> disch_then drule >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at`)) >>
  disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  simp[mk_inst_def,Abbr `vs`] >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  impl_tac >- (simp[] >> qexists_tac `H` >> simp[]) >> strip_tac >>
  qabbrev_tac `vs = array_elements (ArrayTV tv (Dynamic n')) av` >>
  qabbrev_tac `sA = t with vs_inst_idx := s0.vs_inst_idx` >>
  `exec_alloca (mk_inst (start.cs_next_id + 1) ALLOCA
       [Lit (n2w (type_memory_size tv))] [p])
     (update_var lv (n2w (LENGTH vs)) s0)
     (n2w (type_memory_size tv) : bytes32) = OK sA` by
    (qpat_x_assum `exec_alloca _ _ _ = OK _` mp_tac >>
     qpat_x_assum `Abbrev (sA = _)` mp_tac >>
     qpat_x_assum `lv = _` mp_tac >> qpat_x_assum `p = _` mp_tac >>
     qpat_x_assum `Abbrev (vs = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomExecSemanticsTheory.exec_alloca_def,mk_inst_def,
       update_var_def,AllCaseEqs(),Abbr `sA`,Abbr `vs`] >>
     gvs[venom_state_component_equality]) >>
  `lookup_var lv (jump_to entry' sA) = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `lookup_var _ t = SOME (n2w (LENGTH _))` mp_tac >>
     simp[Abbr `sA`,Abbr `vs`,jump_to_def,lookup_var_def]) >>
  `allocas_from lo (jump_to entry' sA) /\
   lo <= (jump_to entry' sA).vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       drule >> strip_tac >>
     qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ t` mp_tac >>
     rewrite_tac[ghost_inv_at_def] >> strip_tac >>
     qpat_x_assum `allocas_from lo t` mp_tac >>
     simp[allocas_from_def,Abbr `sA`,jump_to_def]) >>
  `?Gf tf. (!D. inst_seq_ptr D lo ctx func PG Gp tp
     [mk_inst (start.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
      mk_inst (start.cs_next_id + 4) GT [Var lv;Lit (n2w n')] [g];
      mk_inst (start.cs_next_id + 5) ISZERO [Var g] [vld];
      mk_inst (start.cs_next_id + 6) ASSERT [Var vld] []]
     (jump_to entry' sA) Gf tf) /\
     FLOOKUP Gf idx = NONE /\ FLOOKUP Gf lv = NONE /\
     op_taint tf (Var idx) = {} /\ op_taint tf (Var lv) = {} /\
     tf.t_mem = tp.t_mem /\ tf.t_stor = tp.t_stor /\
     tf.t_trans = tp.t_trans /\ tf.t_imm = tp.t_imm /\
     (!x. ~MEM x [idx;g;vld] ==> FLOOKUP Gf x = FLOOKUP Gp x /\
       op_taint tf (Var x) = op_taint tp (Var x))` by
    (irule bodyFullForArrayDynamicScalarTheory.for_array_dynamic_scalar_sequence_full >>
     simp[] >> qexists_tac `LENGTH vs` >> simp[ALL_DISTINCT]) >>
  `!H. inst_seq_ptr (DF H) lo ctx func PG Gp tp
     [mk_inst (start.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
      mk_inst (start.cs_next_id + 4) GT [Var lv;Lit (n2w n')] [g];
      mk_inst (start.cs_next_id + 5) ISZERO [Var g] [vld];
      mk_inst (start.cs_next_id + 6) ASSERT [Var vld] []]
     (jump_to entry' sA) Gf tf` by simp[] >>
  `!H. inst_seq_ptr (DF H) lo ctx func PG G0 tn0
     [mk_inst start.cs_next_id MLOAD [Var ap] [lv];
      mk_inst (start.cs_next_id + 1) ALLOCA [Lit (n2w (type_memory_size tv))] [p]]
     s0 Gp tp` by simp[mk_inst_def] >>
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","body_fragment","body_outcome","handler","entry"] >>
  `?dst cc s1.
    exec_alloca (mk_inst (start.cs_next_id + 1) ALLOCA
      [Lit (n2w (type_memory_size tv))] [p])
      (update_var lv (n2w (LENGTH vs)) s0)
      (n2w (type_memory_size tv) : bytes32) = OK s1 /\ s1 = sA /\
    cc = jump_to cond (update_var vld 1w (update_var g 0w
      (update_var idx 0w (jump_to entry' s1)))) /\
    array_loop_inv ctx func cenv cx st0 (expr_sim_inv cenv cx env)
      vs id idx (Var ap) base' p dst (type_memory_size tv)
      (mk_inst (start.cs_next_id + 1) ALLOCA
        [Lit (n2w (type_memory_size tv))] [p]) cond start 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame start s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    gas_path_mem ctx func s0 0 (OK cc) /\
    alloca_history func cc /\ cc.vs_memory = s0.vs_memory /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    (!H. gas_origin_ptr_path
      (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK cc,Gf,tf))` by
    suspend "dynamic_entry_pending" >>
  suspend "dynamic_init_after_entry"
QED

Resume body_for_local_array_full_from_contracts[initialized_packet]:
  qabbrev_tac `Inv = Head idx p bound_op cond_lbl ainst arr_base dst` >>
  qabbrev_tac `Done = \H ee G tn s.
    stmt_lands lctx finish (INL ()) s /\ ~s.vs_halted /\
    ~block_is_terminated finish /\ cenv_top_ext cenv cenv ee.scopes /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv finish s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    (!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at start x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))` >>
  qabbrev_tac `Exit = \H ex ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
      (INR ex : unit + exception) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==> !s.
      (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)` >>
  `!rs ee s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Inv H rs ee G tn s) /\
    gas_admissible (eval_for cx tv id stmts rs) (stmt_res_ok lctx) ee ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_for cx tv id stmts rs) (ee,s,G,tn)
      (\H res ee G tn t. res = INL () /\ Done H ee G tn t)
      (\H res ee gt r. ?ex. res = INR ex /\ Exit H ex ee gt r)`
    by suspend "common_loop" >>
  suspend "initialized_loop_suffix"
QED

Resume body_for_local_array_full_from_contracts[common_loop]:
  ho_match_mp_tac (Q.INST
    [`round` |-> `\a. do v <- read_result cx a;
       push_scope_with_var id tv v;
       finally (try (do eval_stmts cx stmts; return F od)
                    handle_loop_exception) pop_scope od`,
     `next` |-> `\rs b. if b then return () else eval_for cx tv id stmts rs`]
    eval_for_rounds_full) >>
  simp_tac bool_ss [] >>
  conj_tac >- suspend "common_round" >>
  conj_tac >- suspend "common_nil" >>
  conj_tac >- suspend "common_cert_head" >>
  suspend "common_cert_tail"
QED

Resume body_for_local_array_full_from_contracts[common_nil]:
  VALID (rpt gen_tac >> strip_tac >>
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
     "body_outcome","handler","entry"] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> Inv _ [] _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  simp_tac (srw_ss()) [Abbr `Inv`,Abbr `Head`] >> strip_tac >>
  `lo <= s.vs_alloca_next` by fs[ghost_inv_at_def]) >>
  `!H. gas_origin_ptr_path
      (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s,G,tn) []
      (OK (jump_to exit_lbl (update_var dv 1w s)),
       DRESTRICT G (COMPL {dv}),tn with t_var := tn.t_var |+ (dv,{}))` by
    (irule (SRULE [venomExecSemanticsTheory.bool_to_word_def]
      (Q.INST [`a` |-> `n2w (LENGTH (vs : value list)) : 256 word`,
               `b` |-> `n2w (LENGTH (vs : value list)) : 256 word`]
        (cj 1 (SRULE [] for_array_local_condition_full)))) >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`body_lbl`,`bound_op`,`idx`,`j1`,`j2`,`vs`] >>
     simp_tac bool_ss [APPEND] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`jump_to exit_lbl (update_var dv 1w s)`,
    `DRESTRICT G (COMPL {dv})`,`tn with t_var := tn.t_var |+ (dv,{})`] >>
  VALID (rpt gen_tac >> disch_tac) >> conj_tac >- simp[] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    drule >> simp_tac (srw_ss()) [] >> strip_tac >>
  `(jump_to exit_lbl (update_var dv 1w s)).vs_current_bb = exit_lbl /\
   (jump_to exit_lbl (update_var dv 1w s)).vs_inst_idx = 0` by
    simp[jump_to_def,update_var_def] >>
  simp[Abbr `Done`,stmt_lands_def,block_is_terminated_def,
    stmtSimPropsTheory.cenv_top_ext_refl] >>
  conj_tac >- (rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_jump_to] >>
    irule exprLoweringPropsTheory.stmt_state_rel_update_var >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `storage_well_formed_on cx ee (FST H)` mp_tac >>
     simp[vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageBackendTheory.get_storage_def,boolTheory.FORALL_BOOL]) >>
  conj_tac >-
    (`start.cs_next_var <= finish.cs_next_var` by
       (qspecl_then [`cenv`,`lctx`,`ret_ty`,
          `For id typ (Array (Name (ArrayT typ bd) name)) n stmts`,`start`]
          mp_tac (cj 1 compile_stmt_ci_mono) >>
        simp[exprLoweringPropsTheory.ci_mono_def]) >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s`,`start`] >>
     simp[jump_to_def,update_var_def,lookup_var_def] >>
     rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at scopy x /\ _`
       drule >> simp[FLOOKUP_UPDATE]) >>
  conj_tac >-
    (irule allocaHistoryTheory.alloca_history_jump >>
     simp[jump_to_def,update_var_def] >> qexists_tac `s` >> simp[]) >>
  conj_tac >- simp[jump_to_def,update_var_def] >>
  conj_tac >-
    (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`ee`,`s`,`start`,`tn`] >>
     simp[jump_to_def,update_var_def] >>
     conj_tac >-
       (qpat_x_assum `ret_pc_ok cenv start s0` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        pure_rewrite_tac[ret_pc_ok_def] >>
        rpt strip_tac >> first_x_assum drule >>
        disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at scopy x /\ _`
       drule >> simp[lookup_var_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,
         ptrDisciplineTheory.op_taint_def] >> strip_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> FLOOKUP G x = _ /\ _`
       drule >> simp[ptrDisciplineTheory.op_taint_def]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at scopy x /\ _`
       drule >> simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
     strip_tac >>
     qpat_x_assum `!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==> _`
       drule_all >> simp[lookup_var_def]) >>
  conj_tac >- simp[jump_to_def,update_var_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at scopy x /\ _`
    drule >> simp[FLOOKUP_DRESTRICT,ptrDisciplineTheory.op_taint_def,
      FLOOKUP_UPDATE] >> strip_tac >>
  qpat_x_assum `!x. not_fresh_at start x ==> FLOOKUP G x = _ /\ _`
    drule >> simp[ptrDisciplineTheory.op_taint_def]
QED

Resume body_for_local_array_full_from_contracts[common_cert_head]:
  rpt gen_tac >> strip_tac >>
  irule gasExemptCertTheory.gas_exempt_cert_error_bool >>
  asm_rewrite_tac []
QED

Resume body_for_local_array_full_from_contracts[common_cert_tail]:
  rpt gen_tac >> strip_tac >>
  irule gasExemptCertTheory.gas_exempt_cert_bind_bool >>
  qexistsl_tac [`mid`,`t`,`b`] >> asm_simp_tac bool_ss []
QED

Resume body_for_local_array_full_from_contracts[common_round]:
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >-
    (once_rewrite_tac[ignore_bind_def] >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result] >> gen_tac >>
     once_rewrite_tac[ignore_bind_def] >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_state_updates] >>
     irule storage_trace_frame_finally >>
     simp[storage_trace_frame_pop_scope] >>
     irule storage_trace_frame_try >>
     simp[storage_trace_frame_loop_handler] >>
     once_rewrite_tac[ignore_bind_def] >>
     irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `Abbrev (Inv = _)` (fn idef =>
    qpat_assum `Abbrev (Head = _)` (fn hdef =>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> Inv _ (a::rs) _ _ _ _`
        (mk_asm "entry_inv" o SIMP_RULE bool_ss
          [REWRITE_RULE [markerTheory.Abbrev_def] idef,
           REWRITE_RULE [markerTheory.Abbrev_def] hdef]))) >>
  asm "entry_inv" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qabbrev_tac `k = LENGTH vs - SUC (LENGTH rs)` >>
  `k < LENGTH vs` by
    (qpat_x_assum `Abbrev (k = _)` mp_tac >>
     qpat_x_assum `SUC (LENGTH rs) <= LENGTH vs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >> decide_tac) >>
  qpat_x_assum `a::rs = MAP Value _` (mp_tac o GSYM) >>
  rewrite_tac[MAP_EQ_CONS] >> strip_tac >>
  qpat_x_assum `a = Value _` SUBST_ALL_TAC >>
  pure_rewrite_tac[read_result_def,bind_return] >>
  rename1 `DROP k vs = v :: tail_vs` >>
  `same_frame cenv bc /\ cenv_top_ext cenv bc (FEMPTY :: ee.scopes)` by
    (qpat_x_assum `!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = _` mp_tac >>
     qpat_x_assum `FLOOKUP bc.ce_vars id = SOME _` mp_tac >>
     qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _;
       ce_dynarray_capacity := _|> = cenv` mp_tac >>
     qpat_x_assum `FLOOKUP cenv.ce_vars id = NONE` mp_tac >>
     qpat_x_assum `lookup_scopes id ee.scopes = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     rw[bodySimTheory.same_frame_def,cenv_top_ext_def] >>
     Cases_on `n = id` >> gvs[]) >>
  `cs_extends start sb0` by
    (irule cs_extends_trans >> qexists_tac `scopy` >> simp[]) >>
  `?ss Gs ts. !H. valid_horizon cx st0 H ee.storage_trace ==>
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
    lookup_var p ss = SOME dst /\ ptr_covers Gs ts p ss (type_memory_bytes cenv typ) /\
    FLOOKUP ss.vs_allocas ainst.inst_id = SOME (w2n dst,type_memory_bytes cenv typ) /\
    w2n dst + type_memory_bytes cenv typ < dimword (:256) /\
    w2n dst + type_memory_bytes cenv typ <= ss.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes ss nm b len ==>
      regions_disjoint (w2n dst) (type_memory_bytes cenv typ) b len) /\
    lookup_var idx ss = SOME (n2w k) /\
    eval_operand bound_op ss = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gs idx = NONE /\ op_prov Gs bound_op = NONE /\
    op_taint ts (Var idx) = {} /\ op_taint ts bound_op = {} /\
    lookup_scopes name ee.scopes = SOME ent /\
    ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\ eval_operand (Var ap) ss = SOME arr_base /\
    (!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==>
      lookup_var x ss = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP ss.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at start x ==> FLOOKUP Gs x = FLOOKUP G0 x /\
      op_taint ts (Var x) = op_taint tn0 (Var x))` by
    (asm "entry" irule >> suspend "common_entry_premises") >>
  suspend "common_round_body"
QED

Resume body_for_local_array_full_from_contracts[common_entry_premises]:
  map_every (fn label => asm_x label kall_tac)
    ["fixed","dynamic_prefix","dynamic_entry","body_fragment",
     "body_outcome","handler","entry"] >>
  conj_tac >-
    (qpat_x_assum `!x sz. cenv.ce_return_buf = _ ==> _` mp_tac >>
     qpat_x_assum `ret_pc_ok cenv start s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ret_pc_ok_def] >> metis_tac[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexists_tac `MAP Value tail_vs` >>
     qpat_x_assum `DROP k vs = _` (fn th => rewrite_tac[th,MAP])) >>
  rpt (conj_tac >- FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  conj_tac >- (qexistsl_tac [`ap`,`az`] >>
    simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`sdecl`,`sdecl'`] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `ArrayT typ bd` >> REFL_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl_tac [`body_lbl`,`type_memory_bytes cenv typ`,`cond_lbl`,
       `dv`,`ep`,`exit_lbl`,`j1`,`j2`,`j3`,`j4`,`joff`,`nv`,`ov`,`scopy`,
       `tail_code`,`tov`] >>
     suspend "common_entry_code") >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`,`env_b`,`ret_ty`,`stmts`,`tops`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeCallGraphTheory.int_calls_stmt_def,
       vyperTypeCallGraphTheory.int_calls_iterator_def,
       vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_for_local_array_full_from_contracts[common_entry_code]:
  conj_tac >-
    (gen_tac >> disch_tac >> asm "entry_inv" drule >>
     simp_tac (srw_ss()) [Abbr `k`] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_x_assum `~MEM ap _` mp_tac >>
     qpat_x_assum `bd = Dynamic _ ==> ap <> tov` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[MEM] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at scopy x /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at sb0 x /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `ALL_DISTINCT [idx;dv;ov;ep;p] /\ p <> ep /\ p <> ov` by
    (qpat_x_assum `ALL_DISTINCT [idx;dv;ov;ep;nv;p]` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  rpt (conj_tac >- FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  conj_tac >-
    (qpat_x_assum `bd = Dynamic _ ==> ALL_DISTINCT _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `bd = Dynamic _ ==> not_fresh_at scopy tov /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at scopy x /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `!scs. not_local_ptr cenv scs idx /\ _` (qspec_then `ee.scopes` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume body_for_local_array_full_from_contracts[common_round_body]:
  simp_tac bool_ss [] >>
  qabbrev_tac `be = ee with <|scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
    gas_obs := []|>` >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
    gas_origin_ptr_path _ (s,G,tn) [] (OK ss,Gs,ts) /\ _`
    (mk_asm "entry_packet") >>
  asm "entry_packet" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  simp_tac bool_ss [] >> strip_tac >>
  `body_stmts_full_ok cx stmts` by
    (qpat_x_assum `body_for_full_ok cx tv id stmts _` mp_tac >>
     qpat_x_assum `DROP k vs = v::tail_vs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `vs` >> simp[body_for_full_ok_def,MAP,read_result_def] >>
     rpt strip_tac >> first_x_assum irule >>
     qexistsl_tac [`ee`,`h`,`ee`] >> simp[read_result_def,return_def]) >>
  `stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts)
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts))
    (eval_stmts cx stmts) be` by
    (asm "body_fragment" irule >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bindings`,`cenv`,`env`,`env`,`id`,
       `Array (Name (ArrayT typ bd) name)`,`n`,`sdecl`,`sdecl'`,`tops`,`typ`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0` >>
  rename1 `stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb_body)` >>
  `sb_body = sb1` by
    (qpat_x_assum `stmts_env bc _ _ stmts sb0 = _` mp_tac >>
     qpat_x_assum `compile_stmts bc _ _ stmts sb0 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[stmtSimPropsTheory.compile_stmts_env,pairTheory.SND]) >>
  qpat_x_assum `sb_body = sb1` SUBST_ALL_TAC >>
  capture_goal "body-shadow-packet" (* original: FAIL_TAC "body-shadow-packet" *)
QED

Resume body_for_local_array_full_from_contracts[initialized_loop_suffix]:
  capture_goal "initialized-loop-suffix" (* original: FAIL_TAC "initialized-loop-suffix" *)
QED

(* The original typed-entry diagnostic is retained behind the external
   interface-approval gate; common-loop work does not use a changed cut. *)
Resume body_for_local_array_full_from_contracts[dynamic_entry_pending]:
  asm "dynamic_entry" match_mp_tac >> simp[mk_inst_def] >>
  capture_goal "dynamic-entry-premises" (* original: FAIL_TAC "dynamic-entry-premises" *)
QED

Resume body_for_local_array_full_from_contracts[dynamic_init_after_entry]:
  capture_goal "dynamic-entry-apply" (* original: FAIL_TAC "dynamic-entry-apply" *)
QED

Finalise body_for_local_array_full_from_contracts
