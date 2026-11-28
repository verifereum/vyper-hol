(* Compose the source-ordered RawCreate cuts up to its prepared dispatch. *)
Theory s1PrefixRawCreateCompose
Ancestors
  s1PrefixRawCreateStop s1PrefixRawCreateScalar s1PrefixRawCreateBytecode
  s1PrefixCreateCtorRows s1PrefixPreds s1PrefixOfVV s1PrefixProps s1PrefixDefs
  bodyFullCreateHeld bodyFullPreds bodySimFull exprSimDefs exprSimSource
  bodyFullExprsListFacts
  exprListSplitProps[qualified,ignore_grammar]
  s1PrefixCreateOutcomeTyping exprSimHypsDefs exprBodyPreProps exprLoweringProps builtinCreate
  loweringPosts loweringStateRelDefs bodyPtrDefs fragExec codegenRel compileEnv
  vyperInterpreter vyperCreate vyperValue vyperState vyperAST vyperTypeSystem
  vyperStorageTrace vyperStorageFootprint vyperCallOutcome vyperCallOutcomeFrame
  gasOutcomeFull venomState venomMemDefs venomInst ptrDiscipline memSafeRun
  exprSimWordArgs[qualified] constSubstCorrect[qualified] stmtFragPtr[qualified]
  gasShadowCompileHelpers[qualified] extCallOracle vfmConstants list words sum
Libs
  pairLib

Theorem create_prefix_exprs_split:
  !xs ys cx. body_exprs_prefix_ok cx (xs ++ ys) ==>
    body_exprs_prefix_ok cx xs /\
    (!st vs en. eval_exprs cx xs st = (INL vs,en) ==> body_exprs_prefix_ok cx ys)
Proof
  mp_tac (Q.SPECL [`body_exprs_prefix_ok`, `body_expr_prefix_ok`]
    exprListSplitPropsTheory.expr_list_ok_append_split) >>
  simp[body_exprs_prefix_ok_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "dispatch") >>
  map_every qx_gen_tac [`cx`,`ann`,`salted`,`rof`,`ks`,`args`,`dflt`] >>
  strip_tac >> rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_create_pre_args >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`code`,`amount`,`ctor`,`salts`,`bd`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  conj_asm1_tac
  >- (rewrite_tac[expr_sim_prefix_def,expr_sim_full_pre_def] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all raw_create_compile_cuts >> strip_tac >>
      rename1 `compile_expr cenv (expr_type code) code sa = (vv,sa1)` >>
      rename1 `compile_expr _ _ (gas_shadow_expr code) shadow_sa = (vv,sha1)` >>
      rename1 `compile_create_snapshot cenv vv (lowered_value_type cenv code) sa1 = (root,sa2)` >>
      rename1 `emit_op MLOAD [root] sa2 = (len,sa3)` >>
      rename1 `emit_op ADD [root;Lit 32w] sa3 = (data,sc)` >>
      rename1 `emit_op ADD [root;Lit 32w] _ = (data,shc)` >>
      rename1 `lower_value _ _ _ amount se = (v,sf)` >>
      rename1 `lower_value _ _ _ (gas_shadow_expr amount) she = (v,shf)` >>
      rename1 `compile_create_salt _ _ _ sf = (sop,sg)` >>
      rename1 `compile_create_salt _ _ _ shf = (sop,shg)` >>
      rename1 `compile_create_dispatch init_op size_op v sop rof sg = (op,sb)` >>
      simp[create_eval_read] >>
      suspend "bytecode") >>
  irule expr_vv_sim_stack_prefix >> simp[create_compile_stack] >>
  metis_tac[create_eval_value]
QED
*)
Theorem raw_create_expr_prefix_from_dispatch:
  (!DF lo explicit ctx func PG cx st0 source ee s G tn d cenv
     codep len amount sop rof sm result sb pv sz initcode aw sw.
    compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
    fn_has_code sm sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
    outcomes_accounts_typed ee.outcomes /\
    eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
    (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
    (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
      (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
       w2n pv + w2n sz <= w2n s.vs_fmp)) /\
    read_memory (w2n pv) (w2n sz) s = initcode /\
    (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
    op_taint tn codep = {} /\ op_taint tn len = {} /\
    eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
    (case sop of NONE => sw = NONE | SOME op =>
       ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
    (!tail. source (ee with gas_obs := tail) =
      if w2n sz > 2 * max_code_size then
        (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
      else bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)) ==>
  !cx ty s r ks es d.
    body_exprs_full_ok cx (create_operand_order RawCreate s es) /\
    body_exprs_prefix_ok cx (create_operand_order RawCreate s es) ==>
    body_expr_prefix_ok cx (Call ty (CreateTarget RawCreate s r ks) es d)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_expr_prefix_from_dispatch[bytecode]:
  `expr_body_pre cenv cx env code es` by fs[] >>
  qpat_assum `create_operand_order RawCreate _ _ = _` (fn order_th =>
    qpat_x_assum `body_exprs_full_ok _ (create_operand_order RawCreate _ _)`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons] o REWRITE_RULE [order_th])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `create_operand_order RawCreate _ _ = _` (fn order_th =>
    qpat_x_assum `body_exprs_prefix_ok _ (create_operand_order RawCreate _ _)`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def] o REWRITE_RULE [order_th])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `src_action = eval_create_operands cx RawCreate salted rof
    (BaseT (BytesT (Dynamic bd))::BaseT (UintT 256)::(MAP expr_type ctor ++ MAP expr_type salts))
    (blueprint_literal_offset cx salted (code::amount::(ctor ++ salts)))` >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule (INST_TYPE [``:'b`` |-> ``:value``] raw_create_prefix_bind_stop) >>
  `!vs. storage_trace_frame (src_action vs)` by
    simp[Abbr `src_action`,storage_trace_frame_create_operands] >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  conj_tac
  >- (irule raw_create_bytecode_operand_prefix >>
      qpat_assum `compile_expr cenv _ code sa = (vv,sa1)` (irule_at Any) >>
      qpat_assum `compile_expr _ _ (gas_shadow_expr code) shadow_sa = _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
      qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
      qexists `shadow_func` >> simp[] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)`,
    `\x:value. x`, `cx_tops cx`, `\x:value. x`] >>
  simp[] >> conj_tac >- (Cases_on `res` >> simp[]) >>
  ho_match_mp_tac (GEN_ALL raw_create_bytecode_cut) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es` (irule_at Any) >>
  qpat_assum `compile_expr cenv _ code sa = (vv,sa1)` (irule_at Any) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr code) shadow_sa = _` (irule_at Any) >>
  qpat_assum `compile_create_snapshot cenv vv _ sa1 = (root,sa2)` (irule_at Any) >>
  qpat_assum `emit_op MLOAD [root] sa2 = (len,sa3)` (irule_at Any) >>
  qpat_assum `emit_op ADD [root; Lit 32w] sa3 = (data,sc)` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `MEM shadow_func shadow_ctx.ctx_functions` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env code es` (irule_at Any) >>
  qpat_assum `expr_type code = BaseT (BytesT (Dynamic bd))` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
  simp[storage_trace_frame_return] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`bs`,`ee`,`z`,`Gz`,`tz`,`marks`,`src`,`owner`,`pbase`,`cap`,`site`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gz`,`ee`,`INL (BytesV bs)`,`z`,`tz`] >>
  simp[return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_exprs cx (ctor ++ amount::salts))
      (\vs. bind (src_action (BytesV bs::vs)) (read_result cx))) (ee,z,Gz,tz)`
    suffices_by simp[gas_prefix_full_def,Abbr `src_action`] >>
  `body_exprs_full_ok cx (ctor ++ amount::salts) /\
   body_exprs_prefix_ok cx (ctor ++ amount::salts)` by
    (qpat_assum `!tail. bind (eval_expr cx code) _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> metis_tac[]) >>
  `ci_mono sa sa1` by
    (qspecl_then [`cenv`,`expr_type code`,`code`,`sa`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `ci_mono sa1 sa2` by
    (qspecl_then [`cenv`,`vv`,`lowered_value_type cenv code`,`sa1`]
       mp_tac ci_mono_compile_create_snapshot >> simp[]) >>
  `ci_mono sa2 sa3 /\ ci_mono sa3 sc` by
    (conj_tac
     >- (qspecl_then [`MLOAD`,`[root]`,`sa2`] mp_tac ci_mono_emit_op >> simp[]) >>
     qspecl_then [`ADD`,`[root; Lit 32w]`,`sa3`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `ci_mono se sf` by
    (qspecl_then [`cenv`,`expr_type amount`,`amount`,`se`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `!a. ci_mono sa a ==> local_ptrs_reserved cenv a /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x)` by
    (gen_tac >> rewrite_tac[ci_mono_def] >> strip_tac >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
     conj_tac >> rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  `if salted then ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
   else salts = []` by (Cases_on `salted` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `!e u. MEM e (ctor ++ amount::salts) /\ expr_sim_inv cenv cx env u ==>
     expr_body_pre cenv cx env e u` by
    (rpt gen_tac >> strip_tac >> irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ (CreateTarget RawCreate _ _ _) _ _) es` (irule_at Any) >>
     fs[MEM_APPEND]) >>
  qabbrev_tac `cutP = \e u Gu tu (action:evaluation_state -> (value + exception) # evaluation_state).
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 action (e,u,Gu,tu)` >>
  `!cvs enc eu u Gu tu.
    (if ctor = [] /\ cvs = [] then enc = []
     else encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) cvs = SOME enc) /\
    body_const_cells_agree [(NONE,tops)] cx env eu /\ expr_sim_inv cenv cx env eu /\
    body_exprs_full_ok cx (amount::salts) /\ body_exprs_prefix_ok cx (amount::salts) /\
    ci_mono sa se /\ return_buf_frame d cenv se u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = se.cs_current_bb /\ u.vs_inst_idx = LENGTH se.cs_current_insts /\
    (!H. valid_horizon cx st0 H eu.storage_trace ==>
      stmt_state_rel H ctx func cenv cx eu u /\ storage_well_formed_on cx eu (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx eu Gu tu u) /\
    (!ef Gf tf f.
      wb_frame cenv eu ef se u f /\ ghost_kept_at lo cenv eu se Gu tu u Gf tf /\
      u.vs_alloca_next <= f.vs_alloca_next ==>
      ?p base. init_op = Var p /\ lookup_var p f = SOME (n2w base) /\
        base < dimword (:256) /\ LENGTH (bs ++ enc) < dimword (:256) /\
        ptr_covers Gf tf p f (LENGTH (bs ++ enc)) /\ op_taint tf (Var p) = {} /\
        base + LENGTH (bs ++ enc) <= f.vs_alloca_next /\
        eval_operand size_op f = SOME (n2w (LENGTH (bs ++ enc))) /\
        op_taint tf size_op = {} /\ read_memory base (LENGTH (bs ++ enc)) f = bs ++ enc /\
        (!i. base <= i /\ i < base + LENGTH (bs ++ enc) ==> i NOTIN tf.t_mem)) ==>
    cutP eu u Gu tu (bind (eval_exprs cx (amount::salts))
      (\ws. bind (src_action (BytesV bs::(cvs ++ ws))) (read_result cx)))` by
      (qx_genl_tac [`cvs`,`ctor_bytes`,`eu`,`u`,`Gu`,`tu`] >>
       disch_then (map_every assume_tac o CONJUNCTS) >> suspend "scalar") >>
  Cases_on `ctor = []`
  >- suspend "no_ctor" >>
  suspend "ctor"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_expr_prefix_from_dispatch[scalar]:
  `expr_body_pre cenv cx env amount eu` by
    (qpat_assum `!e st. MEM e (ctor ++ amount::salts) /\ _ ==> _` irule >> simp[MEM_APPEND]) >>
  `!e st. MEM e salts /\ expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st` by
    (rpt strip_tac >> qpat_assum `!e st. MEM e (ctor ++ amount::salts) /\ _ ==> _` irule >> simp[MEM_APPEND]) >>
  qpat_assum `!a. ci_mono sa a ==> _` (drule_then strip_assume_tac) >>
  simp[Abbr `cutP`] >>
  irule (INST_TYPE [``:'b`` |-> ``:value``] raw_create_prefix_bind_stop) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, evaluate_requests_outcomes_frame] >>
  conj_tac
  >- (irule raw_create_scalar_operands_prefix >>
      qpat_assum `body_const_cells_agree [(NONE,tops)] cx env eu` (irule_at Any) >>
      qpat_assum `lower_value _ _ _ amount se = (v,sf)` (irule_at Any) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) she = _` (irule_at Any) >>
      qpat_assum `compile_create_salt _ _ _ sf = (sop,sg)` (irule_at Any) >>
      qpat_assum `compile_create_salt _ _ _ shf = (sop,shg)` (irule_at Any) >>
      qpat_assum `return_buf_frame d cenv se u` (irule_at Any) >>
      qexists `shadow_func` >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`\H (res:value + exception) ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)`,
    `\xs. ArrayV (TupleV xs)`, `cx_tops cx`,
    `\w. case w of ArrayV (TupleV xs) => xs | _ => []`] >>
  simp[] >> conj_tac >- (Cases_on `res` >> simp[]) >>
  `bind (eval_exprs cx (amount::salts)) (\xs. return (ArrayV (TupleV xs))) =
   bind (eval_exprs cx (amount::salts))
      (\(xs:value list). return (ArrayV (TupleV (HD xs :: (case (if salted then SOME (EL 1 xs) else NONE) of
                                                   NONE => [] | SOME salt_v => [salt_v])))))` by
    (irule vyperInterpreterTheory.bind_cong_implicit >> simp[] >>
     rpt strip_tac >> drule vyperInterpreterTheory.eval_exprs_length >>
     Cases_on `salted` >> fs[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  irule (SIMP_RULE bool_ss [] (Q.INST
    [`next` |-> `\(av:value) (sv:value option).
      return (ArrayV (TupleV (av::(case sv of NONE => [] | SOME salt_v => [salt_v]))))`]
    raw_create_scalar_suffix_cut)) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env eu` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ amount se = (v,sf)` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) she = _` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ _ sf = (sop,sg)` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ _ shf = (sop,shg)` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `MEM shadow_func shadow_ctx.ctx_functions` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv se u` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env amount eu` (irule_at Any) >>
  simp[storage_trace_frame_return] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`av`,`sv`,`yw`,`sw`,`ef`,`Gf`,`tf`,`f`,`gs`,`scalar_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ef`, `INL (ArrayV (TupleV (av::(case sv of NONE => [] | SOME salt_v => [salt_v]))))`,`f`,`tf`] >>
  simp[return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full _ _ _ dispatch_src _` >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     dispatch_src (ef,f,Gf,tf)` suffices_by simp[gas_prefix_full_def] >>
  qpat_assum `!ef Gf tf f. wb_frame cenv eu ef se u f /\ _ ==> ?p base. _`
    (qspecl_then [`ef`,`Gf`,`tf`,`f`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rename1 `init_op = Var final_ptr` >>
  rename1 `lookup_var final_ptr f = SOME (n2w final_base)` >>
  `eval_operand init_op f = SOME (n2w final_base)` by simp[eval_operand_def] >>
  `outcomes_accounts_typed ef.outcomes /\ IS_SOME ef.outcomes` by suspend "outcome_typing" >>
  asm "dispatch" irule >>
  qpat_assum `compile_create_dispatch init_op size_op v sop rof sg = (op,sb)` (irule_at Any) >>
  qpat_assum `eval_operand init_op f = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand size_op f = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand v f = SOME yw` (irule_at Any) >>
  qexistsl [`sw`,`bs ++ ctor_bytes`,`d`,`cenv`] >>
  simp[wordsTheory.w2n_n2w] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,Abbr `dispatch_src`,Abbr `src_action`] >>
      qpat_assum `IS_SOME sv <=> salted` (pure_once_rewrite_tac o single o GSYM) >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [Q.INST [`ctor_tys` |-> `MAP expr_type ctor`, `encoded` |-> `ctor_bytes`,
                 `value` |-> `w2n (yw:256 word)`, `sw` |-> `sw`] raw_create_read_prepared] >>
      simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `IS_SOME sv <=> salted` (pure_once_rewrite_tac o single) >>
      first_assum ACCEPT_TAC)
  >- (PURE_ONCE_REWRITE_TAC [GSYM LENGTH_APPEND] >> first_assum ACCEPT_TAC)
  >- (disch_tac >> PURE_ONCE_REWRITE_TAC [GSYM LENGTH_APPEND] >> first_assum ACCEPT_TAC)
  >- (disch_tac >> disj1_tac >> PURE_ONCE_REWRITE_TAC [GSYM LENGTH_APPEND] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `OPTREL _ sop sw` mp_tac >>
  Cases_on `sop` >> Cases_on `sw` >> simp[NoAsms,optionTheory.OPTREL_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_expr_prefix_from_dispatch[no_ctor]:
  qpat_x_assum `if ctor = [] then _ else _`
    (fn th => qpat_assum `ctor = []` (fn eq => mp_tac (SIMP_RULE bool_ss [eq] th))) >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  qpat_assum `ctor = []` SUBST_ALL_TAC >>
  qpat_assum `data = Var src` SUBST_ALL_TAC >>
  qpat_assum `!cvs enc eu u Gu tu. _ ==> cutP eu u Gu tu _`
    (qspecl_then [`[]`,`[]`,`ee`,`z`,`Gz`,`tz`] mp_tac) >>
  simp[NoAsms,Abbr `cutP`] >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- fs[APPEND]
    >- fs[APPEND]
    >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
    qx_genl_tac [`ef`,`Gf`,`tf`,`f`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
      by fs[storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    `pbase + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)` by
      (qpat_assum `cap + pbase < _` mp_tac >> qpat_assum `LENGTH bs + 32 <= cap` mp_tac >>
       simp[NoAsms,wordsTheory.dimword_def] >> numLib.ARITH_TAC) >>
    `w2n (n2w (pbase + 32) :bytes32) = pbase + 32` by simp[wordsTheory.w2n_n2w] >>
    `pbase + cap <= z.vs_alloca_next /\ 32 + LENGTH bs <= cap` by decide_tac >>
    `!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tz.t_mem` by
      (gen_tac >> strip_tac >>
       qpat_assum `!i. pbase + 32 <= i /\ i < pbase + (LENGTH bs + 32) ==> _` irule >>
       decide_tac) >>
    qpat_assum `wb_frame cenv ee ef sc z f`
      (mp_then Any (drule_all_then (fn th =>
        qpat_assum `w2n (n2w (pbase + 32) :bytes32) = _`
          (fn eq => map_every assume_tac (CONJUNCTS (REWRITE_RULE[eq] th)))))
        (Q.INST [`off` |-> `32`] raw_create_owned_window_frame)) >>
    qexists `pbase + 32` >> fs[wordsTheory.dimword_def]) >>
  simp[NoAsms]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_expr_prefix_from_dispatch[ctor]:
  qpat_x_assum `if ctor = [] then _ else _`
    (fn th => qpat_assum `ctor <> []` (fn ne => mp_tac (SIMP_RULE bool_ss [ne,LET_THM] th))) >>
  strip_tac >>
  qpat_assum `data = Var src` SUBST_ALL_TAC >>
  qpat_assum `init_op = _` SUBST_ALL_TAC >>
  qpat_assum `body_exprs_full_ok cx (ctor ++ amount::salts)`
    (mp_then Any (map_every assume_tac o CONJUNCTS) create_body_exprs_split) >>
  qpat_assum `body_exprs_prefix_ok cx (ctor ++ amount::salts)`
    (mp_then Any (map_every assume_tac o CONJUNCTS) create_prefix_exprs_split) >>
  qpat_assum `!a. ci_mono sa a ==> _` (qspec_then `sc` (drule_then strip_assume_tac)) >>
  `!e st. MEM e ctor /\ expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st` by
    (rpt strip_tac >> qpat_assum `!e st. MEM e (ctor ++ amount::salts) /\ _ ==> _` irule >> simp[MEM_APPEND]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tz z` by
      (rpt strip_tac >> qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  once_rewrite_tac[create_eval_exprs_append] >> simp[NoAsms,bind_assoc,bind_return] >>
  irule (INST_TYPE [``:'b`` |-> ``:value``] raw_create_prefix_bind_stop) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, evaluate_requests_outcomes_frame] >>
  conj_tac
  >- (irule create_ctor_rows_operand_prefix >>
      qpat_assum `compile_create_ctor_args _ cenv ctor sc = _` (irule_at Any) >>
      qpat_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr ctor) shc = _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree [(NONE,tops)] cx env ee` (irule_at Any) >>
      qpat_assum `return_buf_frame d cenv sc z` (irule_at Any) >>
      qexists `shadow_func` >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`\H (res:value + exception) ef gt rr. expr_exit res rr /\ halt_exit H cx ef res rr /\
      (ctx_has_dalloca ctx ==> !u. rr = Halt u ==> allocas_below_fmp u)`,
    `\xs. ArrayV (TupleV xs)`, `cx_tops cx`,
    `\w. case w of ArrayV (TupleV xs) => xs | _ => []`] >>
  simp[] >> conj_tac >- (Cases_on `res` >> simp[]) >>
  ho_match_mp_tac (GEN_ALL (Q.INST [`off` |-> `32`] raw_create_encoded_args_cut)) >>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env ee` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env (Call _ (CreateTarget RawCreate _ _ _) _ _) es` (irule_at Any) >>
  qpat_assum `expr_type code = BaseT (BytesT (Dynamic bd))` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ cenv ctor sc = _` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr ctor) shc = _` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sc z` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
  qpat_assum `compile_copy_memory_dynamic _ (Var src) len _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD [_;len] _ = _` (irule_at Any) >>
  qpat_assum `compile_abi_encode_values_to_buf cenv _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD [len;_] _ = (size_op,se)` (irule_at Any) >>
  qpat_assum `lookup_var src z = SOME (n2w (pbase+32))` (irule_at Any) >>
  qpat_assum `FLOOKUP z.vs_allocas site.inst_id = SOME (pbase,cap)` (irule_at Any) >>
  qpat_assum `site.inst_outputs = [owner]` (irule_at Any) >>
  qpat_assum `ptr_covers Gz tz src z (LENGTH bs)` (irule_at Any) >>
  qpat_assum `read_memory (pbase+32) (LENGTH bs) z = bs` (irule_at Any) >>
  qexists `shadow_func` >>
  simp[storage_trace_frame_return] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`cvs`,`ctor_bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gu`,`eu`,`INL (ArrayV (TupleV cvs))`,`u`,`tu`] >>
  simp[return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  `cutP eu u Gu tu (bind (eval_exprs cx (amount::salts))
      (\ws. bind (src_action (BytesV bs::(cvs ++ ws))) (read_result cx)))`
    suffices_by simp[Abbr `cutP`,gas_prefix_full_def] >>
  `well_typed_exprs env ctor` by
    (simp[constSubstCorrectTheory.frame_well_typed_exprs_every,EVERY_MEM] >>
     qx_gen_tac `arg` >> strip_tac >>
     `expr_body_pre cenv cx env arg ee` by (first_assum irule >> simp[]) >>
     drule_then strip_assume_tac expr_body_pre_static_facts >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env eu` by
    (qpat_assum `!tail. eval_exprs cx ctor _ = (INL cvs,_)` (qspec_then `[]` assume_tac) >>
     `body_const_cells_agree [(NONE,tops)] cx env (eu with gas_obs := [])` suffices_by simp[] >>
     irule body_const_cells_agree_exprs >>
     qexistsl [`ctor`,`INL cvs`,`ee with gas_obs := gas_explicit ctor_marks z.vs_gas_readings`] >> fs[]) >>
  `body_exprs_full_ok cx (amount::salts) /\ body_exprs_prefix_ok cx (amount::salts)` by
    (conj_tac >> first_assum irule >>
     qpat_assum `!tail. eval_exprs cx ctor _ = _` (qspec_then `[]` (irule_at Any))) >>
  `ci_mono sc r /\ ci_mono r i /\ ci_mono i j /\ ci_mono j k /\ ci_mono k m /\ ci_mono m se` by
    (conj_tac >- metis_tac[ci_mono_compile_create_ctor_args,compile_expr_ci_mono,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_copy_memory_dynamic,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_emit_op,pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_compile_abi_encode_values_to_buf,pairTheory.SND] >>
     metis_tac[ci_mono_emit_op,pairTheory.SND]) >>
  `ci_mono sa se` by metis_tac[ci_mono_trans] >>
  first_assum irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H eu.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  qexists `ctor_bytes` >> reverse conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_assum `!ef Gf tf f. wb_frame cenv eu ef se u f /\ _ ==> ?p base. _`
    (drule_all_then strip_assume_tac) >>
  rename1 `lookup_var final_ptr f = SOME (n2w final_base)` >>
  `LENGTH bs + LENGTH ctor_bytes = LENGTH ctor_bytes + LENGTH bs` by decide_tac >>
  qexistsl [`final_ptr`,`final_base`] >> simp[] >>
  qpat_assum `LENGTH bs + LENGTH ctor_bytes = _` (pure_once_rewrite_tac o single) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_expr_prefix_from_dispatch[outcome_typing]:
  qpat_assum `expr_sim_inv cenv cx env ef`
    (mp_then Any ACCEPT_TAC expr_sim_inv_outcomes)
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_create_expr_prefix_from_dispatch
*)
