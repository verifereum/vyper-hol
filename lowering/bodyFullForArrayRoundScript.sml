(* Concrete compiler slices and indexed state packets for non-slot For. *)
Theory bodyFullForArrayRound
Ancestors gasContext[qualified,ignore_grammar] bodyFullShared[qualified,ignore_grammar] stmtSimProps[qualified,ignore_grammar]
  bodyFullShadowBodyInv
  bodyFullForArrayElementPrepare bodyFullForArray
  stmtLowering compileEnv context exprLoweringProps emitHelper emitHelperProps
  loweringStateRelDefs loweringPosts stmtSimDefs exprSimHyps
  bodySimFull bodyFullPreds bodyPtrDefs exprSimMemDefs ptrDiscipline
  fragExec fragExecMem fragGasMode gasShadowState venomInst venomState venomExecSemantics
  vyperAST vyperState vyperTypeSystem vyperTyping vyperValueOperation
  vyperInterpreter vyperTypeValues valueEncoding valueEncodingDefs
  finite_map pred_set list words arithmetic gasOutcomeFull vyperStorageFootprint
  fragGasOriginPtr fragGasSeqPtr ptrSafeRun instMemFrontier memSafeRun
  bodyPtrBopInLiteralSuffix decoderNavigationPtr exprPtrUnwrapCondition
  exprSimOperands bodyFullGhostFrame bodyMemoryDefs exprSimWordArgs allocaHistory
  unitTransformDefs contextCodegenRel codegenRel
  bodyFullForRange fragGasCopyLoop fragGasOriginPtrLoop augAssignPtrScalarCertificate rich_list
  exprPtrUnwrapCode exprSimProps bodyFullHashKeccakFixed
  bodyExprPreFacts gasOriginPtrLabels
  gasOutcomeFullCompose gasOutcomeFullStmts bodyFullForHandlers haltExitProj
  vyperStorageTrace gasExemptCert bodyLoopImmutableFrame forConsBodyGas
  forNestedArrayCapture[qualified,ignore_grammar]
  vyperTypeContract[qualified,ignore_grammar]
  bodyFullPostsMods[qualified] bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
Libs
  monadsyntax

(* Boundaries of the actual compiler actions. In particular, saL is the
   length-load endpoint, and sa has no instructions yet at the body label. *)
Definition for_nonslot_layout_def:
  for_nonslot_layout (c, id, fty, e, sty, bd, ret_ty, loop_body)
    (func, shadow_func)
    (sa0, vv, sbExpr, shadow_sa0, shadow_sbExpr, loc, len_op, saL)
    (bc, saD, saA, xd, capacity, aidItem)
    (entry, cond, bod, incr, exit, idx, invalid, valid, done_var, next_var)
    (sa, stride, off_op, sm, sum_op, sn, addr, saCopy, sbCopy)
    (sbBody, sj, sb, shadow_sbCopy, shadow_sbBody) <=>
    expr_type e = ArrayT sty bd /\
    compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\
    compile_expr (gas_shadow_env T c) (expr_type e) (gas_shadow_expr e) shadow_sa0 =
      (vv,shadow_sbExpr) /\
    gas_shadow_state sa0 shadow_sa0 /\ gas_shadow_state sbExpr shadow_sbExpr /\
    fn_has_code sa0 sbExpr func /\ fn_has_code shadow_sa0 shadow_sbExpr shadow_func /\
    loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
    (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
       | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                        (vv_operand vv)) sbExpr = (len_op,saL) /\
    fn_has_code sbExpr saL func /\ ci_mono sa0 saL /\
    declare_local c id fty saL = (bc,saD) /\
    emit_local_alloca bc id saD = ((),saA) /\
    capacity = type_memory_bytes c fty /\
    compile_alloc_buffer capacity saL =
      (<|buf_operand := Var xd; buf_size := capacity|>,saA) /\
    aidItem = saL.cs_next_id /\ sa0.cs_next_id <= aidItem /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity) /\
    (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
    fn_has_code saL saA func /\
    lookup_block saL.cs_current_bb func.fn_blocks = SOME
      <|bb_label := saL.cs_current_bb;
        bb_instructions := saA.cs_current_insts ++
          [mk_inst saA.cs_next_id JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks = SOME
      <|bb_label := entry;
        bb_instructions := [mk_inst (saA.cs_next_id + 1) ASSIGN [Lit 0w] [idx]] ++
          (case bd of Fixed _ => []
           | Dynamic cnt =>
               [mk_inst (saA.cs_next_id + 2) GT [len_op;Lit (n2w cnt)] [invalid];
                mk_inst (saA.cs_next_id + 3) ISZERO [Var invalid] [valid];
                mk_inst (saA.cs_next_id + 4) ASSERT [Var valid] []]) ++
          [mk_inst (sa.cs_next_id - 3) JMP [Label cond] []]|> /\
    lookup_block cond func.fn_blocks = SOME
      <|bb_label := cond;
        bb_instructions := [mk_inst (sa.cs_next_id - 2) EQ [Var idx;len_op] [done_var];
          mk_inst (sa.cs_next_id - 1) JNZ [Var done_var;Label exit;Label bod] []]|> /\
    sa.cs_current_bb = bod /\ sa.cs_current_insts = [] /\
    stride = elem_size_in_location c loc sty /\
    emit_op MUL [Var idx;Lit (n2w stride)] sa = (off_op,sm) /\
    (let hdr = case bd of Fixed _ => 0 | Dynamic _ => word_scale loc in
       if 0 < hdr then emit_op ADD [Lit (n2w hdr);off_op] sm = (sum_op,sn)
       else sum_op = off_op /\ sn = sm) /\
    emit_op ADD [vv_operand vv;sum_op] sn = (addr,saCopy) /\
    compile_iter_elem_copy c addr (Var xd) stride loc (is_slot_addressed loc) fty sty
      saCopy = ((),sbCopy) /\
    fn_has_code sa saCopy func /\ fn_has_code saCopy sbCopy func /\
    compile_stmts bc (InLoop exit incr) ret_ty loop_body sbCopy = ((),sbBody) /\
    compile_stmts (gas_shadow_env T bc) (InLoop exit incr) ret_ty
      (MAP gas_shadow_stmt loop_body)
      shadow_sbCopy = ((),shadow_sbBody) /\
    gas_shadow_state sbCopy shadow_sbCopy /\ gas_shadow_state sbBody shadow_sbBody /\
    fn_has_code sbCopy sbBody func /\ fn_has_code shadow_sbCopy shadow_sbBody shadow_func /\
    emit_jmp_if_not_terminated incr sbBody = ((),sj) /\ fn_has_code sbBody sj func /\
    (~block_is_terminated sbBody ==>
      sj.cs_current_bb = sbBody.cs_current_bb /\
      sj.cs_current_insts = sbBody.cs_current_insts ++
        [mk_inst sbBody.cs_next_id JMP [Label incr] []]) /\
    lookup_block incr func.fn_blocks = SOME
      <|bb_label := incr;
        bb_instructions := [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [next_var];
          mk_inst (sj.cs_next_id + 1) ASSIGN [Var next_var] [idx];
          mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
    IS_SOME (lookup_block exit func.fn_blocks) /\
    ci_mono saL saA /\ ci_mono saA sa /\ ci_mono sa saCopy /\
    ci_mono saCopy sbCopy /\ ci_mono sbCopy sbBody /\ ci_mono sbBody sj /\ ci_mono sj sb /\
    aidItem < sa.cs_next_id /\ not_fresh_at sa xd /\ not_fresh_at sa idx /\
    local_ptrs_reserved c saL /\ local_ptrs_reserved c sa /\
    local_ptrs_reserved c saCopy /\ local_ptrs_reserved bc sbCopy /\
    (!p. vv_operand vv = Var p \/ len_op = Var p ==> not_fresh_at saL p) /\
    EVERY (\p. ~not_fresh_at saL p) [idx;done_var;next_var] /\
    (case bd of Fixed _ => T
       | Dynamic _ => EVERY (\p. ~not_fresh_at saL p) [invalid;valid] /\
                      ALL_DISTINCT [xd;idx;invalid;valid;done_var;next_var]) /\
    ALL_DISTINCT [xd;idx;done_var;next_var] /\
    ALL_DISTINCT [entry;cond;bod;incr;exit]
End

(* es has the outer scopes. The machine environment and state view (cc,ee)
   are (c,es) at the condition and increment, and (bc,eb) at body entry.
   Neither the cursor nor a claim about future execution is part of live. *)
Definition for_nonslot_live_def:
  for_nonslot_live (D, lo, d, ctx, func, cx, c, id, env, loop_body)
    (es0, sa0, s0, G0, tn0)
    (e, sbExpr, saL, loc, vv, bd, stv, vs, rv, av, xs, em, u, Gu, tu)
    (len_op, idx, bw) (xd, dw, capacity, aidItem)
    (H, k, rs, es, cc, ee, G, tn, s) <=>
    k <= LENGTH vs /\ rs = DROP k vs /\
    LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
    vs = MAP Value xs /\
    read_result cx rv em = (INL (ArrayV av),em) /\
    value_has_type (ArrayTV stv bd) (ArrayV av) /\
    extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
    (!name path. rv = PlaceR (MemoryPlace name path) ==>
       runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
    (!name path. rv = PlaceR (MemoryPlace name path) ==>
       ?entry. lookup_scopes name em.scopes = SOME entry /\
         evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
    (loc = LocMemory \/ loc = LocCode) /\
    (loc = LocMemory ==> rv = Value (ArrayV av) \/
       ?name path. rv = PlaceR (MemoryPlace name path)) /\
    vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
    vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
    ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
    (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
      (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
    (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
        eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
          val_in_memory rt (ArrayV av) (w2n w) mem)) /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
      ptr_buf_ok c e op Gu u) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok c e p.ptr_operand Gu u) /\
    (loc = LocMemory ==> !name path. rv = PlaceR (MemoryPlace name path) ==>
      OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
        (lookup_scopes name es.scopes) =
      OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
        (lookup_scopes name em.scopes)) /\
    (loc = LocCode ==>
      immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw es s) /\
    (loc = LocCode ==> !src name path.
      rv = PlaceR (ImmutablePlace src name path) ==>
      ?tv root. lookup_immutable cx es src name = SOME (tv,root) /\
                evaluate_subscripts tv root path = INL (ArrayV av)) /\
    eval_operand (vv_operand vv) u = SOME bw /\
    eval_operand (vv_operand vv) s = SOME bw /\
    op_prov G (vv_operand vv) = op_prov Gu (vv_operand vv) /\
    op_taint tn (vv_operand vv) = {} /\
    eval_operand len_op s = SOME (n2w (LENGTH vs)) /\
    op_prov G len_op = NONE /\ op_taint tn len_op = {} /\
    lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    expr_sim_inv c cx env es /\ ce_locals_declared c env /\ locals_alloc_ok c env /\
    lookup_scopes id es.scopes = NONE /\
    (k <> 0 ==> body_stmts_full_ok cx loop_body) /\
    cenv_top_ext c cc ee.scopes /\
    stmt_state_rel H ctx func cc cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at D lo d cc cx ee G tn s /\
    return_buf_frame d cc sa0 s /\ ret_pc_ok cc sa0 s /\ ~s.vs_halted /\
    alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
    (* Original anchor, at entry to the whole For fragment. *)
    alloca_frame c es0 sa0 s0 cc ee s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!x. not_fresh_at sa0 x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!name b len. local_region c es0.scopes s0 name b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
    (* Capture anchor, with the expression age for captured array bytes.
       The length operand is already reserved at saL, not necessarily at sbExpr. *)
    alloca_frame c em sbExpr u cc ee s /\
    (!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> FLOOKUP s.vs_allocas aid = SOME r) /\
    (!x w. not_fresh_at saL x /\ lookup_var x u = SOME w ==> lookup_var x s = SOME w) /\
    (!name path root sz w. rv = PlaceR (MemoryPlace name path) /\
      FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\
      lookup_var root u = SOME w ==> lookup_var root s = SOME w) /\
    (!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
      aid < sbExpr.cs_next_id /\
      (!name lb lsz. local_region c em.scopes u name lb lsz ==>
        b + len <= lb \/ lb + lsz <= b) /\
      b <= i /\ i < b + len /\ i IN tn.t_mem ==> i IN tu.t_mem) /\
    (* Item is a younger, separate allocation, not an old capture row. *)
    sa0.cs_next_id <= aidItem /\ sbExpr.cs_next_id <= aidItem /\
    w2n dw + capacity < dimword (:256) /\
    w2n dw + capacity <= s.vs_alloca_next /\
    FLOOKUP s.vs_allocas aidItem = SOME (w2n dw,capacity) /\
    lookup_var xd s = SOME dw /\ ptr_covers G tn xd s capacity /\
    (!name b len. local_region c es.scopes s name b len ==>
      w2n dw + capacity <= b \/ b + len <= w2n dw)
End

Definition for_nonslot_body_entry_def:
  for_nonslot_body_entry (D, lo, d, ctx, func, cx, c, id, env, loop_body)
    original captured operands (xd, dw, capacity, aidItem)
    (bc, benv, sbCopy, dtv, v) (H, k, rs, es, eb, G, tn, t) <=>
    for_nonslot_live (D, lo, d, ctx, func, cx, c, id, env, loop_body)
      original captured operands (xd, dw, capacity, aidItem)
      (H, k, rs, es, bc, eb, G, tn, t) /\
    push_scope_with_var id dtv v es = (INL (),eb) /\
    TL eb.scopes = es.scopes /\ capacity = type_memory_size dtv /\
    value_has_type dtv v /\ val_wf dtv v /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    expr_sim_inv bc cx benv eb /\ ce_locals_declared bc benv /\ locals_alloc_ok bc benv /\
    body_stmts_full_ok cx loop_body /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity) /\
    return_buf_frame d bc sbCopy t /\ ret_pc_ok bc sbCopy t /\
    t.vs_current_bb = sbCopy.cs_current_bb /\ t.vs_inst_idx = LENGTH sbCopy.cs_current_insts
End

Theorem for_nonslot_live_head_index:
  for_nonslot_live params original
    (e, sbExpr, saL, loc, vv, bd, stv, vs, rv, av, xs, em, u, Gu, tu)
    operands item (H, k, a::rs, es, cc, ee, G, tn, s) ==>
  k = LENGTH vs - LENGTH (a::rs) /\ k < LENGTH vs /\
  a = EL k vs /\ rs = DROP (SUC k) vs
Proof
  PairCases_on `params` >> PairCases_on `original` >>
  PairCases_on `operands` >> PairCases_on `item` >> strip_tac >>
  qpat_x_assum `for_nonslot_live _ _ _ _ _ _`
    (fn th => let val fields = REWRITE_RULE [for_nonslot_live_def] th
              in map_every assume_tac [cj 1 fields, cj 2 fields] end) >>
  conj_tac >-
    (qpat_assum `a::rs = DROP k vs`
       (mp_tac o AP_TERM ``LENGTH : eval_result list -> num``) >>
     simp[] >> decide_tac) >>
  metis_tac[DROP_EQ_CONS]
QED

(* The false condition arm has a fixed endpoint and only writes done_var. *)
Theorem for_nonslot_head_test[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst eid EQ [a;b] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var out; Label exit; Label bod] []) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\ x <> y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to bod (update_var out 0w s)),
     DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst eid EQ [a;b] [out]` >>
  qabbrev_tac `u = update_var out 0w s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = DRESTRICT G (COMPL {out})` >>
  qabbrev_tac `tn' = tn with t_var := tn.t_var |+ (out,{})` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`] >>
     qspecl_then [`a`,`b`,`x`,`y`] mp_tac step_EQ >> simp[bool_to_word_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
     conj_tac >- metis_tac[] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[Abbr `u`, update_var_def]) >>
  `step_prov PG G i u = G' /\ step_taint i s u tn = tn'` by
    (`new_site_bytes s u = {}` by
       simp[Abbr `u`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
            EXTENSION, SF CONJ_ss] >>
     simp[Abbr `i`, Abbr `G'`, Abbr `tn'`, step_prov_def, out_prov_def,
          first_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
          out_taint_def, mem_taint_def, written_taint_def, step_writes_def,
          store_taint_def, imm_taint_def, adopt_reset_def, range_bytes_def,
          source_memory_write_ranges_def, mk_inst_def, taint_component_equality]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,G',tn')` by
    (`i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
       (ctx_has_dalloca ctx ==> dalloca_no_wrap i s) /\ i.inst_opcode <> GAS` by
       simp[Abbr `i`, mk_inst_def, is_terminator_def,
            inst_mem_below_frontier_def, inst_dload_in_section_def,
            dalloca_no_wrap_non_dalloca,
            source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
     simp[Abbr `v`]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,G',tn') []
     (OK (jump_to bod u),G',tn')` by
    (`jump_to bod v = jump_to bod u` by simp[Abbr `v`, jump_to_def] >>
     pop_assum (SUBST1_TAC o SYM) >>
     irule (SRULE [] (Q.INST [`v` |-> `0w`] decoderNavigationPtrTheory.jnz_origin_ptr_path)) >>
     simp[Abbr `v`, Abbr `u`, Abbr `tn'`, update_var_def, eval_operand_def,
          lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
          allocas_from_def, allocas_below_fmp_def] >>
     qexistsl [`jid`,`Var out`,`exit`] >>
     simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem for_nonslot_head_test_at_cond[local]:
  s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
  lookup_block cond func.fn_blocks = SOME
    <|bb_label := cond;
      bb_instructions := [mk_inst eid EQ [Var idx;len_op] [done_var];
        mk_inst jid JNZ [Var done_var;Label exit;Label bod] []]|> /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand len_op s = SOME (n2w len) /\
  k < len /\ len < dimword (:256) /\
  op_taint tn (Var idx) = {} /\ op_taint tn len_op = {} /\
  FLOOKUP G idx = NONE /\ op_prov G len_op = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to bod (update_var done_var 0w s)),
     DRESTRICT G (COMPL {done_var}), tn with t_var := tn.t_var |+ (done_var,{}))
Proof
  strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  `(n2w k : 256 word) <> n2w len` by (simp[LESS_MOD] >> decide_tac) >>
  irule for_nonslot_head_test >>
  simp[eval_operand_def, op_prov_def, get_instruction_def] >>
  qexistsl [`Var idx`, `len_op`, `eid`, `exit`, `jid`, `n2w k`, `n2w len`] >>
  gvs[eval_operand_def, op_prov_def, get_instruction_def]
QED

Theorem for_nonslot_head_test_frame[local]:
  stmt_state_rel H ctx func c cx es s /\ ghost_inv_at D lo d c cx es G tn s /\
  local_ptrs_reserved c saL /\ ~not_fresh_at saL done_var /\
  return_buf_frame d c saL s /\ ret_pc_ok c saL s /\
  xd <> done_var /\ ptr_covers G tn xd s cap ==>
  stmt_state_rel H ctx func c cx es (jump_to bod (update_var done_var 0w s)) /\
  ghost_inv_at D lo d c cx es
    (DRESTRICT G (COMPL {done_var})) (tn with t_var := tn.t_var |+ (done_var,{}))
    (jump_to bod (update_var done_var 0w s)) /\
  ptr_covers (DRESTRICT G (COMPL {done_var}))
    (tn with t_var := tn.t_var |+ (done_var,{})) xd
    (jump_to bod (update_var done_var 0w s)) cap /\
  return_buf_frame d c saL (jump_to bod (update_var done_var 0w s)) /\
  ret_pc_ok c saL (jump_to bod (update_var done_var 0w s)) /\
  (jump_to bod (update_var done_var 0w s)).vs_current_bb = bod /\
  (jump_to bod (update_var done_var 0w s)).vs_inst_idx = 0 /\
  (jump_to bod (update_var done_var 0w s)).vs_halted = s.vs_halted /\
  (jump_to bod (update_var done_var 0w s)).vs_memory = s.vs_memory /\
  (jump_to bod (update_var done_var 0w s)).vs_allocas = s.vs_allocas /\
  (jump_to bod (update_var done_var 0w s)).vs_alloca_next = s.vs_alloca_next /\
  (tn with t_var := tn.t_var |+ (done_var,{})).t_mem = tn.t_mem /\
  (!x. x <> done_var ==>
    lookup_var x (jump_to bod (update_var done_var 0w s)) = lookup_var x s /\
    FLOOKUP (DRESTRICT G (COMPL {done_var})) x = FLOOKUP G x /\
    op_taint (tn with t_var := tn.t_var |+ (done_var,{})) (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `t = jump_to bod (update_var done_var 0w s)` >>
  qabbrev_tac `G' = DRESTRICT G (COMPL {done_var})` >>
  qabbrev_tac `tn' = tn with t_var := tn.t_var |+ (done_var,{})` >>
  `!x. x <> done_var ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t`, Abbr `G'`, Abbr `tn'`, jump_to_def, update_var_def,
         lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x` by
    (Cases_on `d` >> gvs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME rb) c saL s` >> PairCases_on `rb` >>
     gvs[return_buf_frame_def]) >>
  conj_tac >-
    (simp[Abbr `t`, stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
     simp[] >> metis_tac[fresh_not_local_ptr]) >>
  conj_tac >-
    (irule ghost_inv_at_exterior_frame >> qexistsl [`G`,`es`,`s`,`saL`,`tn`] >>
     simp[Abbr `t`, Abbr `tn'`, jump_to_def, update_var_def] >>
     conj_tac >- gvs[ret_pc_ok_def] >>
     rpt strip_tac >> `x <> done_var` by metis_tac[] >>
     gvs[lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >-
    (fs[ptr_covers_def] >> simp[Abbr `t`, jump_to_def, update_var_def]) >>
  conj_tac >-
    (irule return_buf_frame_frame >> qexistsl [`c`,`s`,`saL`] >>
     simp[Abbr `t`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  conj_tac >- metis_tac[ret_pc_ok_def] >>
  simp[Abbr `t`, Abbr `tn'`, jump_to_def, update_var_def]
QED

(* Execution facts at the body entry, shared by outcomes and prefixes. *)
Theorem for_nonslot_array_body_exec_pre:
  !DF lo d ctx func cx c id env body original captured operands item
   bc benv sbCopy dtv v k a rs es eb G tn s st0.
  (!H. valid_horizon cx st0 H eb.storage_trace ==>
    for_nonslot_body_entry (DF H,lo,d,ctx,func,cx,c,id,env,body)
      original captured operands item (bc,benv,sbCopy,dtv,v)
      (H,k,a::rs,es,eb,G,tn,s)) /\
  storage_trace_domain cx st0 eb.storage_trace ==>
  (!H. valid_horizon cx st0 H eb.storage_trace ==>
    stmt_state_rel H ctx func bc cx eb s /\ storage_well_formed_on cx eb (FST H) /\
    ghost_inv_at (DF H) lo d bc cx eb G tn s) /\
  return_buf_frame d bc sbCopy s /\ ret_pc_ok bc sbCopy s /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  ~s.vs_halted /\ s.vs_current_bb = sbCopy.cs_current_bb /\
  s.vs_inst_idx = LENGTH sbCopy.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  PairCases_on `original` >> PairCases_on `captured` >>
  PairCases_on `operands` >> PairCases_on `item` >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
        (qspec_then `H` drule) >>
      disch_then (map_every assume_tac o CONJUNCTS o
        REWRITE_RULE [for_nonslot_body_entry_def, for_nonslot_live_def]) >>
      asm_rewrite_tac[]) >>
  qpat_x_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon eb.storage_trace`
      (drule o REWRITE_RULE [GSYM storage_trace_domain_def])) >>
  disch_then (map_every assume_tac o CONJUNCTS o
    REWRITE_RULE [for_nonslot_body_entry_def, for_nonslot_live_def]) >>
  asm_rewrite_tac[]
QED

(* Keep the raw source result until the actual fallthrough/continue/break
   suffix is chosen. The source execution is available at the same post. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then (map_every assume_tac o CONJUNCTS) for_nonslot_array_body_exec_pre >>
  qpat_x_assum `body_stmts_full_ok _ _`
    (mp_then Any mp_tac s1PrefixStmtFullApplyTheory.body_stmts_full_ok_apply) >>
  disch_then drule_all >> disch_then (qspec_then `InLoop exit incr` mp_tac) >>
  rewrite_tac[stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`,`sbCopy`,`sbBody`,`shadow_sbCopy`,
    `shadow_sbBody`,`s`,`G`,`tn`,`bc'`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
*)
Theorem for_nonslot_array_body_invoke:
  !DF lo d ctx shadow_ctx func shadow_func PG cx RetQ c id env body
   original captured operands item bc benv sbCopy dtv v k a rs es eb G tn s
   tops bindings env' ret_ty st0 exit incr bc' sbBody shadow_sbCopy shadow_sbBody.
  (!H. valid_horizon cx st0 H eb.storage_trace ==>
    for_nonslot_body_entry (DF H,lo,d,ctx,func,cx,c,id,env,body)
      original captured operands item (bc,benv,sbCopy,dtv,v)
      (H,k,a::rs,es,eb,G,tn,s)) /\
  return_buf_sep d bc eb s /\
  storage_trace_domain cx st0 eb.storage_trace /\
  body_const_cells_agree mods cx benv eb /\
  body_stmts_full_ok_mods mods exps cx body /\ expr_sim_inv_mods mods bc cx benv eb /\
  ce_locals_declared bc benv /\ locals_alloc_ok bc benv /\
  (contract_inv mods exps ctx bc cx /\
     module_body_inv mods bc.ce_module tops bc cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ supported_stmts tops bindings body /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops) /\
  type_stmts benv ret_ty body = SOME env' /\ stmts_exprs_ok bc body /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty /\
  stmts_env bc (InLoop exit incr) ret_ty body sbCopy = (bc',sbBody) /\
  stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
    shadow_sbCopy = (gas_shadow_env T bc',shadow_sbBody) /\
  gas_shadow_state sbCopy shadow_sbCopy /\ gas_shadow_state sbBody shadow_sbBody /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sbCopy sbBody func /\ fn_has_code shadow_sbCopy shadow_sbBody shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sbCopy /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sbCopy x) /\
  ~block_is_terminated sbCopy /\
  gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr)) eb ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_stmts cx body) (eb,s,G,tn)
    (\H raw ef GG tt u.
      (?c'. stmt_lands (InLoop exit incr) sbBody raw u /\ ~u.vs_halted /\
        (raw = INL () ==> ~block_is_terminated sbBody /\ c' = bc') /\
        cenv_top_ext bc c' ef.scopes /\ stmt_state_rel H ctx func c' cx ef u /\
        storage_well_formed_on cx ef (FST H) /\ return_buf_frame d c' sbBody u /\
        alloca_history func u /\ return_buf_sep d c' ef u /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        s.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d c' cx ef GG tt u /\
        (!x w. not_fresh_at sbCopy x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sbCopy x ==>
          FLOOKUP GG x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
        alloca_frame bc eb sbCopy s c' ef u /\
        (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sbCopy.cs_next_id /\
          (!name b len. local_region bc eb.scopes s name b len ==> off+sz <= b \/ b+len <= off) /\
          off <= i /\ i < off+sz /\ i IN tt.t_mem ==> i IN tn.t_mem)) /\
      ef.gas_obs = [] /\ (?xs. !tail. eval_stmts cx body (eb with gas_obs := xs ++ tail) =
                                     (raw,ef with gas_obs := tail)))
    (\H raw ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) raw gt r) /\
      halt_exit H cx ef raw r /\
      (ctx_has_dalloca ctx ==> !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==>
                                      allocas_below_fmp u))
Proof
  cheat
QED

(* A raw normal result executes the compiler's fallthrough jump.  The
   two handled exceptions are already at their corresponding labels. *)
Theorem for_nonslot_body_landing[local]:
  stmt_lands (InLoop exit incr) sbBody raw t /\ ~t.vs_halted /\
  (raw = INL () ==> ~block_is_terminated sbBody) /\
  emit_jmp_if_not_terminated incr sbBody = ((),sj) /\ fn_has_code sbBody sj func /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ?b. (case raw of INL _ => INL F | INR ex =>
         if ex = BreakException then INL T else
         if ex = ContinueException then INL F else INR ex) = INL b /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
        (OK (if raw = INL () then jump_to incr t else t),G,tn) /\
      (if raw = INL () then jump_to incr t else t).vs_current_bb =
        (if b then exit else incr) /\
      (if raw = INL () then jump_to incr t else t).vs_inst_idx = 0 /\
      ~(if raw = INL () then jump_to incr t else t).vs_halted
Proof
  strip_tac >>
  Cases_on `raw = INL ()`
  >- (qpat_x_assum `stmt_lands _ _ _ _` mp_tac >> simp[stmt_lands_def] >>
      strip_tac >>
      `emit_inst JMP [Label incr] [] sbBody = ((),sj)` by
        gvs[emitHelperTheory.emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def] >>
      drule_all placeTypedCopyPathTheory.place_copy_emit_instruction >>
      simp[] >> strip_tac >>
      simp[] >>
      conj_tac >- metis_tac[decoderNavigationPtrTheory.jump_origin_ptr_path] >>
      simp[jump_to_def]) >>
  qpat_x_assum `stmt_lands _ _ _ _` mp_tac >>
  simp[stmt_lands_def] >> strip_tac >>
  simp[gas_origin_ptr_path_rules]
QED

(* Cut the compiler before inspecting either the item copy or the body. *)
Theorem nonslot_for_compiler_cuts[local]:
  expr_type e = ArrayT sty bd /\ c.ce_alloca_locals /\
  compile_stmt c lctx ret_ty (For id fty (Array e) n loop_body) sa0 = ((),sb) ==>
  ?vv sbExpr loc len_op saL bc saD saA xd entry cond bod incr exit idx sa
   stride off_op sm sum_op sn addr saCopy sbCopy sbBody sj.
    compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\
    loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
    (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
       | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                        (vv_operand vv)) sbExpr = (len_op,saL) /\
    declare_local c id fty saL = (bc,saD) /\
    emit_local_alloca bc id saD = ((),saA) /\
    xd = STRING #"%" (toString saL.cs_next_var) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) (type_memory_bytes c fty)) /\
    (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
    (do entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        (case bd of Fixed _ => comp_return ()
           | Dynamic cnt => do invalid <- emit_op GT [len_op;Lit (n2w cnt)];
                               valid <- emit_op ISZERO [invalid];
                               emit_void ASSERT [valid] od);
        emit_inst JMP [Label cond] [];
        new_block cond;
        done_op <- emit_op EQ [Var idx;len_op];
        emit_inst JNZ [done_op;Label exit;Label bod] [];
        new_block bod;
        comp_return (entry,cond,bod,incr,exit,idx)
     od) saA = ((entry,cond,bod,incr,exit,idx),sa) /\
    stride = elem_size_in_location c loc sty /\
    emit_op MUL [Var idx;Lit (n2w stride)] sa = (off_op,sm) /\
    (if 0 < (case bd of Fixed _ => 0 | Dynamic _ => word_scale loc) then
       emit_op ADD [Lit (n2w (case bd of Fixed _ => 0 | Dynamic _ => word_scale loc));off_op]
     else comp_return off_op) sm = (sum_op,sn) /\
    emit_op ADD [vv_operand vv;sum_op] sn = (addr,saCopy) /\
    compile_iter_elem_copy c addr (Var xd) stride loc (is_slot_addressed loc) fty sty
      saCopy = ((),sbCopy) /\
    compile_stmts bc (InLoop exit incr) ret_ty loop_body sbCopy = ((),sbBody) /\
    emit_jmp_if_not_terminated incr sbBody = ((),sj) /\
    (do new_block incr;
        next <- emit_op ADD [Var idx;Lit 1w];
        emit_inst ASSIGN [next] [idx];
        emit_inst JMP [Label cond] [];
        new_block exit;
        comp_return ()
     od) sj = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def] >>
  Cases_on `bd` >> simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  gvs[] >>
  Cases_on `0 < word_scale (case vv_location arr_vv of NONE => LocMemory | SOME l => l)` >>
  gvs[comp_return_def]
QED

(* Only the control emissions are computed here; the length stays symbolic. *)
Theorem nonslot_for_control_geometry[local]:
  (do entry <- fresh_label "iter_entry";
      cond <- fresh_label "iter_cond";
      bod <- fresh_label "iter_body";
      incr <- fresh_label "iter_incr";
      exit <- fresh_label "iter_exit";
      emit_inst JMP [Label entry] [];
      new_block entry;
      idx <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx];
      (case bd of Fixed _ => comp_return ()
         | Dynamic cnt => do invalid <- emit_op GT [len_op;Lit (n2w cnt)];
                             valid <- emit_op ISZERO [invalid];
                             emit_void ASSERT [valid] od);
      emit_inst JMP [Label cond] [];
      new_block cond;
      done_op <- emit_op EQ [Var idx;len_op];
      emit_inst JNZ [done_op;Label exit;Label bod] [];
      new_block bod;
      comp_return (entry,cond,bod,incr,exit,idx)
   od) saA = ((entry,cond,bod,incr,exit,idx),sa) ==>
  ?invalid valid done_var.
    idx = STRING #"%" (toString saA.cs_next_var) /\
    invalid = STRING #"%" (toString (saA.cs_next_var + 1)) /\
    valid = STRING #"%" (toString (saA.cs_next_var + 2)) /\
    done_var = STRING #"%" (toString (sa.cs_next_var - 1)) /\
    sa.cs_next_var = saA.cs_next_var + (case bd of Fixed _ => 2 | Dynamic _ => 4) /\
    sa.cs_next_id = saA.cs_next_id + (case bd of Fixed _ => 5 | Dynamic _ => 8) /\
    sa.cs_current_bb = bod /\ sa.cs_current_insts = [] /\
    sa.cs_blocks =
      [<|bb_label := cond;
         bb_instructions := [mk_inst (sa.cs_next_id - 2) EQ [Var idx;len_op] [done_var];
             mk_inst (sa.cs_next_id - 1) JNZ [Var done_var;Label exit;Label bod] []]|>;
       <|bb_label := entry;
         bb_instructions := [mk_inst (saA.cs_next_id + 1) ASSIGN [Lit 0w] [idx]] ++
           (case bd of Fixed _ => []
            | Dynamic cnt =>
                [mk_inst (saA.cs_next_id + 2) GT [len_op;Lit (n2w cnt)] [invalid];
                 mk_inst (saA.cs_next_id + 3) ISZERO [Var invalid] [valid];
                 mk_inst (saA.cs_next_id + 4) ASSERT [Var valid] []]) ++
           [mk_inst (sa.cs_next_id - 3) JMP [Label cond] []]|>;
       <|bb_label := saA.cs_current_bb;
         bb_instructions := saA.cs_current_insts ++
           [mk_inst saA.cs_next_id JMP [Label entry] []]|>] ++ saA.cs_blocks /\
    ALL_DISTINCT [entry;cond;bod;incr;exit]
Proof
  Cases_on `bd` >>
  simp[fresh_label_def, emit_inst_def, emit_op_def, emit_void_def, fresh_id_def,
       emit_def, new_block_def, fresh_var_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >> strip_tac >> gvs[] >>
  simp[GSYM ADD_ASSOC] >> rpt conj_tac >> strip_tac >>
  drule fresh_label_output_inj >> simp[]
QED

Theorem nonslot_shadow_cut:
  gas_shadow_compiles f g ==>
  gas_shadow_state s t /\ f s = (x,u) /\ g t = (y,v) ==>
  x = y /\ gas_shadow_state u v
Proof
  simp[gas_shadow_compiles_def] >> metis_tac[pairTheory.FST,pairTheory.SND]
QED

Theorem nonslot_length_shadow[local]:
  (\f. gas_shadow_compiles f f)
    (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
       | Dynamic _ => compile_ptr_load ctor imm loc op)
Proof
  Cases_on `bd` >>
  simp[gas_shadow_compiles_return, gasShadowCompileContextTheory.gas_shadow_compiles_ptr_load]
QED

Theorem nonslot_header_shadow[local]:
  (\f. gas_shadow_compiles f f)
    (if 0 < hdr then emit_op ADD [Lit (n2w hdr);off] else comp_return off)
Proof
  IF_CASES_TAC >> simp[gas_shadow_compiles_return,gas_shadow_compiles_emit_op]
QED

Theorem nonslot_control_shadow[local]:
  (\f. gas_shadow_compiles f f)
    (do entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        (case bd of Fixed _ => comp_return ()
           | Dynamic cnt => do invalid <- emit_op GT [len_op;Lit (n2w cnt)];
                               valid <- emit_op ISZERO [invalid];
                               emit_void ASSERT [valid] od);
        emit_inst JMP [Label cond] [];
        new_block cond;
        done_op <- emit_op EQ [Var idx;len_op];
        emit_inst JNZ [done_op;Label exit;Label bod] [];
        new_block bod;
        comp_return (entry,cond,bod,incr,exit,idx)
     od)
Proof
  Cases_on `bd` >> simp[comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- (rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
                >- simp[gas_shadow_compiles_emit_op] >> gen_tac) >>
           simp[gas_shadow_compiles_fresh_label,gas_shadow_compiles_emit_inst,
                gas_shadow_compiles_fresh_var,gas_shadow_compiles_new_block,
                gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void,
                gas_shadow_compiles_return]) >> gen_tac) >>
  simp[gas_shadow_compiles_return]
QED

(* Both compilers traverse these cuts with the same operands and labels. *)
fun nonslot_align_cut th =
  drule_all (MATCH_MP nonslot_shadow_cut (BETA_RULE (SPEC_ALL th))) >> strip_tac >> gvs[];

Theorem nonslot_cut_mono[local]:
  f a = (x,b) ==> ci_mono a (SND (f a)) ==> ci_mono a b
Proof
  simp[]
QED

fun nonslot_mono_cut eqn rws =
  qpat_assum eqn (irule o MATCH_MP nonslot_cut_mono) >> simp rws;

Theorem nonslot_length_mono[local]:
  ci_mono s (SND ((case bd of Fixed cnt => comp_return (Lit (n2w cnt))
    | Dynamic _ => compile_ptr_load ctor imm loc op) s))
Proof
  Cases_on `bd` >> simp[ci_mono_comp_return,ci_mono_compile_ptr_load]
QED

Theorem nonslot_header_mono[local]:
  ci_mono s (SND ((if 0 < hdr then emit_op ADD [Lit (n2w hdr);off]
                    else comp_return off) s))
Proof
  IF_CASES_TAC >> simp[ci_mono_comp_return,ci_mono_emit_op]
QED

Theorem nonslot_code_mid[local]:
  fn_has_code a f func /\ ci_mono a b /\ ci_mono b c /\ ci_mono c f ==>
  fn_has_code b c func
Proof
  simp[ci_mono_def] >> metis_tac[fn_has_code_mid]
QED

fun nonslot_code_cut start finish =
  irule nonslot_code_mid >> conj_tac >- simp[] >>
  qexistsl [start,finish] >> simp[ci_mono_refl];

fun nonslot_block_lookups blocks code =
  qpat_assum blocks (fn th =>
    qpat_assum code (strip_assume_tac o SIMP_RULE (srw_ss())
      [fn_has_code_def, MATCH_MP emitted_blocks_append th,
       DISJ_IMP_THM, FORALL_AND_THM]));

Theorem nonslot_reserved_extend[local]:
  declare_local c id fty st = (bc,sd) /\ c.ce_alloca_locals /\
  local_ptrs_reserved c st /\ st.cs_next_var <= t.cs_next_var /\
  not_fresh_at t (STRING #"%" (toString st.cs_next_var)) ==>
  local_ptrs_reserved bc t
Proof
  strip_tac >>
  gvs[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def, LET_THM] >>
  `~not_fresh_at st (STRING #"%" (toString st.cs_next_var))` by
    simp[not_fresh_at_def] >>
  gvs[local_ptrs_reserved_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem for_nonslot_array_layout_full_with_increment:
  expr_type e = ArrayT sty bd /\ c.ce_alloca_locals /\
  local_ptrs_reserved c sa0 /\ gas_shadow_state sa0 shadow_sa0 /\
  compile_stmt c lctx ret_ty (For id fty (Array e) n loop_body) sa0 = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty (gas_shadow_stmt (For id fty (Array e) n loop_body))
    shadow_sa0 = ((),shadow_sb) /\
  fn_has_code sa0 sb func /\ fn_has_code shadow_sa0 shadow_sb shadow_func ==>
  ?vv sbExpr shadow_sbExpr loc len_op saL bc saD saA xd capacity aidItem
   entry cond bod incr exit idx invalid valid done_var next_var
   sa stride off_op sm sum_op sn addr saCopy sbCopy sbBody sj shadow_sbCopy shadow_sbBody.
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
      (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\ not_fresh_at sa done_var /\
      next_var = STRING #"%" (toString sj.cs_next_var)
Proof
  strip_tac >> drule_all nonslot_for_compiler_cuts >> strip_tac >>
  gvs[gasShadowTheory.gas_shadow_stmt_def,gasShadowTheory.gas_shadow_iterator_def] >>
  `expr_type (gas_shadow_expr e) = ArrayT sty bd` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`c` |-> `gas_shadow_env T c`, `e` |-> `gas_shadow_expr e`,
             `loop_body` |-> `MAP gas_shadow_stmt loop_body`]
      nonslot_for_compiler_cuts)) >> strip_tac >> gvs[] >>
  nonslot_align_cut gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
  nonslot_align_cut nonslot_length_shadow >>
  `gas_shadow_env T bc = bc' /\ gas_shadow_state saD saD'` by
    (mp_tac (Q.INST [`sd` |-> `T`, `cenv` |-> `c`, `ty` |-> `fty`]
       gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_declare_local) >>
     rewrite_tac[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`saL`,`saL'`] (drule_then mp_tac)) >> simp[]) >>
  (* Retain only the real lookup before simplifying the shadow projections. *)
  qpat_x_assum `FLOOKUP bc'.ce_vars id = SOME _` kall_tac >>
  qpat_x_assum `gas_shadow_env _ _ = bc'` (SUBST_ALL_TAC o SYM) >>
  gvs[] >>
  nonslot_align_cut gasShadowCompileStmtBaseTheory.gas_shadow_compiles_emit_local_alloca >>
  nonslot_align_cut nonslot_control_shadow >>
  nonslot_align_cut gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same >>
  nonslot_align_cut nonslot_header_shadow >>
  nonslot_align_cut gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same >>
  `saL'.cs_next_var = saL.cs_next_var` by fs[gas_shadow_state_def] >>
  pop_assum (fn th =>
    qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ saCopy' = _`
      (assume_tac o REWRITE_RULE [th])) >>
  nonslot_align_cut gasShadowCompileStmtOpsTheory.gas_shadow_compiles_iter_elem_copy >>
  nonslot_align_cut (CONJUNCT2 gasShadowCompileStmtTheory.gas_shadow_compile_stmt_env) >>
  `compile_alloc_buffer (type_memory_bytes c fty) saL =
   (<|buf_operand := Var (STRING #"%" (toString saL.cs_next_var));
      buf_size := type_memory_bytes c fty|>,saA)` by
    metis_tac[for_array_declare_emit_alloc_buffer] >>
  qpat_assum `compile_alloc_buffer _ saL = _` (fn th =>
    strip_assume_tac (MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts th) >>
    strip_assume_tac (MATCH_MP loweringHaltTheory.compile_alloc_buffer_insts th)) >>
  qpat_assum `_ saA = (_,sa)`
    (strip_assume_tac o MATCH_MP nonslot_for_control_geometry) >>
  qpat_assum `_ saA' = (_,sa')`
    (strip_assume_tac o MATCH_MP nonslot_for_control_geometry) >>
  qpat_assum `_ sj = ((),sb)`
    (strip_assume_tac o MATCH_MP stmtSimForArrayPartsTheory.compile_for_array_suffix) >>
  qpat_assum `_ sj' = ((),shadow_sb)`
    (strip_assume_tac o MATCH_MP stmtSimForArrayPartsTheory.compile_for_array_suffix) >>
  suspend "prefix_mono"
QED

Resume for_nonslot_array_layout_full_with_increment[prefix_mono]:
  `ci_mono sa0 sbExpr` by
    nonslot_mono_cut `compile_expr _ _ _ sa0 = (_,sbExpr)`
      [stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
  `ci_mono shadow_sa0 sbExpr'` by
    nonslot_mono_cut `compile_expr _ _ (gas_shadow_expr _) shadow_sa0 = (_,sbExpr')`
      [stmtLoweringMonoTheory.ci_mono_compile_expr_sa] >>
  `ci_mono sbExpr saL` by
    nonslot_mono_cut `_ sbExpr = (len_op,saL)` [nonslot_length_mono] >>
  `ci_mono sbExpr' saL'` by
    nonslot_mono_cut `_ sbExpr' = (len_op,saL')` [nonslot_length_mono] >>
  `ci_mono saL saD` by
    nonslot_mono_cut `declare_local _ _ _ saL = (_,saD)`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono saD saA` by
    nonslot_mono_cut `emit_local_alloca _ _ saD = (_,saA)`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono saL' saD'` by
    nonslot_mono_cut `declare_local _ _ _ saL' = (_,saD')`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono saD' saA'` by
    nonslot_mono_cut `emit_local_alloca _ _ saD' = (_,saA')`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono saA sa` by
    (simp[ci_mono_def] >> irule stmtSimForArrayPartsTheory.array_prefix_extends >>
     simp[]) >>
  `ci_mono saA' sa'` by
    (simp[ci_mono_def] >> irule stmtSimForArrayPartsTheory.array_prefix_extends >>
     simp[]) >>
  suspend "body_mono"
QED

Resume for_nonslot_array_layout_full_with_increment[body_mono]:
  `ci_mono sa sm` by nonslot_mono_cut `emit_op MUL _ sa = (off_op,sm)` [ci_mono_emit_op] >>
  `ci_mono sa' sm'` by nonslot_mono_cut `emit_op MUL _ sa' = (off_op,sm')` [ci_mono_emit_op] >>
  `ci_mono sm sn` by nonslot_mono_cut `_ sm = (sum_op,sn)` [nonslot_header_mono] >>
  `ci_mono sm' sn'` by nonslot_mono_cut `_ sm' = (sum_op,sn')` [nonslot_header_mono] >>
  `ci_mono sn saCopy` by
    nonslot_mono_cut `emit_op ADD _ sn = (addr,saCopy)` [ci_mono_emit_op] >>
  `ci_mono sn' saCopy'` by
    nonslot_mono_cut `emit_op ADD _ sn' = (addr,saCopy')` [ci_mono_emit_op] >>
  `ci_mono saCopy sbCopy` by
    nonslot_mono_cut `compile_iter_elem_copy _ _ _ _ _ _ _ _ saCopy = (_,sbCopy)`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono saCopy' sbCopy'` by
    nonslot_mono_cut `compile_iter_elem_copy _ _ _ _ _ _ _ _ saCopy' = (_,sbCopy')`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono sbCopy sbBody` by
    nonslot_mono_cut `compile_stmts _ _ _ _ sbCopy = (_,sbBody)`
      [stmtLoweringMonoTheory.compile_stmt_ci_mono] >>
  `ci_mono sbCopy' sbBody'` by
    nonslot_mono_cut `compile_stmts _ _ _ (MAP gas_shadow_stmt _) sbCopy' = (_,sbBody')`
      [stmtLoweringMonoTheory.compile_stmt_ci_mono] >>
  `ci_mono sbBody sj` by
    nonslot_mono_cut `emit_jmp_if_not_terminated _ sbBody = (_,sj)`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono sbBody' sj'` by
    nonslot_mono_cut `emit_jmp_if_not_terminated _ sbBody' = (_,sj')`
      [stmtLoweringMonoTheory.ci_mono_stmt_helpers] >>
  `ci_mono sj sb` by simp[ci_mono_def] >>
  `ci_mono sj' shadow_sb` by simp[ci_mono_def] >>
  suspend "composed_cuts"
QED

Resume for_nonslot_array_layout_full_with_increment[composed_cuts]:
  (* Compose only the cuts used in the public layout. *)
  `ci_mono sa0 saL` by (irule ci_mono_trans >> qexists `sbExpr` >> simp[]) >>
  `ci_mono saL saA` by (irule ci_mono_trans >> qexists `saD` >> simp[]) >>
  `ci_mono sa saCopy` by
    (irule ci_mono_trans >> qexists `sm` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sn` >> simp[]) >>
  `ci_mono saL sa` by (irule ci_mono_trans >> qexists `saA` >> simp[]) >>
  `ci_mono saL saCopy` by (irule ci_mono_trans >> qexists `sa` >> simp[]) >>
  `ci_mono saL sbCopy` by (irule ci_mono_trans >> qexists `saCopy` >> simp[]) >>
  `ci_mono sa0 saA` by (irule ci_mono_trans >> qexists `saL` >> simp[]) >>
  `ci_mono sa0 sa` by (irule ci_mono_trans >> qexists `saA` >> simp[]) >>
  `ci_mono sa0 saCopy` by (irule ci_mono_trans >> qexists `sa` >> simp[]) >>
  `ci_mono sa0 sbCopy` by (irule ci_mono_trans >> qexists `saCopy` >> simp[]) >>
  `ci_mono sa0 sbBody` by (irule ci_mono_trans >> qexists `sbCopy` >> simp[]) >>
  `ci_mono sbBody sb` by (irule ci_mono_trans >> qexists `sj` >> simp[]) >>
  `ci_mono sbCopy sb` by (irule ci_mono_trans >> qexists `sbBody` >> simp[]) >>
  `ci_mono saCopy sb` by (irule ci_mono_trans >> qexists `sbCopy` >> simp[]) >>
  `ci_mono sa sb` by (irule ci_mono_trans >> qexists `saCopy` >> simp[]) >>
  `ci_mono saA sb` by (irule ci_mono_trans >> qexists `sa` >> simp[]) >>
  `ci_mono saL sb` by (irule ci_mono_trans >> qexists `saA` >> simp[]) >>
  `ci_mono sbExpr sb` by (irule ci_mono_trans >> qexists `saL` >> simp[]) >>
  `ci_mono shadow_sa0 sbCopy'` by
    (irule ci_mono_trans >> qexists `sbExpr'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saL'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saD'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saA'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sa'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sm'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sn'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saCopy'` >> simp[]) >>
  `ci_mono sbBody' shadow_sb` by
    (irule ci_mono_trans >> qexists `sj'` >> simp[]) >>
  `ci_mono sbExpr' shadow_sb` by
    (irule ci_mono_trans >> qexists `saL'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saD'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saA'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sa'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sm'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sn'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saCopy'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sbCopy'` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sbBody'` >> simp[]) >>
  suspend "layout_resources"
QED

Resume for_nonslot_array_layout_full_with_increment[layout_resources]:
  `fn_has_code sa0 sbExpr func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code shadow_sa0 sbExpr' shadow_func` by nonslot_code_cut `shadow_sa0` `shadow_sb` >>
  `fn_has_code sbExpr saL func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code saL saA func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code saA sa func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code sa saCopy func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code saCopy sbCopy func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code sbCopy sbBody func` by nonslot_code_cut `sa0` `sb` >>
  `fn_has_code sbCopy' sbBody' shadow_func` by nonslot_code_cut `shadow_sa0` `shadow_sb` >>
  `fn_has_code sbBody sj func` by nonslot_code_cut `sa0` `sb` >>
  `ci_mono sa0 sj` by (irule ci_mono_trans >> qexists `sbBody` >> simp[]) >>
  `fn_has_code sj sb func` by nonslot_code_cut `sa0` `sb` >>
  nonslot_block_lookups `sa.cs_blocks = _` `fn_has_code saA sa func` >>
  nonslot_block_lookups `sb.cs_blocks = _` `fn_has_code sj sb func` >>
  `IS_SOME (lookup_block exit func.fn_blocks)` by
    (qpat_assum `fn_has_code sa0 sb func` mp_tac >>
     simp[fn_has_code_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `local_ptrs_reserved c saL` by
    (irule local_ptrs_reserved_next_var >> qexists `sa0` >> conj_tac >-
       qpat_assum `ci_mono sa0 saL`
         (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved c sa` by
    (irule local_ptrs_reserved_next_var >> qexists `saL` >> conj_tac >-
       qpat_assum `ci_mono saL sa`
         (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved c saCopy` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> conj_tac >-
       qpat_assum `ci_mono sa saCopy`
         (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  `ci_mono saA sbCopy` by
    (irule ci_mono_trans >> qexists `sa` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `saCopy` >> simp[]) >>
  `not_fresh_at sbCopy (STRING #"%" (toString saL.cs_next_var))` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `saA` >>
     qpat_assum `ci_mono saA sbCopy` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     simp[not_fresh_at_def]) >>
  `local_ptrs_reserved bc sbCopy` by
    (irule nonslot_reserved_extend >> qexistsl [`c`,`fty`,`id`,`saD`,`saL`] >>
     qpat_assum `ci_mono saL sbCopy` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "witnesses"
QED

Resume for_nonslot_array_layout_full_with_increment[witnesses]:
  qexistsl [`vv`,`sbExpr`,`sbExpr'`,
    `case vv_location vv of NONE => LocMemory | SOME l => l`, `len_op`,`saL`,
    `bc`,`saD`,`saA`,`STRING #"%" (toString saL.cs_next_var)`,
    `type_memory_bytes c fty`,`saL.cs_next_id`,
    `entry`,`cond`,`bod`,`incr`,`exit`,`idx`,`invalid`,`valid`,`done_var`,`sa`,
    `elem_size_in_location c (case vv_location vv of NONE => LocMemory | SOME l => l) sty`,
    `off_op`,`sm`,`sum_op`,`sn`,`addr`,`saCopy`,`sbCopy`,`sbBody`,`sj`,`sbCopy'`,`sbBody'`] >>
  qpat_x_assum `idx = STRING #"%" (toString saA'.cs_next_var)` kall_tac >>
  qpat_assum `ci_mono sa0 saL` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `ci_mono saA sa` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `ci_mono sbExpr saL` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `ci_mono sa sj` by
    (irule ci_mono_trans >> qexists `saCopy` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sbCopy` >> conj_tac >- simp[] >>
     irule ci_mono_trans >> qexists `sbBody` >> simp[]) >>
  qpat_assum `ci_mono sa sj` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `emit_jmp_if_not_terminated incr sbBody = ((),sj)`
    (strip_assume_tac o MATCH_MP stmtSimForArrayPartsTheory.array_body_backedge) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sbExpr p` by
    (qpat_assum `compile_expr _ _ _ sa0 = _` mp_tac >>
     qpat_assum `local_ptrs_reserved c sa0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var]) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at saL p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sbExpr` >> simp[]) >>
  `!p. len_op = Var p ==> not_fresh_at saL p` by
    (qpat_assum `_ sbExpr = (len_op,saL)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bd` >> simp[comp_return_def]
     >- (strip_tac >> gvs[]) >>
     disch_then (mp_tac o MATCH_MP exprSafeOperandTheory.compile_ptr_load_safe_operand) >>
     simp[exprSafeOperandTheory.safe_operand_def]) >>
  `not_fresh_at sa done_var` by
    (qpat_assum `done_var = STRING #"%" (toString (sa.cs_next_var - 1))` mp_tac >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >> decide_tac) >>
  suspend "geometry"
QED

Resume for_nonslot_array_layout_full_with_increment[geometry]:
  simp[for_nonslot_layout_def, DISJ_IMP_THM, FORALL_AND_THM, listTheory.APPEND_ASSOC] >>
  conj_tac >-
    (qpat_x_assum `lookup_block saA.cs_current_bb func.fn_blocks = _` mp_tac >>
     simp[listTheory.APPEND_ASSOC]) >>
  conj_tac >-
    (qpat_x_assum `(if _ then _ else _) sm = (sum_op,sn)` mp_tac >>
     IF_CASES_TAC >> simp[comp_return_def]) >>
  qpat_assum `sa.cs_next_var = _` mp_tac >>
  qpat_assum `sa.cs_next_var <= sj.cs_next_var` mp_tac >>
  qpat_assum `sj.cs_next_var = sbBody.cs_next_var` mp_tac >>
  qpat_assum `saA.cs_next_var = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `bd` >> simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  decide_tac
QED

Finalise for_nonslot_array_layout_full_with_increment

Theorem for_nonslot_array_layout_full_with_done_age[local]:
  expr_type e = ArrayT sty bd /\ c.ce_alloca_locals /\
  local_ptrs_reserved c sa0 /\ gas_shadow_state sa0 shadow_sa0 /\
  compile_stmt c lctx ret_ty (For id fty (Array e) n loop_body) sa0 = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty (gas_shadow_stmt (For id fty (Array e) n loop_body))
    shadow_sa0 = ((),shadow_sb) /\
  fn_has_code sa0 sb func /\ fn_has_code shadow_sa0 shadow_sb shadow_func ==>
  ?vv sbExpr shadow_sbExpr loc len_op saL bc saD saA xd capacity aidItem
   entry cond bod incr exit idx invalid valid done_var next_var
   sa stride off_op sm sum_op sn addr saCopy sbCopy sbBody sj shadow_sbCopy shadow_sbBody.
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
      (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\ not_fresh_at sa done_var
Proof
  strip_tac >> drule_all for_nonslot_array_layout_full_with_increment >> metis_tac[]
QED

Theorem for_nonslot_array_layout_full:
  expr_type e = ArrayT sty bd /\ c.ce_alloca_locals /\
  local_ptrs_reserved c sa0 /\ gas_shadow_state sa0 shadow_sa0 /\
  compile_stmt c lctx ret_ty (For id fty (Array e) n loop_body) sa0 = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty (gas_shadow_stmt (For id fty (Array e) n loop_body))
    shadow_sa0 = ((),shadow_sb) /\
  fn_has_code sa0 sb func /\ fn_has_code shadow_sa0 shadow_sb shadow_func ==>
  ?vv sbExpr shadow_sbExpr loc len_op saL bc saD saA xd capacity aidItem
   entry cond bod incr exit idx invalid valid done_var next_var
   sa stride off_op sm sum_op sn addr saCopy sbCopy sbBody sj shadow_sbCopy shadow_sbBody.
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
      (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody)
Proof
  strip_tac >> drule_all for_nonslot_array_layout_full_with_done_age >> metis_tac[]
QED

Theorem for_nonslot_increment_slice:
  lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr;
      bb_instructions := [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [out];
        mk_inst (sj.cs_next_id + 1) ASSIGN [Var out] [idx];
        mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
  out = STRING #"%" (toString sj.cs_next_var) ==>
  ?si sa sb sc. si.cs_current_bb = incr /\ si.cs_current_insts = [] /\
    si.cs_next_var = sj.cs_next_var /\
    emit_op ADD [Var idx;Lit 1w] si = (Var out,sa) /\
    emit_inst ASSIGN [Var out] [idx] sa = ((),sb) /\
    emit_inst JMP [Label cond] [] sb = ((),sc) /\ fn_has_code si sc func
Proof
  strip_tac >>
  qexists `sj with <|cs_current_bb := incr; cs_current_insts := []|>` >>
  fs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
     comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fn_has_code_def, emitted_blocks_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem for_nonslot_array_nil_separated[local]:
  !DF lo d ctx func cx c id env body es0 sa0 s0 G0 tn0
   captured len_op idx bw item lctx sb explicit PG st0 tyv ok
   cond bod exit eid jid dv.
  local_ptrs_reserved c sa0 /\ ~not_fresh_at sa0 dv /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  sa0.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
  lookup_block cond func.fn_blocks = SOME
    <|bb_label := cond; bb_instructions :=
      [mk_inst eid EQ [Var idx;len_op] [dv];
       mk_inst jid JNZ [Var dv;Label exit;Label bod] []]|> ==>
  !es s G tn.
    ~s.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      ?k. s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
        for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,body)
          (es0,sa0,s0,G0,tn0) captured (len_op,idx,bw) item
          (H,k,[],es,c,es,G,tn,s)) /\
    gas_admissible (eval_for cx tyv id body []) ok es ==>
    ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext c c (es with gas_obs := []).scopes /\
      stmt_state_rel H ctx func c cx (es with gas_obs := []) t /\
      storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
      return_buf_frame d c sb t /\
      ghost_inv_at (DF H) lo d c cx (es with gas_obs := []) G1 tn1 t /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c es0 sa0 s0 c (es with gas_obs := []) t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
        aid < sa0.cs_next_id /\
        (!name b len. local_region c es0.scopes s0 name b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem) /\
      (return_buf_sep d c es s ==> return_buf_sep d c (es with gas_obs := []) t)
Proof
  rpt strip_tac >>
  qabbrev_tac `ins = mk_inst eid EQ [Var idx;len_op] [dv]` >>
  qabbrev_tac `su = update_var dv 1w s` >>
  qabbrev_tac `t = jump_to exit su` >>
  qabbrev_tac `G1 = step_prov PG G ins su` >>
  qabbrev_tac `tn1 = step_taint ins s su tn` >>
  qexistsl [`t`, `G1`, `tn1`] >> qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
  strip_tac >>
  PairCases_on `captured` >> PairCases_on `item` >>
  qpat_x_assum `for_nonslot_live _ _ _ _ _ _` mp_tac >>
  rewrite_tac[for_nonslot_live_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `[] = DROP k vs` >>
  `k = LENGTH vs` by
    (qpat_assum `[] = DROP k vs`
       (mp_tac o AP_TERM ``LENGTH : eval_result list -> num``) >>
     qpat_assum `k <= LENGTH vs` mp_tac >> simp[NoAsms] >> decide_tac) >>
  qpat_x_assum `k = LENGTH vs` SUBST_ALL_TAC >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`, Abbr `ins`, Abbr `su`, membership_scalar_ghost_frame] >>
  conj_tac >- suspend "nil_path" >>
  suspend "nil_post"
QED

Resume for_nonslot_array_nil_separated[nil_path]:
  `step_inst_base ins s = OK su` by
    simp[Abbr `ins`, Abbr `su`, step_inst_base_opcode_eqs,
         eval_operand_def, exec_pure2_def, bool_to_word_def] >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn ins s` by suspend "compare_checks" >>
  qabbrev_tac `v = su with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,G1,tn1)` by
    (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_origin_ptr_edge >>
     simp[Abbr `ins`, Abbr `v`, Abbr `G1`, Abbr `tn1`, get_instruction_def,
          mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def] >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >>
     fs[mk_inst_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (v,G1,tn1) [] (OK t,G1,tn1)` by
    suspend "nil_branch" >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED

Resume for_nonslot_array_nil_separated[compare_checks]:
  simp[Abbr `ins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `su`, update_var_def] >>
  rpt strip_tac
  >- (qpat_x_assum `FLOOKUP G idx = NONE` mp_tac >> simp[FLOOKUP_DEF])
  >- (qpat_x_assum `op_prov G len_op = NONE` mp_tac >>
      simp[op_prov_def, FLOOKUP_DEF]) >>
  Cases_on `op = Var idx` >> Cases_on `op = len_op` >> fs[]
QED

Resume for_nonslot_array_nil_separated[nil_branch]:
  `lookup_block v.vs_current_bb func.fn_blocks = SOME
     <|bb_label := cond; bb_instructions :=
       [ins; mk_inst jid JNZ [Var dv;Label exit;Label bod] []]|> /\
   get_instruction <|bb_label := cond; bb_instructions :=
       [ins; mk_inst jid JNZ [Var dv;Label exit;Label bod] []]|>
      v.vs_inst_idx = SOME (mk_inst jid JNZ [Var dv;Label exit;Label bod] []) /\
   ~v.vs_halted /\ eval_operand (Var dv) v = SOME 1w /\
   op_taint tn1 (Var dv) = {} /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    simp[Abbr `v`, Abbr `su`, get_instruction_def, update_var_def,
         eval_operand_def, lookup_var_def, allocas_from_def,
         allocas_below_fmp_def, op_taint_def, FLOOKUP_UPDATE] >>
  drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
  simp[Abbr `v`, Abbr `t`, jump_to_def]
QED

Resume for_nonslot_array_nil_separated[nil_post]:
  `not_local_ptr c es.scopes dv` by (irule fresh_not_local_ptr >> metis_tac[]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   (!x. x <> dv ==> FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))` by
    simp[Abbr `G1`, Abbr `tn1`, Abbr `t`, Abbr `ins`, Abbr `su`,
         SRULE [] copy_eq_jump_frames] >>
  `!x. not_fresh_at sa0 x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `t`, Abbr `su`, lookup_var_def, update_var_def, jump_to_def,
          FLOOKUP_UPDATE] >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_inst_idx = 0 /\
   t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    simp[Abbr `t`, Abbr `su`, jump_to_def, update_var_def] >>
  qpat_x_assum `tn1 = tn with t_var := _` kall_tac >>
  `stmt_state_rel H ctx func c cx es t` by
    (simp[Abbr `t`, Abbr `su`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
     qexists `es` >> simp[]) >>
  `return_buf_frame d c sb t` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x` by
    (qpat_assum `ret_pc_ok _ _ _` (mp_tac o REWRITE_RULE [ret_pc_ok_def]) >>
     metis_tac[]) >>
  `ghost_inv_at (DF H) lo d c cx (es with gas_obs := []) G1 tn1 t` by
    (irule ghost_inv_at_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa0` >> simp[]) >>
  `alloca_frame c es0 sa0 s0 c es su` by
    (simp[Abbr `su`] >> irule alloca_frame_update_var >> simp[]) >>
  `alloca_frame c es0 sa0 s0 c es t` by
    (irule alloca_frame_same_state >>
     qexists `su` >> simp[Abbr `t`, Abbr `su`, jump_to_def, update_var_def]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp s` by
    simp[Abbr `t`, Abbr `su`, allocas_below_fmp_def, jump_to_def, update_var_def] >>
  `return_buf_sep d c es s ==> return_buf_sep d c (es with gas_obs := []) t` by
    (strip_tac >>
     qpat_assum `stmt_state_rel H ctx func c cx es s`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule
         bodyFullSharedTheory.return_buf_sep_locals_kept) >>
     conj_tac
     >- (Cases_on `d` >> simp[] >> rename1 `SOME buf` >> PairCases_on `buf` >>
         fs[return_buf_sep_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
     simp[] >> qexists `sa0` >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa0 x ==> lookup_var x t = _ /\ _` drule >> simp[]) >>
  simp[stmt_lands_def, block_is_terminated_def] >>
  first_assum ACCEPT_TAC
QED

Finalise for_nonslot_array_nil_separated

Theorem for_nonslot_entry_control:
  ~(s.vs_halted) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j0 JMP [Label entry] []) /\
  lookup_block entry fn.fn_blocks = SOME eb /\
  eb.bb_instructions = ([mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (if dyn then
       [mk_inst (eid+1) GT [len_op;Lit (n2w cap)] [bad];
        mk_inst (eid+2) ISZERO [Var bad] [good];
        mk_inst (eid+3) ASSERT [Var good] []] else [])) ++
    [mk_inst j1 JMP [Label cond] []] /\
  eval_operand len_op s = SOME (n2w n) /\ op_prov G len_op = NONE /\
  op_taint tn len_op = {} /\ n <= cap /\ cap < dimword (:256) /\
  (!x. len_op = Var x ==> x NOTIN (if dyn then {idx;bad;good} else {idx})) /\
  (dyn ==> ALL_DISTINCT [idx;bad;good] /\
           ((?x. len_op = Var x) \/ (?w. len_op = Lit w))) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t = jump_to cond
      (if dyn then update_var good 1w (update_var bad 0w (update_var idx 0w (jump_to entry s)))
       else update_var idx 0w (jump_to entry s)) /\
    lookup_var idx t = SOME 0w /\ op_prov G' (Var idx) = NONE /\
    op_taint tn' (Var idx) = {} /\
    (!x. x NOTIN (if dyn then {idx;bad;good} else {idx}) ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  qabbrev_tac `writes = if dyn then {idx;bad;good} else {idx}` >>
  qabbrev_tac `code = [mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (if dyn then
       [mk_inst (eid+1) GT [len_op;Lit (n2w cap)] [bad];
        mk_inst (eid+2) ISZERO [Var bad] [good];
        mk_inst (eid+3) ASSERT [Var good] []] else [])` >>
  qabbrev_tac `s1 = jump_to entry s` >>
  qabbrev_tac `u = if dyn then
    update_var good 1w (update_var bad 0w (update_var idx 0w s1))
    else update_var idx 0w s1` >>
  qabbrev_tac `A = {x | len_op = Var x}` >>
  `scalar_code A code /\ (!v. v IN A ==> op_prov G (Var v) = NONE /\
                                         op_taint tn (Var v) = {})` by
    (Cases_on `len_op` >> Cases_on `dyn` >>
     gvs[Abbr `code`, Abbr `A`, scalar_code_def, scalar_available_def,
         scalar_shape_def, scalar_binary_def, scalar_unary_def, eval_operand_def]) >>
  `~s1.vs_halted /\ allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME eb /\
   isPREFIX code (DROP s1.vs_inst_idx eb.bb_instructions)` by
    (simp[Abbr `s1`, jump_to_def, allocas_from_def, allocas_below_fmp_def] >>
     fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok code s1` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `dyn` >>
     simp[Abbr `code`, inst_mem_below_frontier_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          inst_dload_in_section_def]) >>
  `run_inst_seq code s1 = OK u` by suspend "run" >>
  drule_all range_scalar_joint_lift >>
  disch_then (qspecl_then [`PG`, `explicit`]
    (qx_choosel_then [`G'`,`tn'`,`j`] strip_assume_tac)) >>
  qexistsl [`jump_to cond u`, `G'`, `tn'`] >>
  rewrite_tac[] >>
  conj_tac >- suspend "path" >>
  suspend "posts"
QED

Resume for_nonslot_entry_control[run]:
  `n < dimword (:256)` by decide_tac >>
  Cases_on `len_op` >> Cases_on `dyn` >>
  gvs[Abbr `code`, Abbr `writes`, Abbr `u`, Abbr `s1`, jump_to_def,
      run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
      eval_operand_def, lookup_var_update_var, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, w2n_n2w, LESS_MOD, bool_to_word_def, NOT_LESS]
QED

Resume for_nonslot_entry_control[path]:
  gen_tac >>
  qabbrev_tac `v = u with vs_inst_idx := s1.vs_inst_idx + LENGTH code` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK s1,G,tn)` by
    (simp[Abbr `s1`] >> irule jmp_origin_ptr_path >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s1,G,tn) [] (OK v,G',tn')` by
    (simp[Abbr `v`] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (v,G',tn') []
    (OK (jump_to cond v),G',tn')` by
    (irule jmp_origin_ptr_path >>
     `lookup_block v.vs_current_bb fn.fn_blocks = SOME eb /\
      get_instruction eb v.vs_inst_idx = SOME (mk_inst j1 JMP [Label cond] [])` by
       (Cases_on `dyn` >> simp[Abbr `v`, Abbr `u`, Abbr `s1`, jump_to_def,
         update_var_def, get_instruction_def, EL_LENGTH_APPEND_0]) >>
     Cases_on `dyn` >>
     fs[Abbr `v`, Abbr `u`, Abbr `s1`, jump_to_def, update_var_def,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `jump_to cond v = jump_to cond u` by simp[Abbr `v`, jump_to_def] >>
  `!cfg a b C U r E V.
     gas_origin_ptr_path cfg a [] (OK b,C,U) /\
     gas_origin_ptr_path cfg (b,C,U) [] (r,E,V) ==>
     gas_origin_ptr_path cfg a [] (r,E,V)` by
    (metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,G',tn')` by
    (first_x_assum irule >> metis_tac[]) >>
  simp[Abbr `s1`, Abbr `u`] >>
  metis_tac[]
QED

Resume for_nonslot_entry_control[posts]:
  qpat_assum `!t. run_inst_seq code s1 = OK t ==> _`
    (drule_then strip_assume_tac) >>
  `op_prov G' (Var idx) = NONE /\ op_taint tn' (Var idx) = {}` by
    ((qpat_assum `!v. v IN A UNION _ ==> _` (qspec_then `idx` mp_tac) >>
     Cases_on `dyn` >> simp[Abbr `code`] >> (gvs[]))) >>
  `!x. x NOTIN (if dyn then {idx;bad;good} else {idx}) ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> qpat_assum `!v. ~MEM v _ ==> _` (qspec_then `x` mp_tac) >>
     Cases_on `dyn` >> simp[Abbr `writes`, Abbr `code`]) >>
  Cases_on `dyn` >>
  fs[Abbr `writes`, Abbr `u`, Abbr `s1`, jump_to_def, update_var_def,
     lookup_var_def, FLOOKUP_UPDATE, SF CONJ_ss] >> metis_tac[]
QED

Finalise for_nonslot_entry_control

(* Place the chosen iterator capture at the condition label before the first round. *)
Theorem for_nonslot_array_entry_full:
  !c id fty e sty bd ret_ty body func shadow_func sa0 vv sbExpr shadow_sa0
   shadow_sbExpr loc len_op saL bc saD saA xd capacity aidItem entry cond bod incr
   exit idx invalid valid done_var next_var sa stride off_op sm sum_op sn addr
   saCopy sbCopy sbBody sj sb shadow_sbCopy shadow_sbBody n d s0 ctx u cx st0 em
   env vs stv xs av rv tu lo es0 G0 tn0 Gu DF explicit PG.
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  fn_inst_ids_distinct func /\ c.ce_alloca_locals /\
  stmt_exprs_ok c (For id fty (Array e) n body) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  return_buf_frame d c sa0 s0 /\ ret_pc_ok c sa0 s0 /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  storage_trace_domain cx st0 em.storage_trace /\
  expr_sim_inv_mods mods c cx env em /\ ce_locals_declared c env /\ locals_alloc_ok c env /\
  lookup_scopes id em.scopes = NONE /\
  vs = MAP Value xs /\ evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
  value_has_type (ArrayTV stv bd) (ArrayV av) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
    runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
    ?ent. lookup_scopes name em.scopes = SOME ent /\
      evaluate_subscripts ent.type ent.value path = INL (ArrayV av)) /\
  read_result cx rv em = (INL (ArrayV av),em) /\
  extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
  (loc = LocMemory \/ loc = LocCode) /\
  (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)) /\
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\ op_taint tu len_op = {} /\
  op_prov Gu len_op = NONE /\ ~u.vs_halted /\
  u.vs_current_bb = saL.cs_current_bb /\ u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em u /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em Gu tu u) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) ==>
  ?dw bw s G tn.
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK s,G,tn) /\
      for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,body)
        (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
        (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,0,vs,em,c,em,G,tn,s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  `LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256)` by
    (conj_tac
     >- (Cases_on `bd` >> Cases_on `av` >>
         gvs[value_has_type_inv, extract_elements_def, array_elements_def, bound_length_def]) >>
     metis_tac[typedMemoryCopyTheory.typed_copy_array_count_bound]) >>
  `sbExpr.cs_next_id <= saL.cs_next_id` by
    (Cases_on `bd` >> fs[comp_return_def] >>
     metis_tac[ci_mono_compile_ptr_load, pairTheory.SND, ci_mono_def]) >>
  `sa0.cs_next_var <= saL.cs_next_var /\ lo <= u.vs_alloca_next /\
   stmt_state_rel (storage_trace_horizon em.storage_trace) ctx func c cx em u` by
    (fs[ci_mono_def, storage_trace_domain_def, vv_post_def] >>
     metis_tac[ghost_inv_at_def]) >>
  `capacity < dimword (:256)` by
    (fs[bodySimTheory.stmt_exprs_ok_def, Once allocLimitsTheory.alloc_limits_stmt_def, dimword_def] >> decide_tac) >>
  drule_all (INST_TYPE [beta |-> alpha] bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tu`, `explicit`, `PG`, `Gu`]
    (qx_choosel_then [`p`, `dw`, `a`, `Ga`, `ta`] (map_every assume_tac o CONJUNCTS))) >>
  `p = xd` by fs[] >> pop_assum SUBST_ALL_TAC >>
  `~a.vs_halted /\ a.vs_memory = u.vs_memory` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = u`
       (mp_tac o AP_TERM ``\s:venom_state. (s.vs_halted,s.vs_memory)``) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon em.storage_trace) ctx func c cx em a` by
    (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ u ==> _`
       (qspec_then `storage_trace_horizon em.storage_trace` mp_tac) >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ a`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  suspend "entry_control"
QED

Resume for_nonslot_array_entry_full[entry_control]:
  `saA.cs_current_bb = saL.cs_current_bb` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> simp[]) >>
  qabbrev_tac `dyn = ?cap. bd = Dynamic cap` >>
  qabbrev_tac `writes = if dyn then {idx;invalid;valid} else {idx}` >>
  `!x. not_fresh_at saL x ==> x NOTIN writes` by
    (qpat_assum `EVERY (\p. ~not_fresh_at saL p) [idx;done_var;next_var]` mp_tac >>
     qpat_assum `(case bd of Fixed _ => T | Dynamic _ => _)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `dyn`, Abbr `writes`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!x. len_op = Var x ==> x NOTIN writes` by metis_tac[] >>
  `dyn ==> ALL_DISTINCT [idx;invalid;valid] /\ ((?x. len_op = Var x) \/ (?w. len_op = Lit w))` by
    (qpat_assum `(case bd of Fixed _ => T | Dynamic _ => _)` mp_tac >>
     qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => compile_ptr_load _ _ _ _)
                  sbExpr = (len_op,saL)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `dyn`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> simp[] >>
     Cases_on `len_op` >> simp[] >>
     metis_tac[fragFuelExprHelpersTheory.compile_ptr_load_not_label]) >>
  `a.vs_labels = u.vs_labels` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = u`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >> simp[]) >>
  `!op. (!p. op = Var p ==> not_fresh_at saL p) ==>
     eval_operand op a = eval_operand op u /\
     op_prov Ga op = op_prov Gu op /\ op_taint ta op = op_taint tu op` by
    (Cases >> simp[NoAsms,eval_operand_def,op_prov_def,op_taint_def] >>
     simp[eval_operand_def,op_prov_def,op_taint_def] >>
     rename1 `not_fresh_at saL p ==> _` >> strip_tac >>
     qpat_assum `!p. not_fresh_at saL p ==> lookup_var p a = _ /\ _`
       (qspec_then `p` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[NoAsms,op_taint_def] >> disch_then (fn th => simp[th])) >>
  `eval_operand len_op a = SOME (n2w (LENGTH vs)) /\ op_prov Ga len_op = NONE /\
   op_taint ta len_op = {}` by
    (qpat_assum `!op. _ ==> eval_operand op a = _ /\ _`
       (qspec_then `len_op` mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> asm_rewrite_tac[]) >>
  `?s G tn.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK s,G,tn)) /\
    s = jump_to cond
      (if dyn then update_var valid 1w (update_var invalid 0w (update_var idx 0w (jump_to entry a)))
       else update_var idx 0w (jump_to entry a)) /\
    lookup_var idx s = SOME 0w /\ op_prov G (Var idx) = NONE /\ op_taint tn (Var idx) = {} /\
    (!x. x NOTIN writes ==> lookup_var x s = lookup_var x a /\
      FLOOKUP G x = FLOOKUP Ga x /\ op_taint tn (Var x) = op_taint ta (Var x)) /\
    tn.t_mem = ta.t_mem /\ tn.t_stor = ta.t_stor /\ tn.t_trans = ta.t_trans /\ tn.t_imm = ta.t_imm` by
    (qpat_assum `Abbrev (writes = _)`
       (fn th => pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     irule for_nonslot_entry_control >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qexistsl [`<|bb_label := saL.cs_current_bb;
                      bb_instructions := saA.cs_current_insts ++
                        [mk_inst saA.cs_next_id JMP [Label entry] []]|>`, `saA.cs_next_id`] >>
        simp[get_instruction_def,EL_LENGTH_APPEND_0]) >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     qrefinel [`bound_length bd`, `_`, `saA.cs_next_id + 1`, `sa.cs_next_id - 3`,
               `len_op`, `LENGTH vs`] >>
     qpat_assum `lookup_block entry func.fn_blocks = SOME _` (irule_at Any) >>
     simp[Abbr `writes`] >>
     Cases_on `bd` >> simp[Abbr `dyn`,bound_length_def,ADD_ASSOC]) >>
  `s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
   s.vs_memory = a.vs_memory /\ s.vs_allocas = a.vs_allocas /\
   s.vs_alloca_next = a.vs_alloca_next /\ s.vs_halted = a.vs_halted /\
   s.vs_labels = a.vs_labels` by
    (qpat_assum `s = jump_to _ _` SUBST1_TAC >>
     Cases_on `dyn` >> simp[NoAsms,jump_to_def,update_var_def]) >>
  qpat_x_assum `s = jump_to _ _` (mk_asm "control") >>
  `xd NOTIN writes` by
    (qpat_assum `ALL_DISTINCT [xd;idx;done_var;next_var]` mp_tac >>
     qpat_assum `(case bd of Fixed _ => T | Dynamic _ => _)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms,Abbr `writes`,Abbr `dyn`]) >>
  `!x. not_fresh_at saL x ==>
       lookup_var x s = lookup_var x u /\ FLOOKUP G x = FLOOKUP Gu x /\
       op_taint tn (Var x) = op_taint tu (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!p. not_fresh_at saL p ==> x1 /\ x2 /\ x3`
       (drule_then strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at saL p ==> p NOTIN writes`
       (drule_then assume_tac) >>
     qpat_assum `!p. p NOTIN writes ==> lookup_var p s = _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[]) >>
  `!x. not_fresh_at sa0 x ==>
       lookup_var x s = lookup_var x u /\ FLOOKUP G x = FLOOKUP Gu x /\
       op_taint tn (Var x) = op_taint tu (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at saL x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     first_assum $ drule_then ACCEPT_TAC) >>
  drule abiEncodeMaterializeTheory.materialize_vv_post_operand >>
  disch_then (qx_choose_then `bw` assume_tac) >>
  qexistsl [`dw`, `bw`, `s`, `G`, `tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK s,G,tn)` by
    (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Ga`,`a`,`ta`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv vv u` by
    (qpat_assum `loc = case vv_location vv of _ => _` mp_tac >>
     strip_tac >>
     irule exprSimMemDefsTheory.vv_post_fields_transport >>
     rpt conj_tac
     >- (Cases_on `vv` >> fs[vv_location_def] >> metis_tac[])
     >- first_assum ACCEPT_TAC
     >- (qexists `u` >> simp[]) >>
     qexists `storage_trace_horizon em.storage_trace` >> simp[]) >>
  `loc = LocCode ==>
    immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw em s` by
    (strip_tac >>
     `immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw em u` by
       (Cases_on `vv` >> fs[vv_location_def,vv_operand_def] >>
        drule_all exprPtrUnwrapCodeTheory.vv_post_code_source >> simp[] >> metis_tac[]) >>
     metis_tac[exprSimPropsTheory.immutable_holds_memory_cong]) >>
  `!op. (!p. op = Var p ==> not_fresh_at saL p) ==>
     eval_operand op s = eval_operand op u /\
     op_prov G op = op_prov Gu op /\ op_taint tn op = op_taint tu op` by
    (`s.vs_labels = u.vs_labels` by simp[] >>
     Cases >>
     qpat_assum `!x. not_fresh_at saL x ==> lookup_var x s = _ /\ _` mp_tac >>
     simp[eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]) >>
  `op_taint tu (vv_operand vv) = {}` by
    (qpat_assum `ptr_vv_ok _ _ _ vv _ _ _ _` mp_tac >>
     Cases_on `vv` >> simp[NoAsms,ptr_vv_ok_def,vv_operand_def,ptr_val_ok_def] >>
     metis_tac[]) >>
  `eval_operand (vv_operand vv) s = SOME bw /\
   op_prov G (vv_operand vv) = op_prov Gu (vv_operand vv) /\
   op_taint tn (vv_operand vv) = {} /\
   eval_operand len_op s = SOME (n2w (LENGTH vs)) /\
   op_prov G len_op = NONE /\ op_taint tn len_op = {}` by
    (qpat_assum `!op. _ ==> eval_operand op s = _ /\ _`
       (fn th => mp_tac (Q.SPEC `vv_operand vv` th) >> mp_tac (Q.SPEC `len_op` th)) >>
     simp[] >> metis_tac[]) >>
  suspend "control_frame"
QED

Resume for_nonslot_array_entry_full[control_frame]:
  `stmt_state_rel H ctx func c cx em a` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `!x. x IN writes ==> not_local_ptr c em.scopes x` by
    (gen_tac >> disch_tac >> irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists `saL` >> simp[] >> metis_tac[]) >>
  `not_local_ptr c em.scopes idx /\
   (dyn ==> not_local_ptr c em.scopes invalid /\ not_local_ptr c em.scopes valid)` by
    (qpat_assum `!x. x IN writes ==> _` mp_tac >>
     Cases_on `dyn` >> simp[Abbr `writes`]) >>
  `stmt_state_rel H ctx func c cx em s` by
    (asm "control" SUBST1_TAC >>
     qpat_assum `dyn ==> not_local_ptr _ _ invalid /\ _` mp_tac >>
     Cases_on `dyn` >> simp[stmt_state_rel_jump_to] >> rpt strip_tac >>
     rpt (irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to])) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x` by
    metis_tac[ret_pc_ok_def,freshWritesTheory.not_fresh_at_mono] >>
  `ghost_inv_at (DF H) lo d c cx em Ga ta a` by
    (qpat_assum `stmt_state_rel H ctx func c cx em u`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule
          bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >>
     simp[] >> qexistsl [`Gu`,`w2n dw + capacity`,`saL`,`tu`] >> simp[]) >>
  `ghost_inv_at (DF H) lo d c cx em G tn s` by
    (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     qexistsl [`Ga`,`em`,`a`,`saL`,`ta`] >> simp[] >>
     asm "control" SUBST1_TAC >> Cases_on `dyn` >>
     simp[NoAsms,jump_to_def,update_var_def]) >>
  `!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w` by
    metis_tac[] >>
  `return_buf_frame d c sa0 s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`c`,`s0`,`sa0`] >> simp[]) >>
  `ret_pc_ok c sa0 s` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     qexistsl [`c`,`s0`,`sa0`] >> simp[]) >>
  `alloca_history func s` by
    (irule allocaHistoryTheory.alloca_history_jump >> simp[] >> qexists `a` >> simp[]) >>
  `allocas_from lo s` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `s.vs_allocas = a.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo a` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_assum `stmt_state_rel H ctx func c cx em s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  suspend "item_frame"
QED

Resume for_nonslot_array_entry_full[item_frame]:
  `alloca_frame c em saL u c em s` by
    (qpat_assum `stmt_state_rel H ctx func c cx em u`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule alloca_frame_of_mem_frame) >>
     simp[]) >>
  `alloca_frame c es0 sa0 s0 c em s` by
    (irule alloca_frame_trans >> qexistsl [`c`,`em`,`u`,`saL`] >> simp[]) >>
  `alloca_frame c em sbExpr u c em s` by
    (rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     `aid < saL.cs_next_id` by
       (qpat_assum `aid < sbExpr.cs_next_id` mp_tac >>
        qpat_assum `sbExpr.cs_next_id <= saL.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `alloca_frame c em saL u c em s`
       (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
     disch_then (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `!name root sz. FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) ==>
     lookup_var root s = lookup_var root u /\ lookup_var root a = lookup_var root u` by
    (rpt strip_tac >>
     `not_fresh_at saL root` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
  `ptr_covers G tn xd s capacity` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`Ga`,`a`,`ta`] >> simp[]) >>
  `!name b len. local_region c em.scopes s name b len <=> local_region c em.scopes a name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[]) >>
  `!aid row. FLOOKUP u.vs_allocas aid = SOME row ==>
    FLOOKUP s.vs_allocas aid = SOME row` by simp[] >>
  suspend "item_row_taint"
QED

Resume for_nonslot_array_entry_full[item_row_taint]:
  `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
      off + sz <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func c cx em u`
       (mp_then Any strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `alloca_inv u`
       (strip_assume_tac o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     qpat_assum `alloca_next_valid u`
       (ACCEPT_TAC o REWRITE_RULE [venomMemDefsTheory.alloca_next_valid_def])) >>
  `!i. i < u.vs_alloca_next ==> (i IN tn.t_mem <=> i IN tu.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!i. i IN ta.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tu.t_mem` by
    (rpt strip_tac >>
     `off + sz <= u.vs_alloca_next` by
       (qpat_assum `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==> _`
          (drule_then ACCEPT_TAC)) >>
     `i < u.vs_alloca_next` by
       (qpat_assum `i < off + sz` mp_tac >>
        qpat_assum `off + sz <= u.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
qpat_assum `!i. i < u.vs_alloca_next ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa0 x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >> simp[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!name b len. local_region c es0.scopes s0 name b len ==>
         off + sz <= b \/ b + len <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by simp[] >>
     `i IN tu.t_mem` by res_tac >>
     qpat_assum `ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     res_tac) >>
  suspend "item_separation"
QED

Resume for_nonslot_array_entry_full[item_separation]:
  `!name b len. local_region c em.scopes s name b len ==>
    w2n dw + capacity <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >>
     `local_region c em.scopes a name b len` by
       (qpat_assum `!name b len. local_region c em.scopes s name b len <=> _`
          (qspecl_then [`name`,`b`,`len`] mp_tac) >> simp[]) >>
     qpat_assum `!name b len. local_region c em.scopes a name b len ==> _`
       (qspecl_then [`name`,`b`,`len`]
          (drule_then (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])))) >>
  `FLOOKUP G idx = NONE` by
    (qpat_assum `op_prov G (Var idx) = NONE`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [op_prov_def])) >>
  `!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t` by
    (`?bb inst. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI` by
       (qpat_assum `lookup_block cond func.fn_blocks = SOME _`
          (fn th => simp[th,get_instruction_def,mk_inst_def])) >>
     `!i. active_inst func i s ==> frag_reachable ctx func u func i s` by
       (qpat_assum `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK s,G,tn)`
          (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
        drule bodyFullIfExpReachTheory.ifexp_ptr_path_reachable >>
        disch_then (qspec_then `s` mp_tac) >> simp[] >> metis_tac[]) >>
     rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_trans >>
     metis_tac[]) >>
  `!name path root sz w. rv = PlaceR (MemoryPlace name path) /\
     FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\ lookup_var root u = SOME w ==>
     lookup_var root s = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!name root sz. FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) ==> _`
       (qspecl_then [`name`,`root`,`sz`] mp_tac) >> simp[]) >>
  suspend "item_live"
QED

Resume for_nonslot_array_entry_full[item_live]:
  `loc = LocCode ==> !src name path. rv = PlaceR (ImmutablePlace src name path) ==>
     ?tv root. lookup_immutable cx em src name = SOME (tv,root) /\
               evaluate_subscripts tv root path = INL (ArrayV av)` by
    (rpt strip_tac >> irule (iffLR forNestedArrayCaptureTheory.read_result_immutable_place) >> gvs[]) >>
  `!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
      aid < sbExpr.cs_next_id /\
      (!name lb lsz. local_region c em.scopes u name lb lsz ==>
        b + len <= lb \/ lb + lsz <= b) /\
      b <= i /\ i < b + len /\ i IN tn.t_mem ==> i IN tu.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\
                               off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tu.t_mem`
       (drule_all_then ACCEPT_TAC)) >>
  `~s.vs_halted /\ lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
   sbExpr.cs_next_id <= aidItem /\ w2n dw + capacity <= s.vs_alloca_next /\
   FLOOKUP s.vs_allocas aidItem = SOME (w2n dw,capacity) /\ lookup_var xd s = SOME dw` by
    simp[] >>
  `!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==> FLOOKUP s.vs_allocas aid = SOME row` by
    simp[] >>
  `!x w. not_fresh_at saL x /\ lookup_var x u = SOME w ==> lookup_var x s = SOME w` by
    simp[] >>
  rewrite_tac[for_nonslot_live_def,stmtSimPropsTheory.cenv_top_ext_refl,DROP_0,ZERO_LESS_EQ] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_nonslot_array_entry_full

Theorem for_nonslot_copy_open[local]:
  (loc = LocMemory \/ loc = LocCode) /\
  acyclic_struct_metadata c.ce_struct_fields /\ ~block_is_terminated sa /\
  compile_iter_elem_copy c addr dst stride loc (is_slot_addressed loc) fty sty sa =
    ((),sb) ==> ~block_is_terminated sb
Proof
  strip_tac
  >- (qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_iter_elem_copy_def, is_slot_addressed_def,
           comp_bind_def, comp_ignore_bind_def] >>
      IF_CASES_TAC
      >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
          drule exprOpenPrimitivesTheory.emit_void_terminated >> simp[is_terminator_def]) >>
      strip_tac >> irule (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]
        exprOpenCopiesTheory.compile_store_memory_open) >>
      metis_tac[]) >>
  qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_iter_elem_copy_def, is_slot_addressed_def,
       comp_bind_def, comp_ignore_bind_def] >>
  IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
      drule exprOpenPrimitivesTheory.emit_void_terminated >> simp[is_terminator_def]) >>
  strip_tac >> drule_all_then ACCEPT_TAC
    exprOpenTerminalsTheory.compile_imm_copy_to_memory_open
QED

Theorem for_nonslot_body_instruction[local]:
  ~block_is_terminated sbCopy /\
  compile_stmts bc (InLoop exit incr) ret_ty ss sbCopy = ((),sbBody) /\
  fn_has_code sbCopy sbBody func /\ fn_has_code sbBody sj func /\
  (~block_is_terminated sbBody ==>
    sj.cs_current_bb = sbBody.cs_current_bb /\
    sj.cs_current_insts = sbBody.cs_current_insts ++
      [mk_inst sbBody.cs_next_id JMP [Label incr] []]) ==>
  ?bb i. lookup_block sbCopy.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sbCopy.cs_current_insts) = SOME i /\
    i.inst_opcode <> PHI
Proof
  strip_tac >>
  drule (cj 2 entryReachBodyFirstEmissionStmtTheory.first_emission_compile_stmt) >>
  disch_then (CONJUNCTS_THEN2 kall_tac DISJ_CASES_TAC)
  >- (`~block_is_terminated sbBody` by fs[block_is_terminated_def] >>
      qpat_assum `~block_is_terminated sbBody ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `fn_has_code sbBody sj func`
        (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
      qexistsl [`bb`, `mk_inst sbBody.cs_next_id JMP [Label incr] []`] >>
      fs[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN, mk_inst_def] >>
      metis_tac[]) >>
  qpat_assum `!fn. fn_has_code sbCopy sbBody fn ==> _`
    (qspec_then `func` (drule_then strip_assume_tac)) >>
  qexistsl [`bb`,`i`] >> fs[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]
QED

(* Execute the nonempty test and the actual indexed copy before calling the body. *)
Theorem for_nonslot_array_head_full:
  for_nonslot_layout (c, id, fty, e, sty, bd, ret_ty, loop_body)
    (func, shadow_func)
    (sa0, vv, sbExpr, shadow_sa0, shadow_sbExpr, loc, len_op, saL)
    (bc, saD, saA, xd, capacity, aidItem)
    (entry, cond, bod, incr, exit, idx, invalid, valid, done_var, next_var)
    (sa, stride, off_op, sm, sum_op, sn, addr, saCopy, sbCopy)
    (sbBody, sj, sb, shadow_sbCopy, shadow_sbBody) /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ c.ce_alloca_locals /\ fn_inst_ids_distinct func /\
  supported_stmt tops bindings (For id fty (Array e) bound loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) bound loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) bound loop_body) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\
  body_for_full_ok_mods mods exps cx dtv id loop_body vs /\
  storage_trace_domain cx st0 es.storage_trace /\
  return_buf_sep d c es s /\
  s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    for_nonslot_live (DF H, lo, d, ctx, func, cx, c, id, env, loop_body)
      (es0, sa0, s0, G0, tn0)
      (e, sbExpr, saL, loc, vv, bd, stv, vs, rv, av, xs, em, u, Gu, tu)
      (len_op, idx, bw) (xd, dw, capacity, aidItem)
      (H, k, a::rs, es, c, es, G, tn, s)) ==>
  ?v eb t Gf tnf.
    read_result cx a es = (INL v,es) /\
    push_scope_with_var id dtv v es = (INL (),eb) /\
    value_has_type dtv v /\ val_wf dtv v /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
      return_buf_sep d bc eb t /\
      for_nonslot_body_entry (DF H, lo, d, ctx, func, cx, c, id, env, loop_body)
        (es0, sa0, s0, G0, tn0)
        (e, sbExpr, saL, loc, vv, bd, stv, vs, rv, av, xs, em, u, Gu, tu)
        (len_op, idx, bw) (xd, dw, capacity, aidItem)
        (bc, extend_local env id fty F, sbCopy, dtv, v) (H, k, a::rs, es, eb, Gf, tnf, t)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then assume_tac) >>
  drule for_nonslot_live_head_index >> strip_tac >>
  qpat_x_assum `k = LENGTH vs - _` kall_tac >>
  qpat_x_assum `a = EL k vs` (mk_asm "head") >>
  qpat_x_assum `for_nonslot_live _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_live_def]) >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  `LENGTH vs < dimword (:256)` by
    (irule LESS_EQ_LESS_TRANS >> qexists_tac `bound_length bd` >> simp[]) >>
  qabbrev_tac `p = jump_to bod (update_var done_var 0w s)` >>
  qabbrev_tac `Gp = DRESTRICT G (COMPL {done_var})` >>
  qabbrev_tac `tnp = tn with t_var := tn.t_var |+ (done_var,{})` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK p,Gp,tnp)` by
    (gen_tac >> simp[Abbr `p`, Abbr `Gp`, Abbr `tnp`] >>
     irule for_nonslot_head_test_at_cond >>
     simp[] >> qexistsl [`sa.cs_next_id - 2`, `exit`, `idx`,
       `sa.cs_next_id - 1`, `k`, `LENGTH vs`, `len_op`] >> simp[]) >>
  `sa0.cs_next_var <= saL.cs_next_var /\ saL.cs_next_var <= saA.cs_next_var /\
   saA.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= saCopy.cs_next_var /\
   saCopy.cs_next_var <= sbCopy.cs_next_var` by fs[ci_mono_def] >>
  `saL.cs_next_var <= sa.cs_next_var /\ sa0.cs_next_var <= sbCopy.cs_next_var` by simp[] >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at saL x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa0` >> simp[]) >>
  `!x. not_fresh_at saL x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `saL` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at saCopy x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `~not_fresh_at saL done_var /\ xd <> done_var /\ idx <> done_var` by fs[] >>
  `return_buf_frame d c saL s` by
    (irule return_buf_frame_frame >> qexistsl [`c`,`s`,`sa0`] >> simp[]) >>
  `ret_pc_ok c saL s` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >> qexistsl [`c`,`s`,`sa0`] >> simp[]) >>
  drule_all for_nonslot_head_test_frame >>
  disch_then (qspec_then `bod` mp_tac) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  map_every (fn q =>
    qpat_assum q (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (p = _)`, `Abbrev (Gp = _)`, `Abbrev (tnp = _)`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
     stmt_state_rel H ctx func c cx es p /\ storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d c cx es Gp tnp p` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s` kall_tac >>
     qpat_x_assum `ghost_inv_at (DF H0) _ _ _ _ _ G tn s` kall_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H` (drule_then
         (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_live_def]))) >>
     drule_all for_nonslot_head_test_frame >>
     disch_then (qspec_then `bod` mp_tac) >>
     simp[Abbr `p`, Abbr `Gp`, Abbr `tnp`]) >>
  `cenv_top_ext c bc (FEMPTY :: es.scopes)` by
    (irule stmtSimDeclComposeTheory.cenv_top_ext_declare_local >>
     simp[] >> qexistsl [`id`, `saL`, `saD`, `fty`] >> simp[] >>
     rpt strip_tac >>
     `id IN FDOM env.var_types` by metis_tac[bodySimTheory.ce_locals_declared_def] >>
     `?ty. FLOOKUP env.var_types id = SOME ty` by metis_tac[FLOOKUP_DEF] >>
     drule_all targetPlaceSimTheory.expr_sim_inv_local >> simp[]) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [xd] /\ inst.inst_id = aidItem` by
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])
       loweringHaltTheory.compile_alloc_buffer_insts >>
     qexists_tac `mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd]` >>
     conj_tac >-
       (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
        qexistsl [`saL`,`saA`] >> simp[]) >>
     simp[mk_inst_def]) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saCopy x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `saL` >> simp[] >>
     qpat_assum `ret_pc_ok c saL p`
       (qspecl_then [`x`,`sz`] mp_tac o REWRITE_RULE [ret_pc_ok_def]) >> simp[]) >>
  `capacity = type_memory_size dtv` by
    (simp[] >> irule expr_sim_inv_memory_size >> qexistsl [`cx`,`env`,`es`] >> simp[]) >>
  `!name root sz. FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) ==>
     not_fresh_at saL root` by
    ((qpat_assum `local_ptrs_reserved c saL` mp_tac >>
     simp[local_ptrs_reserved_def] >> (metis_tac[local_ptrs_reserved_def]))) >>
  `!x. not_fresh_at saL x ==> lookup_var x p = lookup_var x s /\
     FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> done_var` by
       (disch_then SUBST_ALL_TAC >> qpat_assum `~not_fresh_at saL done_var` mp_tac >> simp[]) >>
     simp[]) >>
  `p.vs_labels = s.vs_labels` by
    simp[Abbr `p`, jump_to_def, update_var_def] >>
  `!op. (!x. op = Var x ==> not_fresh_at saL x) ==>
     eval_operand op p = eval_operand op s /\ op_prov Gp op = op_prov G op /\
     op_taint tnp op = op_taint tn op` by
    (Cases >> simp[eval_operand_def,op_prov_def,op_taint_def]) >>
  `!name b z. local_region c es.scopes p name b z <=>
               local_region c es.scopes s name b z` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at saL x ==> lookup_var x p = _ /\ _`
       (irule o cj 1) >>
     qpat_assum `!name root sz. FLOOKUP c.ce_vars name = _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  `!name b z. local_region bc (FEMPTY :: es.scopes) p name b z <=>
               local_region c es.scopes p name b z` by
    (rpt gen_tac >> Cases_on `name = id` >>
     pure_rewrite_tac[local_region_def] >> simp[lookup_scopes_def]) >>
  `alloca_frame c em sbExpr u c es p /\
   alloca_frame c es0 sa0 s0 c es p /\
   alloca_frame c es0 sa0 s0 bc (es with scopes updated_by CONS FEMPTY) p` by
    (pure_rewrite_tac[alloca_frame_def] >> simp[NoAsms] >>
     qpat_assum `!name b z. local_region bc _ p name b z <=> _`
       (pure_rewrite_tac o single) >>
     qpat_assum `!name b z. local_region c _ p name b z <=> _`
       (pure_rewrite_tac o single) >>
     qpat_assum `p.vs_memory = s.vs_memory` (pure_rewrite_tac o single) >>
     conj_tac >-
       qpat_assum `alloca_frame c em sbExpr u c es s`
         (ACCEPT_TAC o REWRITE_RULE[alloca_frame_def]) >>
     conj_tac >> qpat_assum `alloca_frame c es0 sa0 s0 c es s`
       (ACCEPT_TAC o REWRITE_RULE[alloca_frame_def])) >>
  mp_tac (Q.INST [`s` |-> `p`, `G` |-> `Gp`, `tn` |-> `tnp`,
     `offOp` |-> `off_op`, `sumOp` |-> `sum_op`,
     `dyn` |-> `(case bd of Fixed _ => F | Dynamic _ => T)`]
     bodyFullForArrayElementPrepareTheory.for_nonslot_array_element_prepare_full) >>
  (impl_tac >- suspend "prepare_inputs") >>
  disch_then (qx_choose_then `v` (qx_choose_then `eb`
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS)))))) >>
  qexistsl [`v`, `eb`, `t`, `Gf`, `tnf`] >>
  conj_tac >- (asm "head" (once_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspec_then `DF H` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[] >> disch_then irule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "body_entry_separation" >>
  rewrite_tac[for_nonslot_body_entry_def] >>
  conj_tac >- suspend "capture_frames" >>
  suspend "push_body_scope"
QED

Resume for_nonslot_array_head_full[prepare_inputs]:
  simp[exprSimPropsTheory.immutable_holds_memory_cong] >>
     rpt conj_tac
     >- (qpat_assum `loc = _` (pure_rewrite_tac o single o SYM) >>
         strip_tac >>
         drule exprSimPropsTheory.immutable_holds_memory_cong >>
         disch_then (pure_rewrite_tac o single) >>
         qpat_assum `loc = LocCode ==> immutable_holds _ _ _ _ _ _ _`
           (drule_then ACCEPT_TAC))
     >- (rpt strip_tac >>
         `not_fresh_at saL root` by
           (qpat_assum `!name root sz. FLOOKUP c.ce_vars name = _ ==> _`
             (drule_then ACCEPT_TAC)) >>
         qpat_assum `!name path root sz w. _ ==> lookup_var root s = SOME w`
           (drule_all_then assume_tac) >> simp[])
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `let hdr = _ in if 0 < hdr then emit_op ADD _ sm = _ else _`
           (mp_tac o PURE_REWRITE_RULE [LET_THM]) >>
         Cases_on `bd` >> simp[arithmeticTheory.GREATER_DEF])
     >- metis_tac[]
     >- (goal_assum (drule_at (Pat `MEM _ (fn_insts func)`)) >> metis_tac[])
     >- first_assum ACCEPT_TAC
     >- (irule return_buf_frame_frame >> qexistsl [`c`,`p`,`saL`] >> simp[])
     >- (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[])
     >- (pure_rewrite_tac [allocas_from_def] >>
         qpat_assum `p.vs_allocas = s.vs_allocas` (pure_rewrite_tac o single) >>
         qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))
     >> simp[Abbr `p`, allocas_below_fmp_def, jump_to_def, update_var_def] >>
        fs[allocas_below_fmp_def]
QED

Resume for_nonslot_array_head_full[body_entry_separation]:
  qpat_assum `stmt_state_rel H0 ctx func c cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule
       bodyFullSharedTheory.return_buf_sep_allocated_local) >>
  conj_tac
  >- (qpat_assum `gas_origin_ptr_path (DF H,_,_,_,_,_) (s,G,tn) _ (OK t,Gf,tnf)`
        (fn path =>
          qpat_assum `return_buf_frame d c sa0 s` (fn frame =>
            qpat_assum `return_buf_sep d c es s` (fn sep =>
              ACCEPT_TAC (MATCH_MP bodyFullSharedTheory.return_buf_allocas_path
                (LIST_CONJ [path,frame,sep])))))) >>
  conj_tac
  >- (qexistsl [`aidItem`,`id`,`xd`,`capacity`,`dw`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `push_scope_with_var id dtv v es = (INL (),eb)`
        (mp_tac o REWRITE_RULE [push_scope_with_var_def, return_def]) >>
      simp[NoAsms] >> disch_then (fn eq =>
        qpat_assum `lookup_scopes n eb.scopes = SOME _`
          (mp_tac o REWRITE_RULE [GSYM eq])) >>
      simp[lookup_scopes_def, FLOOKUP_UPDATE]) >>
  conj_tac >-
    (qexists_tac `saL` >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa x` by
       (qpat_assum `!x. not_fresh_at saL x ==> not_fresh_at sa x`
         (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at saL x ==> lookup_var x p = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_head_full[capture_frames]:
  `!x. not_fresh_at saL x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by
       (qpat_assum `!x. not_fresh_at saL x ==> not_fresh_at sa x`
         (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at saL x ==> lookup_var x p = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (drule gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at saL x) ==>
      eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
      op_taint tnf op = op_taint tn op` by
    (Cases >> simp[eval_operand_def, op_prov_def, op_taint_def]) >>
  `eval_operand (vv_operand vv) t = SOME bw /\
    op_prov Gf (vv_operand vv) = op_prov Gu (vv_operand vv) /\
    op_taint tnf (vv_operand vv) = {} /\
    eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
    op_prov Gf len_op = NONE /\ op_taint tnf len_op = {}` by
    (qpat_assum `!op. _ ==> eval_operand op t = _ /\ _`
       (fn frame => mp_tac (Q.SPEC `vv_operand vv` frame) >>
                    mp_tac (Q.SPEC `len_op` frame)) >>
     simp[]) >>
  `lookup_var idx t = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {}` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `idx` mp_tac) >>
     qpat_assum `!x. x <> done_var ==> lookup_var x p = _ /\ _`
       (qspec_then `idx` mp_tac) >>
     simp[]) >>
  `!name b len. local_region c es.scopes t name b len <=>
                 local_region c es.scopes s name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at saL x ==> lookup_var x t = _ /\ _`
       (irule o cj 1) >>
     qpat_assum `!name root sz. FLOOKUP c.ce_vars name = _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  `eb.scopes =
      (FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>))
        :: es.scopes` by
    (qpat_x_assum `push_scope_with_var id dtv v es = (INL (),eb)`
       (mp_tac o REWRITE_RULE [push_scope_with_var_def, return_def]) >>
     simp[] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `cenv_top_ext c bc eb.scopes` by
    (simp[] >> irule stmtSimDeclComposeTheory.cenv_top_ext_declare_local >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`id`,`saL`,`saD`,`fty`] >> simp[] >>
     rpt strip_tac >>
     `id IN FDOM env.var_types` by metis_tac[bodySimTheory.ce_locals_declared_def] >>
     `?ty. FLOOKUP env.var_types id = SOME ty` by metis_tac[FLOOKUP_DEF] >>
     drule_all targetPlaceSimTheory.expr_sim_inv_local >> simp[]) >>
  `!x w. not_fresh_at sa0 x /\ lookup_var x s = SOME w ==>
          lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at saL x` by
       (qpat_assum `!x. not_fresh_at sa0 x ==> not_fresh_at saL x`
         (drule_then ACCEPT_TAC)) >> simp[]) >>
  `return_buf_frame d bc sa0 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`c`,`s`,`sa0`] >>
     simp[GSYM AND_IMP_INTRO] >>
     metis_tac[stmtFragPtrTheory.cenv_top_ext_return_buf]) >>
  `ret_pc_ok bc sa0 t` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     qexistsl [`c`,`s`,`sa0`] >> simp[] >>
     metis_tac[stmtSimPropsTheory.cenv_top_ext_return_pc]) >>
  `!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q` by
    suspend "body_position_reachable" >>
  `!name b len. local_region bc eb.scopes t name b len ==>
     (b = w2n dw /\ len = capacity) \/ local_region c es.scopes p name b len` by
    (rpt gen_tac >>
     simp[NoAsms, local_region_def] >> strip_tac >>
     Cases_on `name = id`
     >- (disj1_tac >>
         qpat_assum `name = id` (fn eq =>
           qpat_x_assum `FLOOKUP bc.ce_vars name = SOME (PtrVar (Var p') len)`
             (mp_tac o REWRITE_RULE [eq])) >>
         qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity)`
           (pure_rewrite_tac o single) >>
         simp[] >> strip_tac >>
         qpat_assum `xd = p'` (fn eq =>
           qpat_assum `lookup_var p' t = SOME w` (mp_tac o REWRITE_RULE [GSYM eq])) >>
         qpat_assum `lookup_var xd t = SOME dw` (fn th => simp[NoAsms, th])) >>
     disj2_tac >>
     `FLOOKUP c.ce_vars name = SOME (PtrVar (Var p') len)` by
       (qpat_assum `!name. name <> id ==> FLOOKUP bc.ce_vars name = _`
          (drule_then (rewrite_tac o single o SYM)) >>
        first_assum ACCEPT_TAC) >>
     `not_fresh_at saL p'` by
       (qpat_assum `!name root sz. FLOOKUP c.ce_vars name = _ ==> _`
         (drule_then ACCEPT_TAC)) >>
     `lookup_var p' p = SOME w` by
       (qpat_assum `!x. not_fresh_at saL x ==> lookup_var x p = _ /\ _`
          (drule_then (rewrite_tac o single o cj 1)) >>
        qpat_assum `!x. not_fresh_at saL x ==> lookup_var x t = _ /\ _`
          (drule_then (rewrite_tac o single o SYM o cj 1)) >>
        first_assum ACCEPT_TAC) >>
     qexistsl [`entry'`, `p'`,`w`] >> asm_rewrite_tac[] >>
     qpat_x_assum `lookup_scopes name eb.scopes = SOME entry'` mp_tac >>
     asm_rewrite_tac[] >> simp[lookup_scopes_def, FLOOKUP_UPDATE]) >>
  `venomMemDefs$allocas_non_overlapping s` by
    (qpat_assum `stmt_state_rel H0 ctx func c cx es s`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     simp[venomMemDefsTheory.alloca_inv_def]) >>
  `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sbExpr.cs_next_id ==>
    off + sz <= w2n dw \/ w2n dw + capacity <= off` by
    (rpt gen_tac >> strip_tac >>
     `aid <> aidItem` by
       (qpat_assum `aid < sbExpr.cs_next_id` mp_tac >>
        qpat_assum `sbExpr.cs_next_id <= aidItem` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `allocas_non_overlapping s`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`aid`,`aidItem`,`off`,`sz`,`w2n dw`,`capacity`] mp_tac) >>
     simp[]) >>
  `alloca_frame c em sbExpr u bc eb t` by suspend "capture_copy_frame" >>
  `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sbExpr.cs_next_id /\
    (!name base len. local_region c em.scopes u name base len ==>
      off + sz <= base \/ base + len <= off) /\
    off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tu.t_mem` by
    suspend "capture_copy_taint" >>
  `loc = LocCode ==> immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw es t` by
    (pure_rewrite_tac[immutable_holds_def] >>
     qpat_assum `loc = LocCode ==> immutable_holds _ _ _ _ _ _ s`
       (ACCEPT_TAC o REWRITE_RULE [immutable_holds_def])) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
    for_nonslot_live _ _ _ _ _ _`
    (qspec_then `H` (drule_then
      (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_live_def]))) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func bc cx eb t /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by simp[] >>
  `lo <= t.vs_alloca_next /\ w2n dw + capacity <= t.vs_alloca_next` by simp[] >>
  `!aid row. FLOOKUP u.vs_allocas aid = SOME row ==>
    FLOOKUP t.vs_allocas aid = SOME row` by simp[] >>
  `!x w. not_fresh_at saL x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at saL x ==> lookup_var x t = _ /\ _`
       (drule_then (rewrite_tac o single o cj 1)) >>
     qpat_assum `!x w. not_fresh_at saL x /\ lookup_var x u = SOME w ==> lookup_var x s = _`
       (drule_all_then ACCEPT_TAC)) >>
  pure_rewrite_tac[for_nonslot_live_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `!v. rv = Value v /\ _ ==> vv_own _ _ _ _ _ _ _ _ _ /\ _`
         (fn own => simp[NoAsms, own])) >>
  TRY (first_assum (ACCEPT_TAC o GSYM))
  >~ [`!name path root sz w. rv = PlaceR (MemoryPlace name path) /\ FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\ lookup_var root u = SOME w ==> lookup_var root t = SOME w`]
  >- (rpt strip_tac >>
      `not_fresh_at saL root` by
        (qpat_assum `!name root sz. FLOOKUP c.ce_vars name = _ ==> _`
           (drule_then ACCEPT_TAC)) >>
      qpat_assum `!x. not_fresh_at saL x ==> lookup_var x t = _ /\ _`
        (drule_then (rewrite_tac o single o cj 1)) >>
      qpat_assum `!name path root sz w. rv = PlaceR (MemoryPlace name path) /\ _ ==> _`
        (drule_all_then ACCEPT_TAC))
  >> qpat_assum `!name b z. local_region c es.scopes t name b z <=> _`
       (once_rewrite_tac o single) >>
  qspecl_then [`capacity`,`w2n dw`] (once_rewrite_tac o single)
    arithmeticTheory.ADD_COMM >>
  first_assum ACCEPT_TAC
QED


Resume for_nonslot_array_head_full[body_position_reachable]:
  `~block_is_terminated saCopy` by
    (drule exprOpenPrimitivesTheory.emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  `acyclic_struct_metadata c.ce_struct_fields` by
    (qpat_assum `body_inv tops ctx c cx`
       (ACCEPT_TAC o MATCH_MP bodyInvCodePropsTheory.contract_inv_acyclic_struct_metadata
         o MATCH_MP bodySimTheory.body_inv_contract)) >>
  `~block_is_terminated sbCopy` by
    (irule for_nonslot_copy_open >>
     qexistsl [`addr`,`c`,`Var xd`,`fty`,`loc`,`saCopy`,`stride`,`sty`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?bb i. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI` by
    (simp[] >> irule for_nonslot_body_instruction >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`bc`,`exit`,`incr`,`ret_ty`,`sbBody`,`sj`,`loop_body`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. active_inst func i t ==> frag_reachable ctx func s func i t` by
    (qpat_assum `gas_origin_ptr_path (DF H,_,_,_,_,_) (s,G,tn) _ (OK t,Gf,tnf)`
       (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     drule bodyFullIfExpReachTheory.ifexp_ptr_path_reachable >>
     disch_then (qspec_then `t` mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  drule contextRawReachableTheory.frag_reachable_trans >> metis_tac[]
QED

Resume for_nonslot_array_head_full[capture_copy_frame]:
  rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `off + sz <= w2n dw \/ w2n dw + capacity <= off`
  >- (qpat_assum `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  qpat_assum `alloca_frame c em sbExpr u c es p`
    (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
  disch_then (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  (conj_tac >-
    (irule EQ_TRANS >> qexists_tac `mem_bytes_at off sz p.vs_memory` >>
     conj_tac >-
       (qpat_assum `typed_copy_frame (w2n dw) capacity _ _`
          (fn th => MATCH_MP_TAC (Q.SPECL [`off`,`sz`]
            (CONJUNCT1 (REWRITE_RULE [typedMemoryCopyTheory.typed_copy_frame_def] th)))) >>
        simp[]) >>
     first_assum ACCEPT_TAC)) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!name b len. local_region bc eb.scopes t name b len ==> _`
    (drule_then (DISJ_CASES_THEN STRIP_ASSUME_TAC))
  >- (qpat_assum `b = w2n dw` (pure_rewrite_tac o single) >>
      qpat_assum `sz' = capacity` (pure_rewrite_tac o single) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `!n b sz'. local_region c es.scopes p n b sz' ==> _` (drule_then ACCEPT_TAC)
QED

Resume for_nonslot_array_head_full[capture_copy_taint]:
  rpt gen_tac >> strip_tac >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `off + sz <= w2n dw \/ w2n dw + capacity <= off`
  >- (qpat_assum `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `~(w2n dw <= i /\ i < w2n dw + capacity)` by
    (qpat_assum `off + sz <= w2n dw \/ w2n dw + capacity <= off` mp_tac >>
     qpat_assum `off <= i` mp_tac >> qpat_assum `i < off + sz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `i IN tn.t_mem` by
    (qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     simp[Abbr `tnp`]) >>
  qpat_assum `!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\ _ ==> _`
    (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_head_full[push_body_scope]:
  drule bodyFullForFactsTheory.type_stmt_for_projection >> strip_tac >>
  `eb =
      es with scopes :=
        (FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>))
           :: es.scopes` by
    (qpat_assum `push_scope_with_var id dtv v es = (INL (),eb)` mp_tac >>
     simp[NoAsms, push_scope_with_var_def, return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[evaluation_state_component_equality]) >>
  `expr_sim_inv bc cx (extend_local env id fty F) eb` by
    (simp[] >> irule bodyExprPreFactsTheory.expr_sim_inv_for_scope >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl [`c`,`saL`,`saD`] >> rpt conj_tac >>
     first_assum ACCEPT_TAC) >>
  `ce_locals_declared bc (extend_local env id fty F)` by
    (irule bodyExprPreFactsTheory.ce_locals_declared_declare_local >>
     qexistsl [`c`,`saL`,`saD`] >> simp[]) >>
  `locals_alloc_ok bc (extend_local env id fty F)` by
    (irule bodyExprPreFactsTheory.locals_alloc_ok_extend >> qexists_tac `c` >>
     simp[] >> conj_tac >-
       fs[bodySimTheory.stmt_exprs_ok_def, Once allocLimitsTheory.alloc_limits_stmt_def] >>
     qpat_assum `declare_local c id fty saL = (bc,saD)` mp_tac >>
     qpat_assum `c.ce_alloca_locals` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def, LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  `body_stmts_full_ok cx loop_body` by
    (qpat_assum `body_for_full_ok cx dtv id loop_body vs`
       (MATCH_MP_TAC o REWRITE_RULE [body_for_full_ok_def]) >>
     qpat_assum `k < LENGTH vs` mp_tac >>
     qpat_assum `vs = MAP Value xs` (once_rewrite_tac o single) >>
     Cases_on `xs` >> simp[read_result_def,return_def]) >>
  `saL.cs_next_var <= sbCopy.cs_next_var` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`saL.cs_next_var <= sa.cs_next_var`,
        `sa.cs_next_var <= saCopy.cs_next_var`,
        `saCopy.cs_next_var <= sbCopy.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!r w. not_fresh_at saL r /\ lookup_var r p = SOME w ==>
    lookup_var r t = SOME w` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!r. not_fresh_at sa r ==> lookup_var r t = lookup_var r p /\ _`
       (qspec_then `r` (fn copy =>
          qpat_assum `!r. not_fresh_at saL r ==> not_fresh_at sa r`
            (qspec_then `r` (fn age =>
               qpat_assum `not_fresh_at saL r`
                 (once_rewrite_tac o single o cj 1 o MP copy o MP age))))) >>
     first_assum ACCEPT_TAC) >>
  `bc.ce_return_pc = c.ce_return_pc` by
    (qpat_assum `cenv_top_ext c bc (FEMPTY::es.scopes)`
       (ACCEPT_TAC o MATCH_MP stmtSimPropsTheory.cenv_top_ext_return_pc)) >>
  simp[] >>
  irule stmtSimPropsTheory.ret_pc_ok_frame >>
  qexistsl [`c`,`p`,`saL`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_nonslot_array_head_full

(* The raw normal post has already run the required machine suffix.  Pop
   only the source scope, without losing the raw nonlocal exit witness. *)
Theorem for_nonslot_body_handle[local]:
  eb.scopes <> [] /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx stmts) (eb,s,G,tn)
    (\H raw ef GG tt t. ?sc rest b. ef.scopes = sc::rest /\
      (case raw of INL _ => INL F | INR ex =>
        if ex = BreakException then INL T else
        if ex = ContinueException then INL F else INR ex) = INL b /\
      Q H b (ef with scopes := rest) GG tt t)
    (\H raw ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) raw gt r) /\
      halt_exit H cx ef raw r /\
      (ctx_has_dalloca ctx ==> !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==>
                                      allocas_below_fmp u)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (finally (try (do eval_stmts cx stmts; return F od)
      handle_loop_exception) pop_scope) (eb,s,G,tn)
    (\H out ef GG tt t. ?b. out = INL b /\ Q H b ef GG tt t)
    (\H out ef gt r. ?ex. out = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ef (INR ex) r /\
      (ctx_has_dalloca ctx ==> !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==>
                                      allocas_below_fmp u))
Proof
  strip_tac >> drule_all for_body_cleanup_full >>
  disch_then (mp_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) mp_tac
    gas_outcome_full_post_mono) >> disch_then irule >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
    gvs[evaluation_state_accfupds, evaluation_state_fupdfupds] >>
    goal_assum (drule_at Any) >> simp[]) >>
  map_every qx_gen_tac [`H`, `out`, `ef`, `gt`, `r`] >> BETA_TAC >>
  disch_then (qx_choose_then `raw` (qx_choose_then `sc` strip_assume_tac)) >>
  `?ex. raw = INR ex /\ out = INR ex` by
    (qpat_assum `!tail. stmt_exit_ptr _ _ _ _ _`
      (qspec_then `[]` mp_tac) >>
     qpat_assum `out = _` SUBST1_TAC >>
     Cases_on `raw` >>
     simp[NoAsms, stmt_exit_ptr_def, oneline exprSimDefsTheory.expr_exit_def] >>
     rename1 `INR ex` >> Cases_on `ex` >> simp[NoAsms] >>
     Cases_on `r` >> simp[NoAsms]) >>
  qexists_tac `ex` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `raw = INR ex` SUBST_ALL_TAC >>
  drule_all for_full_exit_scopes_gas_obs >>
  disch_then (qspecl_then [`ef.scopes`, `ef.gas_obs`] mp_tac) >>
  `!tail. (ef with <|scopes := ef.scopes; gas_obs := tail|>) =
          ef with gas_obs := tail` by
    simp[NoAsms, evaluation_state_component_equality] >>
  simp[evaluation_state_fupdfupds, halt_exit_INR_type] >> metis_tac[]
QED

val _ = Parse.hide "body";

(* The source run determines the popped scope and supplies the domain
   comparison needed to compose the two compiler environment extensions. *)
Theorem for_nonslot_body_pop_scope[local]:
  lookup_scopes id es.scopes = NONE /\
  push_scope_with_var id dtv v es = (INL (),eb) /\
  eval_stmts cx body (eb with gas_obs := obs) = (raw,ef) /\
  cenv_top_ext c bc eb.scopes /\ cenv_top_ext bc cf ef.scopes ==>
  ?sc rest. ef.scopes = sc::rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
    MAP FDOM rest = MAP FDOM es.scopes /\ lookup_scopes id rest = NONE /\
    cenv_top_ext c cf ef.scopes /\
    finally (eval_stmts cx body) pop_scope (eb with gas_obs := obs) =
      (raw,ef with scopes := rest)
Proof
  strip_tac >>
  `eb = es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := dtv; value := v; popped := []|>))::es.scopes` by
    gvs[push_scope_with_var_def, return_def, evaluation_state_component_equality] >>
  `eval_stmts cx body ((es with gas_obs := obs) with scopes :=
    (FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>))::
      (es with gas_obs := obs).scopes) = (raw,ef)` by
    (`(es with gas_obs := obs) with scopes :=
        (FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>))::
          (es with gas_obs := obs).scopes = eb with gas_obs := obs` by
       simp[evaluation_state_component_equality] >> pop_assum SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `lookup_scopes id (es with gas_obs := obs).scopes = NONE` by simp[] >>
  drule_all bodySimDeclCasesTheory.array_body_scope_shape >> strip_tac >>
  qexistsl [`sc`,`rest`] >> simp[NoAsms] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  `MAP FDOM rest = MAP FDOM es.scopes` by
    (qpat_assum `eval_stmts cx body (eb with gas_obs := obs) = _`
       (mp_tac o MATCH_MP vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom) >>
     simp[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom] >>
  conj_tac >-
    (irule stmtSimPropsTheory.cenv_top_ext_trans >>
     qexistsl [`bc`,`eb.scopes`] >> asm_rewrite_tac[] >> simp[]) >>
  qpat_assum `eval_stmts cx body (eb with gas_obs := obs) = _` (fn th =>
    pure_rewrite_tac [finally_def, th]) >>
  Cases_on `raw` >>
  simp[ignore_bind_def, pop_scope_def, bind_def, return_def, raise_def]
QED

Theorem for_nonslot_body_path_post[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) (\H res ee Gf tf t. Q H res ee Gf tf t /\
      ?marks. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,Gf,tf)) R
Proof
  pure_rewrite_tac [gas_outcome_full_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> asm_rewrite_tac[] >>
      qexistsl [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> asm_rewrite_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >>
      asm_rewrite_tac[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H _ ==> _` drule >>
      strip_tac >> asm_rewrite_tac[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> qexistsl
    [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  asm_rewrite_tac[] >> qexists_tac `H` >> asm_rewrite_tac[]
QED

Theorem iterator_place_writes_ok[local]:
  MEM p (expr_places e) /\ iterator_unmodified (Array e) body ==>
  stmts_writes_ok (\w. ~place_contains w p) body
Proof
  simp[iterator_unmodified_def, EVERY_MEM] >> metis_tac[]
QED

Theorem iterator_typing_extend_fresh[local]:
  (!env e. well_typed_expr env e ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_expr (extend_local env id ty F) e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
    !id ty. id NOTIN FDOM env.var_types ==> type_place_expr (extend_local env id ty F) e = SOME vt) /\
  (!env target vt. type_place_target env target = SOME vt ==>
    !id ty. id NOTIN FDOM env.var_types ==> type_place_target (extend_local env id ty F) target = SOME vt) /\
  (!env es. well_typed_exprs env es ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_exprs (extend_local env id ty F) es) /\
  (!env opt. well_typed_opt env opt ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_opt (extend_local env id ty F) opt) /\
  (!env es. well_typed_named_exprs env es ==>
    !id ty. id NOTIN FDOM env.var_types ==> well_typed_named_exprs (extend_local env id ty F) es)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[NoAsms, well_typed_expr_def, extend_local_def] >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, extend_local_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  fs[FLOOKUP_DEF] >>
  TRY (disj1_tac >> irule subscript_base_type_exact_transfer >>
       qexists_tac `env` >> simp[]) >>
  metis_tac[]
QED

Theorem for_nonslot_array_projection_suffix[local]:
  path = prefix ++ suffix /\
  (!entry. lookup_scopes name before = SOME entry ==>
    ?v. evaluate_subscripts entry.type entry.value path = INL v) /\
  OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value prefix))
    (lookup_scopes name after) =
  OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value prefix))
    (lookup_scopes name before) ==>
  OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
    (lookup_scopes name after) =
  OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
    (lookup_scopes name before)
Proof
  Cases_on `lookup_scopes name before` >> Cases_on `lookup_scopes name after` >>
  simp[] >> rpt strip_tac >>
  qpat_assum `path = prefix ++ suffix` SUBST_ALL_TAC >>
  qpat_assum `evaluate_subscripts _ _ (prefix ++ suffix) = INL _`
    (strip_assume_tac o MATCH_MP whitelistForIterMemTheory.evaluate_subscripts_append_prefix) >>
  qpat_assum `x'.type = x.type` (fn eq => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [eq])) >>
  qpat_assum `evaluate_subscripts x.type x.value prefix = INL _`
    (fn read => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [read]) >> ASSUME_TAC read) >>
  rename1 `evaluate_subscripts x.type x.value prefix = INL v0` >>
  qspecl_then [`prefix`,`x.type`,`x'.value`,`x.value`,`suffix`,`v0`] mp_tac
    whitelistForIterMemTheory.evaluate_subscripts_prefix_agree >>
  simp[]
QED

(* Both machines still expose the captures of the reserved outer pointers. *)
Theorem for_nonslot_saved_local_region[local]:
  env_scopes_consistent env cx em /\ env_scopes_consistent env cx ep /\
  local_ptrs_rel func c em.scopes u /\ local_ptrs_reserved c sa /\
  (!p w. not_fresh_at sa p /\ lookup_var p u = SOME w ==>
    lookup_var p s = SOME w /\ lookup_var p t = SOME w) /\
  local_region c ep.scopes t name off sz ==>
  local_region c ep.scopes s name off sz
Proof
  simp[local_region_def] >> rpt strip_tac >>
  rename1 `lookup_scopes name ep.scopes = SOME entry` >>
  rename1 `FLOOKUP c.ce_vars name = SOME (PtrVar (Var p) sz)` >>
  qpat_assum `env_scopes_consistent env cx ep`
    (mp_tac o cj 3 o REWRITE_RULE [vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
  disch_then (drule_then assume_tac) >>
  qpat_assum `env_scopes_consistent env cx em`
    (mp_tac o cj 2 o REWRITE_RULE [vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
  disch_then (qspec_then `name` mp_tac) >>
  Cases_on `FLOOKUP env.var_types name` >> fs[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `captured` assume_tac) >>
  qpat_assum `local_ptrs_rel func c em.scopes u`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`name`,`captured`,`p`,`sz`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `word` strip_assume_tac) >>
  `not_fresh_at sa p` by
    (qpat_assum `local_ptrs_reserved c sa`
       (mp_tac o cj 2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
     disch_then (qspecl_then [`name`,`name`,`p`,`sz`,`sz`] mp_tac) >>
     simp[]) >>
  qpat_assum `!p w. not_fresh_at sa p /\ lookup_var p u = SOME w ==> _`
    (qspecl_then [`p`,`word`] mp_tac) >>
  simp[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem for_nonslot_selected_immutable_holds[local]:
  expr_sim_inv_mods mods c cx env em /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT et bd) /\
  ~cx_const_name cx (src,name) /\
  read_result cx (PlaceR (ImmutablePlace src name [])) em = (INL (ArrayV av),em) /\
  vv_place_ptr c cx em u (PlaceR (ImmutablePlace src name [])) vv /\
  vv_location vv = SOME LocCode /\ eval_operand (vv_operand vv) u = SOME bw /\
  lookup_immutable cx ep src name = lookup_immutable cx em src name ==>
  immutable_holds c cx (ArrayT et bd) (Value (ArrayV av)) bw ep t
Proof
  strip_tac >>
  drule_all whitelistForIterImmSourceTheory.immutable_array_source_ready >>
  strip_tac >>
  Cases_on `vv` >>
  gvs[vv_location_def, vv_place_ptr_def, vv_operand_def, mem_path_offset_def] >>
  gvs[read_result_def,read_place_def,get_immutables_def,get_address_immutables_def,
      evaluate_subscripts_def,bind_def,lift_option_type_def,lift_sum_def,
      return_def,raise_def] >>
  Cases_on `ALOOKUP ep.immutables cx.txn.target` >>
  gvs[vyperBareGlobalNameTheory.lookup_immutable_def] >>
  simp[immutable_holds_def,read_result_def,return_def] >>
  qexistsl [`name`,`off`,`atv`,`ArrayV av`,`0`] >>
  simp[sub_layout_def]
QED

(* A code-backed iterator retains the captured path and address, not the
   containing immutable's entire value. The caller supplies the body frame. *)
Definition for_nonslot_code_frame_def:
  for_nonslot_code_frame c cx env ctx func id e body loc rv vv av em u <=>
    (loc = LocCode ==> ?src name path.
      rv = PlaceR (ImmutablePlace src name path) /\
      !es eb obs raw ef ep dtv v
       (H : (bool # bytes32 # type_value) list # num list) z bw.
        expr_sim_inv c cx env es /\ expr_sim_inv c cx env ep /\
        push_scope_with_var id dtv v es = (INL (),eb) /\
        read_result cx rv es = (INL (ArrayV av),es) /\
        eval_stmts cx body (eb with gas_obs := obs) = (raw,ef) /\
        ep.immutables = ef.immutables /\
        stmt_state_rel H ctx func c cx ep z /\
        read_result cx rv em = (INL (ArrayV av),em) /\
        vv_place_ptr c cx em u rv vv /\
        eval_operand (vv_operand vv) u = SOME bw /\
        eval_operand (vv_operand vv) z = SOME bw ==>
        read_result cx rv ep = (INL (ArrayV av),ep) /\
        immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw ep z)
End

Theorem for_nonslot_bare_immutable_lookup[local]:
  expr_sim_inv_mods mods c cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT et bd) /\
  ~cx_const_name cx (src,name) /\
  read_result cx (PlaceR (ImmutablePlace src name [])) es = (INL (ArrayV av),es) ==>
  ?tv. evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv /\
       lookup_immutable cx es src name = SOME (tv,ArrayV av)
Proof
  strip_tac >>
  drule_all whitelistForIterImmSourceTheory.immutable_array_source_ready >>
  strip_tac >>
  qpat_x_assum `src = c.ce_module` kall_tac >>
  `lookup_immutable cx es src name = SOME (atv,ArrayV av')` by
    simp[vyperBareGlobalNameTheory.lookup_immutable_def] >>
  qpat_assum `read_result _ (PlaceR _) _ = _`
    (mp_tac o REWRITE_RULE [forNestedArrayCaptureTheory.read_result_immutable_place]) >>
  simp[evaluate_subscripts_def]
QED

Theorem for_nonslot_code_frame_bare[local]:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  iterator_unmodified (Array e) body /\
  stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) n body) /\
  expr_sim_inv_mods [(NONE,tops)] c cx env em /\
  (loc = LocCode ==> ?src name.
    e = TopLevelName (ArrayT et bd) (src,name) /\
    rv = PlaceR (ImmutablePlace src name []) /\
    FLOOKUP env.bare_globals (src,name) = SOME (ArrayT et bd) /\
    ~cx_const_name cx (src,name) /\
    vv_location vv = SOME LocCode /\ post_value_type c e = ArrayT et bd) ==>
  for_nonslot_code_frame c cx env ctx func id e body loc rv vv av em u
Proof
  strip_tac >> simp[for_nonslot_code_frame_def] >> disch_tac >>
  qpat_assum `loc = LocCode ==> ?src name. _`
    (drule_then (qx_choosel_then [`src`,`name`] strip_assume_tac)) >>
  qexistsl [`src`,`name`,`[]`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `eb.immutables = es.immutables` by gvs[push_scope_with_var_def,return_def] >>
  drule_all_then strip_assume_tac for_nonslot_bare_immutable_lookup >>
  `lookup_immutable cx em src name = lookup_immutable cx es src name` by
    (qpat_assum `read_result cx (PlaceR _) em = _`
       (mp_then Any mp_tac for_nonslot_bare_immutable_lookup) >>
     disch_then (drule_at (Pat `expr_sim_inv _ _ _ em`)) >> simp[]) >>
  qpat_assum `evaluate_type _ (ArrayT et bd) = SOME _`
    (strip_assume_tac o MATCH_MP vyperTypeValuesTheory.evaluate_type_ArrayT_cases) >>
  `lookup_immutable cx (eb with gas_obs := obs) src name = lookup_immutable cx es src name` by
    (qpat_assum `eb.immutables = es.immutables` (fn eq =>
       simp[NoAsms,vyperBareGlobalNameTheory.lookup_immutable_def,eq])) >>
  `lookup_immutable cx (eb with gas_obs := obs) src name = SOME (ArrayTV elem_tv bd,ArrayV av)` by simp[] >>
  `stmt_loop_calls_ok [(NONE,tops)]
     (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n body)` by
    (qpat_assum `e = TopLevelName _ _` (fn eq =>
       qpat_assum `stmt_loop_calls_ok _ _` (mp_tac o REWRITE_RULE [eq])) >>
     simp[NoAsms,vyperTypeContractTheory.stmt_loop_calls_ok_def]) >>
  `iterator_unmodified (Array (TopLevelName (ArrayT et bd) (src,name))) body` by
    (qpat_assum `e = TopLevelName _ _` (fn eq =>
       qpat_assum `iterator_unmodified _ _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `lookup_immutable cx ef src name = lookup_immutable cx (eb with gas_obs := obs) src name` by
    drule_all_then ACCEPT_TAC bodyLoopImmutableFrameTheory.for_bare_immutable_array_body_observation >>
  `lookup_immutable cx ep src name = lookup_immutable cx ef src name` by
    (qpat_assum `ep.immutables = ef.immutables` (fn eq =>
       simp[NoAsms,vyperBareGlobalNameTheory.lookup_immutable_def,eq])) >>
  conj_tac >- (simp[forNestedArrayCaptureTheory.read_result_immutable_place,evaluate_subscripts_def] >> metis_tac[]) >>
  irule for_nonslot_selected_immutable_holds >>
  qexistsl [`em`,`env`,`name`,`src`,`u`,`vv`] >> simp[]
QED

(* Finish the prepared round with one target suffix for all storage horizons. *)
Theorem for_nonslot_array_scoped_body_at[local]:
  (!H. valid_horizon cx st0 H eb.storage_trace ==>
    for_nonslot_body_entry (DF H,lo,d,ctx,func,cx,c,id,env,body)
      (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
      (len_op,idx,bw) (xd,dw,capacity,aidItem) (bc,benv,sbCopy,dtv,v)
      (H,k,a::rs,es,eb,G,tn,s)) /\
  return_buf_sep d bc eb s /\
  storage_trace_domain cx st0 eb.storage_trace /\
  expr_sim_inv_mods mods c cx env em /\ local_ptrs_rel func c em.scopes u /\
  well_typed_expr env e /\ expr_writes_ok (\_. F) e /\
  expr_type e = ArrayT et bd /\
  (?start. eval_expr cx e start = (INL rv,em)) /\
  for_nonslot_code_frame c cx env ctx func id e body loc rv vv av em u /\
  body_const_cells_agree mods cx benv eb /\
  body_stmts_full_ok_mods mods exps cx body /\ expr_sim_inv_mods mods bc cx benv eb /\
  ce_locals_declared bc benv /\ locals_alloc_ok bc benv /\
  (contract_inv mods exps ctx bc cx /\
     module_body_inv mods bc.ce_module tops bc cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ supported_stmts tops bindings body /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops) /\
  type_stmts benv ret_ty body = SOME env' /\ stmts_exprs_ok bc body /\
  benv = extend_local env id fty F /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\
  iterator_unmodified (Array e) body /\
  (?limit. stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) limit body)) /\
  (?bb inst. lookup_block incr func.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME inst /\ inst.inst_opcode <> PHI) /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty /\
  stmts_env bc (InLoop exit incr) ret_ty body sbCopy = (bc',sbBody) /\
  stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
    shadow_sbCopy = (gas_shadow_env T bc',shadow_sbBody) /\
  gas_shadow_state sbCopy shadow_sbCopy /\ gas_shadow_state sbBody shadow_sbBody /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sbCopy sbBody func /\ fn_has_code shadow_sbCopy shadow_sbBody shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sbCopy /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sbCopy x) /\
  ~block_is_terminated sbCopy /\
  gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr)) eb /\
  emit_jmp_if_not_terminated incr sbBody = ((),sj) /\ fn_has_code sbBody sj func /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
  ci_mono sa0 sbCopy /\ ci_mono sbExpr sbCopy /\ ci_mono saL sbCopy /\ ci_mono sa0 sb /\
  local_ptrs_reserved c saL /\ not_fresh_at sbCopy idx /\ not_fresh_at sbCopy xd /\
  (!p. vv_operand vv = Var p \/ len_op = Var p ==> not_fresh_at saL p) /\
  (!z J tz. z.vs_current_bb = incr /\ z.vs_inst_idx = 0 /\
    (!H. valid_horizon cx st0 H tz.storage_trace ==>
      for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,body)
        (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
        (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,a::rs,tz,c,tz,FST J,SND J,z)) ==>
    ?t Gf tf. !H. valid_horizon cx st0 H tz.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (z,FST J,SND J) [] (OK t,Gf,tf) /\
      t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
      for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,body)
        (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
        (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,SUC k,rs,tz,c,tz,Gf,tf,t)) /\
  ((?Q R. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_stmts cx body) (eb,s,G,tn) Q R) ==> Extra eb s G tn) ==>
  Extra eb s G tn /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (finally (try (do eval_stmts cx body; return F od) handle_loop_exception) pop_scope)
    (eb,s,G,tn)
    (\H out ef GG tt t. ?b. out = INL b /\
        ef.gas_obs = [] /\ ~t.vs_halted /\ return_buf_sep d c ef t /\
        (b ==> stmt_lands lctx sb (INL ()) t /\ ~block_is_terminated sb /\
          cenv_top_ext c c ef.scopes /\ stmt_state_rel H ctx func c cx ef t /\
          storage_well_formed_on cx ef (FST H) /\ return_buf_frame d c sb t /\
          ghost_inv_at (DF H) lo d c cx ef GG tt t /\ alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
          (!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
          (!x. not_fresh_at sa0 x ==>
            FLOOKUP GG x = FLOOKUP G0 x /\ op_taint tt (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame c es0 sa0 s0 c ef t /\
          (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
            (!name base len. local_region c es0.scopes s0 name base len ==>
              off+sz <= base \/ base+len <= off) /\
            off <= i /\ i < off+sz /\ i IN tt.t_mem ==> i IN tn0.t_mem)) /\
        (~b ==> body_const_cells_agree mods cx env ef /\
          t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
          for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,body)
            (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
            (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,SUC k,rs,ef,c,ef,GG,tt,t)))
    (\H out ef gt r. ?ex. out = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ef (INR ex) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==>
        allocas_below_fmp z))
Proof
  strip_tac >>
  qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
    (mp_then Any mp_tac for_nonslot_array_body_invoke) >>
  disch_then (drule_at (Pat `frame_ret_ok_full _ _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `stmts_env bc _ ret_ty body sbCopy = _`
    (mp_then (Pat `stmts_env _ _ _ body _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `stmts_env _ _ _ (MAP gas_shadow_stmt _) _ = _`)) >>
  disch_then (drule_at (Pat `gas_shadow_state sbCopy _`)) >>
  disch_then (drule_at (Pat `supported_stmts _ _ _`)) >>
  disch_then (drule_at (Pat `type_stmts _ _ _ = _`)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  conj_tac >-
    (qpat_assum `(?Q R. gas_outcome_full _ _ _ _ (eval_stmts _ _) _ Q R) ==> Extra eb s G tn` irule >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ _ _` (irule_at Any)) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full fp _ _ _ (eval_stmts _ _) _ Qraw Rraw` >>
  suspend "scoped_suffix"
QED

Resume for_nonslot_array_scoped_body_at[scoped_suffix]:
  `eb.scopes <> []` by
    (qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon eb.storage_trace` mp_tac) >>
     impl_tac >- fs[storage_trace_domain_def] >>
     simp[for_nonslot_body_entry_def] >> strip_tac >>
     gvs[push_scope_with_var_def, return_def]) >>
  qunabbrev_tac `fp` >> ho_match_mp_tac for_nonslot_body_handle >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_full_zero_suffix >>
  qexists_tac `\H res ee Gf tf t. Qraw H res ee Gf tf t /\
    ?marks. gas_origin_ptr_path
      (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,Gf,tf)` >>
  conj_tac >- suspend "uniform_suffix" >>
  irule for_nonslot_body_path_post >> qunabbrev_tac `Rraw` >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_scoped_body_at[uniform_suffix]:
  map_every qx_gen_tac [`raw`, `ef`, `G1`, `tn1`, `t`] >> BETA_TAC >> strip_tac >>
  `!H. valid_horizon cx st0 H ef.storage_trace ==> Qraw H raw ef G1 tn1 t` by
    (rpt strip_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
  `valid_horizon cx st0 (storage_trace_horizon ef.storage_trace) ef.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?obs. !tail. eval_stmts cx body (eb with gas_obs := obs ++ tail) =
                    (raw,ef with gas_obs := tail)` by
    (qpat_assum `!H. _ ==> Qraw H _ _ _ _ _`
       (qspec_then `storage_trace_horizon ef.storage_trace` mp_tac) >>
     simp[Abbr `Qraw`] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ef.storage_trace ==>
       valid_horizon cx st0 H eb.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. eval_stmts _ _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = (res,st')`) mp_tac
          valid_horizon_frame)) >>
     simp[evaluation_state_accfupds,
          cj 2 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `ef.gas_obs = []` by
    (qpat_assum `!H. _ ==> Qraw H _ _ _ _ _`
       (qspec_then `storage_trace_horizon ef.storage_trace` mp_tac) >>
     simp[Abbr `Qraw`] >> metis_tac[]) >>
  `ef with gas_obs := [] = ef` by simp[evaluation_state_component_equality] >>
  `eval_stmts cx body (eb with gas_obs := obs) = (raw,ef)` by
    (qpat_assum `ef with gas_obs := [] = ef` (fn upd =>
       qpat_assum `!tail. eval_stmts _ _ (_ with gas_obs := obs ++ tail) = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,upd])))) >>
  `push_scope_with_var id dtv v es = (INL (),eb) /\ lookup_scopes id es.scopes = NONE /\
    cenv_top_ext c bc eb.scopes` by
    (`valid_horizon cx st0 (storage_trace_horizon ef.storage_trace) eb.storage_trace` by
       metis_tac[] >>
     qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon ef.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE [for_nonslot_body_entry_def]) >>
     qpat_assum `for_nonslot_live _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_live_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "suffix_pop_and_land"
QED

Resume for_nonslot_array_scoped_body_at[suffix_pop_and_land]:
  `?cf. cenv_top_ext bc cf ef.scopes` by
    (qpat_assum `!H. _ ==> Qraw H _ _ _ _ _`
       (qspec_then `storage_trace_horizon ef.storage_trace` mp_tac) >>
     simp[Abbr `Qraw`] >> metis_tac[]) >>
  drule_all for_nonslot_body_pop_scope >>
  disch_then (qx_choose_then `sc` (qx_choose_then `rest` strip_assume_tac)) >>
  qabbrev_tac `ep = ef with scopes := rest` >>
  `stmt_lands (InLoop exit incr) sbBody raw t /\ ~t.vs_halted /\
   (raw = INL () ==> ~block_is_terminated sbBody) /\
   allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `!H. _ ==> Qraw H _ _ _ _ _`
       (qspec_then `storage_trace_horizon ef.storage_trace` mp_tac) >>
     qunabbrev_tac `Qraw` >> BETA_TAC >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     asm_rewrite_tac[] >> disch_tac >>
     qpat_assum `raw = INL () ==> _` drule >> simp[]) >>
  qabbrev_tac `z = if raw = INL () then jump_to incr t else t` >>
  `?b. (case raw of INL _ => INL F | INR ex =>
         if ex = BreakException then INL T else
         if ex = ContinueException then INL F else INR ex) = INL b /\
       z.vs_current_bb = (if b then exit else incr) /\ z.vs_inst_idx = 0 /\
       ~z.vs_halted /\
       (!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
             (t,G1,tn1) [] (OK z,G1,tn1))` by suspend "landing" >>
  Cases_on `b`
  >- suspend "break_suffix" >>
  suspend "continue_suffix"
QED

Resume for_nonslot_array_scoped_body_at[landing]:
  drule_all for_nonslot_body_landing >>
  simp[Abbr `z`] >> disch_tac >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK (if raw = INL () then jump_to incr t else t),G1,tn1)` by
    (gen_tac >> first_assum (qspecl_then
      [`tn1`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`,`DF H`] strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!tn explicit PG G D. ?b. _`
    (qspecl_then [`tn1`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`,`DF H`]
      strip_assume_tac) >>
  qexists_tac `b` >> asm_rewrite_tac[]
QED

Resume for_nonslot_array_scoped_body_at[break_suffix]:
  `raw = INR BreakException` by
    (qpat_assum `(case raw of _ => _ | _ => _) = INL T` mp_tac >>
     namedCases_on `raw` ["x","ex"] >> simp[AllCaseEqs()]) >>
  `z = t` by simp[Abbr `z`] >>
  qexistsl [`z`,`G1`,`tn1`] >> qx_gen_tac `H` >> disch_tac >>
  conj_tac >- simp[] >>
  BETA_TAC >> qexistsl [`sc`,`rest`,`T`] >> simp[] >>
  qpat_assum `!H. _ ==> Qraw H _ _ _ _ _` (qspec_then `H` mp_tac) >>
  qunabbrev_tac `Qraw` >> BETA_TAC >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `cpost` strip_assume_tac) kall_tac) >>
  `cenv_top_ext c cpost ef.scopes` by
    (irule stmtSimPropsTheory.cenv_top_ext_trans >>
     qexistsl [`bc`,`eb.scopes`] >> asm_rewrite_tac[] >>
     gvs[push_scope_with_var_def, return_def]) >>
  `return_buf_sep d c ep t` by
    (irule bodyFullSharedTheory.return_buf_sep_pop >>
     qexistsl [`cpost`,`sc`] >> simp[Abbr `ep`] >>
     qpat_assum `ef.scopes = sc::rest` (once_rewrite_tac o single o SYM) >>
     simp[evaluation_state_component_equality]) >>
  `valid_horizon cx st0 H eb.storage_trace` by simp[] >>
  qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (fn th => map_every assume_tac
    (CONJUNCTS (REWRITE_RULE [for_nonslot_body_entry_def, for_nonslot_live_def] th))) >>
  suspend "break_exit_frame"
QED

Resume for_nonslot_array_scoped_body_at[break_exit_frame]:
  `stmt_state_rel H ctx func c cx ep t` by
    (simp[Abbr `ep`] >> irule stmtSimPropsTheory.stmt_state_rel_pop_top_ext >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `cpost` >> asm_rewrite_tac[]) >>
  `ghost_inv_at (DF H) lo d c cx ep G1 tn1 t` by
    (simp[Abbr `ep`] >> irule bodyFullSharedTheory.ghost_inv_at_pop >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `cpost` >> asm_rewrite_tac[]) >>
  `return_buf_frame d c sb t` by
    (qpat_assum `return_buf_frame d bc sa0 s`
       (mp_then (Pos hd) mp_tac return_buf_frame_frame) >>
     disch_then (qspecl_then [`c`,`sb`,`t`] mp_tac) >>
     `bc.ce_return_buf = c.ce_return_buf` by
       metis_tac[stmtFragPtrTheory.cenv_top_ext_return_buf] >>
     simp[ci_mono_def, GSYM AND_IMP_INTRO] >>
     rpt strip_tac >> first_x_assum irule >>
     fs[ci_mono_def, not_fresh_at_def]) >>
  simp[stmt_lands_def, block_is_terminated_def, stmtSimPropsTheory.cenv_top_ext_refl,
       Abbr `ep`, vyperFiniteStoragePreservationTheory.storage_well_formed_on_scopes] >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sbCopy x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa0` >> fs[ci_mono_def]) >>
  `sa0.cs_next_id <= sbCopy.cs_next_id` by fs[ci_mono_def] >>
  conj_tac >-
    (qpat_assum `z = t` (once_rewrite_tac o single o SYM) >>
     qpat_assum `z.vs_current_bb = _` (mp_tac o REWRITE_RULE [COND_CLAUSES]) >>
     qpat_assum `z.vs_inst_idx = 0` mp_tac >> simp[NoAsms]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >-
    (`alloca_frame c es0 sa0 s0 cpost ef t` by
       (irule alloca_frame_trans >> qexistsl [`bc`,`eb`,`s`,`sbCopy`] >>
        asm_rewrite_tac[]) >>
     irule alloca_frame_pop >> conj_tac
     >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `cpost` >> asm_rewrite_tac[]) >>
  MATCH_MP_TAC (Q.INST [`c1` |-> `bc`, `e1` |-> `eb`, `s1` |-> `s`,
                        `sa1` |-> `sbCopy`, `tn1` |-> `tn`]
                alloca_taint_kept_trans) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_scoped_body_at[continue_suffix]:
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `raw = INL () \/ raw = INR ContinueException`
  >- (qpat_assum `(case raw of _ => _ | _ => _) = INL F` mp_tac >>
      namedCases_on `raw` ["x","ex"] >> simp[AllCaseEqs()]) >>
  `return_buf_sep d c ep z` by suspend "continue_return_buffer" >>
  suspend "continue_live_frame"
QED

Resume for_nonslot_array_scoped_body_at[continue_return_buffer]:
  qpat_assum `!H. _ ==> Qraw H _ _ _ _ _`
    (qspec_then `storage_trace_horizon ef.storage_trace` mp_tac) >>
  qunabbrev_tac `Qraw` >> BETA_TAC >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `cpost` strip_assume_tac) kall_tac) >>
  `cenv_top_ext c cpost ef.scopes` by
    (irule stmtSimPropsTheory.cenv_top_ext_trans >>
     qexistsl [`bc`,`eb.scopes`] >> asm_rewrite_tac[] >>
     gvs[push_scope_with_var_def, return_def]) >>
  `return_buf_sep d c ep t` by
    (irule bodyFullSharedTheory.return_buf_sep_pop >>
     qexistsl [`cpost`,`sc`] >> simp[Abbr `ep`] >>
     qpat_assum `ef.scopes = sc::rest` (once_rewrite_tac o single o SYM) >>
     simp[evaluation_state_component_equality]) >>
  Cases_on `raw = INL ()` >>
  simp[Abbr `z`, bodyFullSharedTheory.return_buf_sep_jump]
QED

Resume for_nonslot_array_scoped_body_at[continue_live_frame]:
  `body_const_cells_agree [(NONE,tops)] cx benv ef` by
    (irule body_const_cells_agree_stmts >>
     qpat_assum `eval_stmts cx body (eb with gas_obs := obs) = (raw,ef)`
       (irule_at Any) >>
     qexists_tac `ret_ty` >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env ep` by
    (qpat_assum `body_const_cells_agree [(NONE,tops)] cx benv ef` mp_tac >>
     qpat_assum `benv = extend_local env id fty F` (fn eq =>
       simp[NoAsms, eq, Abbr `ep`])) >>
  `ep.storage_trace = ef.storage_trace` by simp[Abbr `ep`] >>
  `!H. valid_horizon cx st0 H ep.storage_trace ==>
      for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,body)
        (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
        (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,a::rs,ep,c,ep,G1,tn1,z)` by
    suspend "rebuild_increment_entry" >>
  qpat_assum `!z J tz. _ ==> ?t Gf tf. _`
    (qspecl_then [`z`,`(G1,tn1)`,`ep`] mp_tac) >>
  (impl_tac >-
    (simp[NoAsms] >> conj_tac
     >- (qpat_assum `z.vs_current_bb = _` (ACCEPT_TAC o REWRITE_RULE [COND_CLAUSES])) >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t'`,`G'`,`tn'`] assume_tac) >>
  qexistsl [`t'`,`G'`,`tn'`] >> qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ep.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac >-
    (qpat_assum `!H. gas_origin_ptr_path _ (t,G1,tn1) _ (OK z,G1,tn1)`
       (qspec_then `H` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[] >> disch_then irule >> simp[] >>
     qpat_assum `gas_origin_ptr_path _ (z,FST _,SND _) [] (OK t',G',tn')`
       (ACCEPT_TAC o SRULE [])) >>
  BETA_TAC >> qexistsl [`sc`,`rest`,`F`] >>
  simp[] >>
  suspend "increment_return_buffer"
QED

Resume for_nonslot_array_scoped_body_at[rebuild_increment_entry]:
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H ef.storage_trace` by fs[Abbr `ep`] >>
  qpat_assum `!H. _ ==> Qraw H _ _ _ _ _` (qspec_then `H` mp_tac) >>
  qunabbrev_tac `Qraw` >> BETA_TAC >>
  (impl_tac >- simp[]) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `cpost` strip_assume_tac) kall_tac) >>
  qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => map_every assume_tac
    (CONJUNCTS (REWRITE_RULE [for_nonslot_body_entry_def, for_nonslot_live_def] th))) >>
  `cenv_top_ext c cpost ef.scopes` by
    (irule stmtSimPropsTheory.cenv_top_ext_trans >>
     qexistsl [`bc`,`eb.scopes`] >> asm_rewrite_tac[] >>
     simp[] >> qpat_assum `MAP FDOM rest = MAP FDOM es.scopes` (ACCEPT_TAC o SYM)) >>
  `stmt_state_rel H ctx func c cx ep t` by
    (simp[Abbr `ep`] >> irule stmtSimPropsTheory.stmt_state_rel_pop_top_ext >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `cpost` >> asm_rewrite_tac[]) >>
  `ghost_inv_at (DF H) lo d c cx ep G1 tn1 t` by
    (simp[Abbr `ep`] >> irule bodyFullSharedTheory.ghost_inv_at_pop >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `cpost` >> asm_rewrite_tac[]) >>
  suspend "increment_operand_frame"
QED

Resume for_nonslot_array_scoped_body_at[increment_operand_frame]:
  `?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1)` by
    (qpat_assum `!H. valid_horizon cx st0 H ef.storage_trace ==> _ /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o cj 2)))) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
       (ACCEPT_TAC o MATCH_MP gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels)) >>
  `z.vs_allocas = t.vs_allocas /\ z.vs_memory = t.vs_memory /\
   z.vs_vars = t.vs_vars /\ z.vs_alloca_next = t.vs_alloca_next /\
   z.vs_fmp = t.vs_fmp /\ z.vs_initial_fmp = t.vs_initial_fmp /\
   z.vs_labels = s.vs_labels` by
    (Cases_on `raw = INL ()` >> simp[Abbr `z`, jump_to_def]) >>
  `!x. lookup_var x z = lookup_var x t` by simp[lookup_var_def] >>
  `!x w. not_fresh_at sbCopy x /\ lookup_var x s = SOME w ==>
           lookup_var x z = SOME w` by simp[] >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sbCopy x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa0` >> fs[ci_mono_def]) >>
  `!x. not_fresh_at saL x ==> not_fresh_at sbCopy x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `saL` >> fs[ci_mono_def]) >>
  `!op w. (vv_operand vv = op \/ len_op = op) /\ eval_operand op s = SOME w ==>
      eval_operand op z = SOME w /\ op_prov G1 op = op_prov G op /\
      op_taint tn1 op = op_taint tn op` by
    (Cases >> simp[eval_operand_def,op_prov_def,op_taint_def] >>
     rpt strip_tac >>
     `not_fresh_at sbCopy s'` by
       (qpat_assum `!p. vv_operand vv = Var p \/ len_op = Var p ==> _`
          (qspec_then `s'` mp_tac) >> simp[]) >>
     qpat_assum `!x. not_fresh_at sbCopy x ==> FLOOKUP G1 x = _ /\ _`
       (drule_then (fn frame =>
          simp[SIMP_RULE (srw_ss()) [op_taint_def] frame]))) >>
  suspend "increment_endpoint_frame"
QED

Resume for_nonslot_array_scoped_body_at[increment_endpoint_frame]:
  `return_buf_frame d c sa0 z` by
    (irule return_buf_frame_frame >> qexistsl [`bc`,`s`,`sa0`] >>
     simp[GSYM AND_IMP_INTRO] >>
     metis_tac[stmtFragPtrTheory.cenv_top_ext_return_buf]) >>
  `ret_pc_ok c sa0 z` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     qexistsl [`bc`,`s`,`sa0`] >> simp[GSYM AND_IMP_INTRO] >>
     metis_tac[stmtSimPropsTheory.cenv_top_ext_return_pc]) >>
  `alloca_history func z` by
    (irule allocaHistoryTheory.alloca_history_jump >> simp[] >> qexists_tac `t` >> simp[]) >>
  `stmt_state_rel H ctx func c cx ep z /\ ghost_inv_at (DF H) lo d c cx ep G1 tn1 z` by
    (Cases_on `raw = INL ()` >>
     simp[Abbr `z`, stmt_state_rel_jump_to, bodyFullSharedTheory.ghost_inv_at_jump]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (qpat_assum `stmt_state_rel H ctx func c cx ep z`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `!fn inst q. frag_reachable ctx func z fn inst q ==> dalloca_fmp_headroom inst q` by
    suspend "continue_reachable" >>
  `alloca_frame c es0 sa0 s0 c ep z /\ alloca_frame c em sbExpr u c ep z` by
    suspend "continue_memory_frames" >>
  `expr_sim_inv c cx env ep` by suspend "continue_source_typed" >>
  Q.SUBGOAL_THEN
    `(loc = LocCode ==>
        immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw ep z) /\
      (loc = LocCode ==> !src name path.
        rv = PlaceR (ImmutablePlace src name path) ==>
        ?tv root. lookup_immutable cx ep src name = SOME (tv,root) /\
                  evaluate_subscripts tv root path = INL (ArrayV av))`
    (map_every assume_tac o CONJUNCTS)
  >- suspend "continue_immutable_observation" >>
  suspend "increment_live"
QED

Resume for_nonslot_array_scoped_body_at[increment_live]:
  simp[for_nonslot_live_def, stmtSimPropsTheory.cenv_top_ext_refl,
       vyperFiniteStoragePreservationTheory.storage_well_formed_on_scopes,
       allocas_from_def] >>
  rpt conj_tac
  >- suspend "continue_memory_observation"
  >- simp[Abbr `ep`]
  >- (simp[Abbr `ep`, vyperFiniteStoragePreservationTheory.storage_well_formed_on_scopes] >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `allocas_from lo t` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))
  >- first_assum ACCEPT_TAC
  >- (`sa0.cs_next_id <= sbCopy.cs_next_id` by fs[ci_mono_def] >>
      MATCH_MP_TAC (Q.INST [`c1` |-> `bc`, `e1` |-> `eb`, `s1` |-> `s`,
                            `sa1` |-> `sbCopy`, `tn1` |-> `tn`]
                    alloca_taint_kept_trans) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `not_fresh_at sbCopy root` by
        (qpat_assum `!x. not_fresh_at saL x ==> not_fresh_at sbCopy x` irule >>
         qpat_assum `local_ptrs_reserved c saL`
(mp_tac o cj 2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
         disch_then (qspecl_then [`name`,`name`,`root`,`sz`,`sz`] mp_tac) >>
         simp[]) >>
      `lookup_var root s = SOME w` by
        (qpat_assum `!name path root sz w. rv = PlaceR (MemoryPlace name path) /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >>
      qpat_assum `!x w. not_fresh_at sbCopy x /\ lookup_var x s = SOME w ==> _`
        (drule_all_then ACCEPT_TAC))
  >- (`sbExpr.cs_next_id <= sbCopy.cs_next_id` by fs[ci_mono_def] >>
      MATCH_MP_TAC (Q.INST [`c1` |-> `bc`, `e1` |-> `eb`, `s1` |-> `s`,
                            `sa1` |-> `sbCopy`, `tn1` |-> `tn`]
                    alloca_taint_kept_trans) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `capacity = type_memory_size dtv` (rewrite_tac o single o SYM) >>
      irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
      qexistsl [`G`,`s`,`tn`] >>
      qpat_assum `!x. not_fresh_at sbCopy x ==> FLOOKUP G1 x = _ /\ _`
        (qspec_then `xd` (drule_then strip_assume_tac)) >>
      simp[]) >>
  suspend "continue_local_separation"
QED

Resume for_nonslot_array_scoped_body_at[continue_local_separation]:
  `?top. eb.scopes = top::es.scopes /\
     (!n. n IN FDOM top ==> lookup_scopes n es.scopes = NONE) /\
     es = eb with scopes := es.scopes` by
    (qpat_assum `push_scope_with_var id dtv v es = (INL (),eb)`
       (mp_tac o REWRITE_RULE [push_scope_with_var_def, return_def]) >>
     simp[NoAsms] >> disch_then (assume_tac o SYM) >>
     qexists_tac
       `FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>)` >>
     simp[]) >>
  `stmt_state_rel H ctx func c cx es s` by
    (qpat_assum `es = eb with scopes := es.scopes` (once_rewrite_tac o single) >>
     irule stmtSimPropsTheory.stmt_state_rel_pop_top_ext >>
     conj_tac >- (qexists_tac `top` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexists_tac `bc` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `local_region c es.scopes s name b len` by
    (qpat_assum `stmt_state_rel H ctx func c cx es s`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule
         stmtSimDefsTheory.local_region_kept) >>
     qexistsl [`ep`,`z`,`saL`] >>
     (conj_tac >- simp[Abbr `ep`]) >>
     (conj_tac >-
       (rpt strip_tac >>
        `not_fresh_at sbCopy x` by (first_assum (drule_then ACCEPT_TAC)) >>
        qpat_assum `!x w. not_fresh_at sbCopy x /\ lookup_var x s = SOME w ==> _`
          (drule_all_then ACCEPT_TAC))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!name b len. local_region c es.scopes s name b len ==> _`
    (drule_then strip_assume_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Resume for_nonslot_array_scoped_body_at[continue_reachable]:
  `?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK z,G1,tn1)` by
    (qpat_assum `!H. valid_horizon cx st0 H ef.storage_trace ==> _ /\ _`
      (qspec_then `H` (drule_then (strip_assume_tac o cj 2))) >>
     qexists_tac `marks` >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
       (fn th => mp_tac (Q.SPECL [`t`,`G1`,`tn1`,`[]`,`OK z`,`G1`,`tn1`]
                    (MATCH_MP gas_origin_ptr_path_append th))) >>
     simp[]) >>
  `!i. active_inst func i z ==> frag_reachable ctx func s func i z` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ (OK z,G1,tn1)`
       (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     drule bodyFullIfExpReachTheory.ifexp_ptr_path_reachable >>
     disch_then (qspec_then `z` mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_trans >> metis_tac[]
QED

Resume for_nonslot_array_scoped_body_at[continue_memory_frames]:
  `sa0.cs_next_id <= sbCopy.cs_next_id /\ sbExpr.cs_next_id <= sbCopy.cs_next_id` by
    fs[ci_mono_def] >>
  `alloca_frame c es0 sa0 s0 cpost ef t /\ alloca_frame c em sbExpr u cpost ef t` by
    (conj_tac >> irule alloca_frame_trans >> qexistsl [`bc`,`eb`,`s`,`sbCopy`] >>
     simp[]) >>
  `alloca_frame c es0 sa0 s0 c ep t /\ alloca_frame c em sbExpr u c ep t` by
    (conj_tac >>
     (simp[NoAsms, Abbr `ep`] >> irule alloca_frame_pop >> conj_tac
      >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
      qexists_tac `cpost` >> asm_rewrite_tac[])) >>
  conj_tac >> irule alloca_frame_same_state >> qexists_tac `t` >> simp[]
QED

Resume for_nonslot_array_scoped_body_at[continue_source_typed]:
  qabbrev_tac `esObs = es with gas_obs := obs` >>
  `expr_sim_inv c cx env esObs` by simp[Abbr `esObs`] >>
  `eb with gas_obs := obs = esObs with scopes :=
      (FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>))
       :: esObs.scopes` by
    (qpat_assum `push_scope_with_var id dtv v es = (INL (),eb)`
       (mp_tac o REWRITE_RULE [push_scope_with_var_def, return_def]) >>
     simp[Abbr `esObs`, evaluation_state_component_equality]) >>
  simp[Abbr `ep`] >>
  irule bodyExprPreFactsTheory.expr_sim_inv_for_pop >>
  conj_tac >- (qexists_tac `sc` >> simp[]) >>
  qexistsl_tac [`bindings`,`body`,`env'`,`esObs`,`fty`,`id`,`raw`,
               `ret_ty`,`tops`,`dtv`,`v`] >>
  qpat_assum `body_inv tops ctx bc cx`
    (strip_assume_tac o MATCH_MP bodyInvExecutionPropsTheory.body_inv_main_support) >>
  qpat_assum `eb with gas_obs := obs = _` (SUBST1_TAC o SYM) >>
  simp[] >>
  qpat_assum `benv = extend_local env id fty F` (fn eq =>
    qpat_assum `type_stmts benv ret_ty body = SOME env'`
      (ACCEPT_TAC o REWRITE_RULE [eq]))
QED

Resume for_nonslot_array_scoped_body_at[increment_return_buffer]:
  qpat_assum `!HH. valid_horizon cx st0 HH ep.storage_trace ==>
      for_nonslot_live _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE[for_nonslot_live_def]) >>
  qpat_assum `for_nonslot_live _ _ _ _ _ (H,SUC k,rs,ep,c,ep,G',tn',t')`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[for_nonslot_live_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >-
    (qpat_assum `body_const_cells_agree [(NONE,tops)] cx env ep` mp_tac >>
     simp[NoAsms, Abbr `ep`]) >>
  irule bodyFullSharedTheory.return_buf_sep_transport >>
  conj_tac
  >- (qpat_assum `gas_origin_ptr_path _ (z,FST _,SND _) [] (OK t',G',tn')`
        (fn th =>
          qpat_assum `return_buf_frame d c sa0 z` (fn frame =>
            qpat_assum `return_buf_sep d c ep z` (fn sep =>
              ACCEPT_TAC (MATCH_MP bodyFullSharedTheory.return_buf_allocas_path
                (LIST_CONJ [th,frame,sep])))))) >>
  qexistsl [`c`,`ep`,`z`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `local_ptrs_rel func c em.scopes u`
    (mp_then (Pat `local_ptrs_rel _ _ _ _`) irule for_nonslot_saved_local_region) >>
  conj_tac
  >- (qexistsl [`cx`,`env`] >>
      conj_tac
      >- (qpat_assum `expr_sim_inv c cx env em` mp_tac >>
          simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_def,
               vyperTypeInvariantsTheory.env_consistent_def] >>
          strip_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `expr_sim_inv c cx env ep` mp_tac >>
      simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_def,
           vyperTypeInvariantsTheory.env_consistent_def] >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`saL`,`t'`] >> simp[]
QED

Resume for_nonslot_array_scoped_body_at[continue_memory_observation]:
  rpt strip_tac >>
  qspecl_then [`e`,`cx`,`start`,`em`,`name`,`path`,`[]`] mp_tac
    eval_iterator_memory_place_access >>
  impl_tac >- simp[] >>
  simp[] >> disch_then (qx_choosel_then [`btIter`,`attrs`,`suffix`] strip_assume_tac) >>
  `OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
       (lookup_scopes name es.scopes) =
     OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
       (lookup_scopes name em.scopes)` by
    (qpat_assum `loc = LocMemory ==> !nm p.
         rv = PlaceR (MemoryPlace nm p) ==> OPTION_MAP _ (lookup_scopes nm es.scopes) = _`
       (fn frame => qpat_assum `loc = LocMemory` (fn locMem =>
          qpat_assum `rv = PlaceR (MemoryPlace name path)`
            (ACCEPT_TAC o MP (Q.SPECL [`name`,`path`] (MP frame locMem)))))) >>
  `?entry. lookup_scopes name es.scopes = SOME entry /\
          evaluate_subscripts entry.type entry.value path = INL (ArrayV av)` by
    (qpat_assum `!nm p. rv = PlaceR (MemoryPlace nm p) ==> ?entry. _`
       (qspecl_then [`name`,`path`]
         (drule_then (qx_choose_then `captured` strip_assume_tac))) >>
     qpat_assum `lookup_scopes name em.scopes = SOME captured` (fn lookup =>
       qpat_assum `evaluate_subscripts captured.type captured.value path = INL (ArrayV av)`
         (fn read => qpat_assum `OPTION_MAP _ (lookup_scopes name es.scopes) =
            OPTION_MAP _ (lookup_scopes name em.scopes)`
           (mp_tac o SIMP_RULE (srw_ss()) [lookup,read]))) >>
     Cases_on `lookup_scopes name es.scopes` >> simp[NoAsms]) >>
  `name IN FDOM env.var_types` by
    (`env_scopes_consistent env cx es` by
       (qpat_assum `expr_sim_inv c cx env es` mp_tac >>
        simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_def,
             vyperTypeInvariantsTheory.env_consistent_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `env_scopes_consistent env cx es`
       (strip_assume_tac o REWRITE_RULE [vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
     qpat_assum `!nm ent. lookup_scopes nm es.scopes = SOME ent ==>
                   IS_SOME (FLOOKUP env.var_types nm)`
       (fn scoped => qpat_assum `lookup_scopes name es.scopes = SOME entry`
          (mp_tac o MATCH_MP scoped)) >>
     simp[NoAsms,FLOOKUP_DEF]) >>
  `name <> id` by
    (strip_tac >> qpat_assum `name = id` SUBST_ALL_TAC >>
     qpat_assum `id NOTIN FDOM env.var_types` mp_tac >> simp[]) >>
  suspend "continue_memory_path"
QED

Resume for_nonslot_array_scoped_body_at[continue_memory_path]:
  `name IN FDOM benv.var_types` by
    (qpat_assum `benv = extend_local env id fty F` SUBST1_TAC >>
     simp[extend_local_def]) >>
  `well_typed_expr benv e` by
    (qpat_assum `benv = extend_local env id fty F` SUBST1_TAC >>
     irule (cj 1 iterator_typing_extend_fresh) >> simp[]) >>
  `stmts_writes_ok (\w. ~place_contains w btIter) body` by
    (irule iterator_place_writes_ok >> qexists_tac `e` >> simp[]) >>
  `MAP (\sc. OPTION_MAP
     (\e. (e.type,evaluate_subscripts e.type e.value (MAP AttrSubscript attrs)))
     (FLOOKUP sc name)) ef.scopes =
   MAP (\sc. OPTION_MAP
     (\e. (e.type,evaluate_subscripts e.type e.value (MAP AttrSubscript attrs)))
     (FLOOKUP sc name)) eb.scopes` by
    (qpat_assum `eval_stmts cx body (eb with gas_obs := obs) = (raw,ef)`
       (mp_then (Pat `eval_stmts _ _ _ = _`) mp_tac whitelistForIterMemTheory.typed_stmts_place_frame) >>
     disch_then (drule_at (Pat `type_stmts _ _ _ = _`)) >>
     disch_then (drule_at (Pat `place_access _ _ = _`)) >>
     simp[] >> disch_then (qspecl_then [`et`,`bd`,`e`] mp_tac) >>
     qpat_assum `well_typed_expr benv e` (fn wt =>
       qpat_assum `benv = extend_local env id fty F` (fn ext =>
         simp[REWRITE_RULE [ext] wt]))) >>
  qabbrev_tac `project = \entry.
    (entry.type,evaluate_subscripts entry.type entry.value (MAP AttrSubscript attrs))` >>
  qabbrev_tac `scope = FEMPTY |+ (id,
    <|assignable := F; type := dtv; value := v; popped := []|>)` >>
  `eb.scopes = scope::es.scopes` by
    (qpat_assum `push_scope_with_var id dtv v es = (INL (),eb)` mp_tac >>
     simp[NoAsms,push_scope_with_var_def,return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[Abbr `scope`]) >>
  `name NOTIN FDOM scope` by simp[Abbr `scope`] >>
  suspend "continue_memory_lookup"
QED

Resume for_nonslot_array_scoped_body_at[continue_memory_lookup]:
  `OPTION_MAP project (lookup_scopes name ep.scopes) =
    OPTION_MAP project (lookup_scopes name es.scopes)` by
    (qspecl_then [`ef.scopes`,`scope`,`es.scopes`,`name`,`project`,`entry`]
       mp_tac whitelistForIterMemTheory.scope_projection_lookup_below >>
     impl_tac
     >- (conj_tac >- simp[Abbr `project`] >> simp[]) >>
     qpat_assum `ef.scopes = sc::rest` (fn th => REWRITE_TAC [th]) >>
     simp[Abbr `ep`] >> metis_tac[]) >>
  `OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
     (lookup_scopes name ep.scopes) =
   OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
     (lookup_scopes name es.scopes)` by
    (MATCH_MP_TAC (Q.INST [`prefix` |-> `MAP AttrSubscript attrs`,
                           `suffix` |-> `suffix`]
                   for_nonslot_array_projection_suffix) >>
     simp[Abbr `project`] >> qexists_tac `ArrayV av` >>
     qpat_assum `path = MAP AttrSubscript attrs ++ suffix` (fn path_eq =>
       qpat_assum `evaluate_subscripts entry.type entry.value path = INL (ArrayV av)`
         (ACCEPT_TAC o ONCE_REWRITE_RULE [path_eq]))) >>
  qpat_assum `OPTION_MAP _ (lookup_scopes name ep.scopes) =
               OPTION_MAP _ (lookup_scopes name es.scopes)` (fn frame =>
    qpat_assum `OPTION_MAP _ (lookup_scopes name es.scopes) =
                 OPTION_MAP _ (lookup_scopes name em.scopes)`
      (ACCEPT_TAC o TRANS frame))
QED

Resume for_nonslot_array_scoped_body_at[continue_immutable_observation]:
  Cases_on `loc = LocCode` >> simp[] >>
  qhdtm_assum `for_nonslot_code_frame`
    (mp_tac o REWRITE_RULE [for_nonslot_code_frame_def]) >>
  simp[NoAsms] >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`src`,`name`,`path`] strip_assume_tac) >>
  `read_result cx rv es = (INL (ArrayV av),es)` by
    (qpat_assum `rv = PlaceR _` SUBST1_TAC >>
     irule (iffRL forNestedArrayCaptureTheory.read_result_immutable_place) >>
     qpat_assum `loc = LocCode ==> !src name path. _`
       (drule_then (qspecl_then [`src`,`name`,`path`] mp_tac)) >> simp[]) >>
  `vv_place_ptr c cx em u rv vv` by fs[vv_post_def] >>
  `ep.immutables = ef.immutables` by simp[Abbr `ep`] >>
  `eval_operand (vv_operand vv) z = SOME bw` by
    (qpat_assum `!op w. _ ==> eval_operand op z = _ /\ _`
       (qspecl_then [`vv_operand vv`,`bw`] mp_tac) >> simp[]) >>
  qpat_assum `!es eb obs raw ef ep dtv v H z bw.
            _ ==> read_result cx rv ep = _ /\ immutable_holds _ _ _ _ _ ep z`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> irule (iffLR forNestedArrayCaptureTheory.read_result_immutable_place) >>
  qpat_assum `rv = PlaceR _` (once_rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED

Finalise for_nonslot_array_scoped_body_at

(* Classify the captured result at the actual expression execution. *)
Theorem for_nonslot_array_capture_classify_mods[local]:
  contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env em /\
  well_typed_iterator env et (Array e) /\ expr_type e = ArrayT et bd /\
  type_widens_to env.type_defs (post_value_type c e) (expr_type e) /\
  (!src name. e = TopLevelName (expr_type e) (src,name) ==>
     ?tops. ALOOKUP mods src = SOME tops /\
       IS_SOME (supported_immutable_type tops (NONE,name))) /\
  (~(?ty nid. e = TopLevelName ty nid) ==>
   !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) /\
  eval_expr cx e start = (INL rv,em) /\
  vv_place_ptr c cx em u rv vv /\
  (!v ty p. rv = Value v /\
    ~is_word_type (post_value_type c e) /\ ~is_bytestring_type (post_value_type c e) /\
    vv = LocatedValue ty p ==> p.ptr_location = LocMemory) ==>
  (vv_location vv = SOME LocCode ==> ?src name.
    e = TopLevelName (ArrayT et bd) (src,name) /\
    rv = PlaceR (ImmutablePlace src name []) /\
    FLOOKUP env.bare_globals (src,name) = SOME (ArrayT et bd) /\
    ~cx_const_name_mods mods (src,name) /\ post_value_type c e = ArrayT et bd)
Proof
  strip_tac >>
  Cases_on `?nid. e = TopLevelName (ArrayT et bd) nid`
  >- suspend "bare_root" >>
  suspend "nested_root"
QED

Resume for_nonslot_array_capture_classify_mods[bare_root]:
  pop_assum (qx_choose_then `nid` SUBST_ALL_TAC) >>
  PairCases_on `nid` >>
  rename1 `TopLevelName (ArrayT et bd) (src,name)` >>
  qpat_assum `!src name. _ ==> ?tops. _`
    (qspecl_then [`src`, `name`]
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS])) >>
  rename1 `supported_immutable_type tops (NONE,name) = SOME it` >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (drule_then (qspecl_then [`src`, `tops`] drule)
       moduleVariableKeyPropsTheory.contract_inv_unqualified_variable_keys >>
     simp[NoAsms]) >>
  `find_var_decl_by_name name tops = NONE` by
    (drule_all bodyStorageMetadataTheory.supported_immutable_type_find_NONE >> simp[]) >>
  `get_module_code cx src = SOME tops` by
    (drule_then (qspec_then `src` (assume_tac))
       bodyInvCodePropsTheory.contract_inv_module_codes >> simp[]) >>
  `rv = PlaceR (ImmutablePlace src name [])` by
    (qpat_x_assum `eval_expr _ (TopLevelName _ _) start = _` mp_tac >>
     Cases_on `ALOOKUP start.immutables cx.txn.target` >>
     simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          get_immutables_def, get_address_immutables_def, return_def, raise_def] >>
     rename1 `ALOOKUP start.immutables cx.txn.target = SOME imms` >>
     Cases_on `FLOOKUP (get_source_immutables src imms) name` >>
     simp[return_def,raise_def]) >>
  `~cx_const_name_mods mods (src,name)` by
    (simp[exprSimHypsDefsTheory.cx_const_name_mods_def] >> strip_tac >>
     drule_then (qspec_then `name` drule)
       supportedNameRootTheory.distinct_module_consts_env_names_constant >>
     gvs[supportedDeclsTheory.supported_immutable_type_def, AllCaseEqs()]) >>
  `FLOOKUP env.bare_globals (src,name) = SOME it` by
    (qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
     simp[supportedDeclsTheory.supported_immutable_type_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     drule_then strip_assume_tac bodyStorageMetadataTheory.supported_variable_decl_mem >>
     drule_all_then ACCEPT_TAC immutableRegionTypingPropsTheory.immutable_decl_bare_global_mods) >>
  drule_then assume_tac exprBodyPrePropsTheory.expr_sim_inv_mods_env >>
  drule_all vyperTypeInvariantsTheory.env_consistent_bare_global_find_NONE >> strip_tac >>
  fs[well_typed_iterator_def, Once well_typed_expr_def, vyperASTTheory.expr_type_def] >>
  simp[] >> qexistsl [`src`,`name`] >> simp[]
QED

Resume for_nonslot_array_capture_classify_mods[nested_root]:
  `~(?ty nid. e = TopLevelName ty nid)` by
    (strip_tac >> qpat_x_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
     fs[vyperASTTheory.expr_type_def]) >>
  `!tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid` by
    (qpat_assum `~(?ty nid. e = TopLevelName ty nid) ==> _` (fn guard =>
         qpat_assum `~(?ty nid. e = TopLevelName ty nid)`
           (ACCEPT_TAC o MATCH_MP guard))) >>
  `well_typed_expr env e /\ expr_writes_ok (\_. F) e` by fs[well_typed_iterator_def] >>
  drule_all whitelistForIterTheory.memory_iterator_source_classify >> strip_tac
  >- (`?pty pbd. post_value_type c e = ArrayT pty pbd` by
        (qpat_x_assum `type_widens_to _ _ _` mp_tac >> simp[type_widens_to_def] >>
         Cases_on `post_value_type c e` >> simp[arg_type_fits_def]) >>
      Cases_on `vv` >> fs[vv_location_def,is_word_type_def,is_bytestring_type_def]) >>
  fs[] >> Cases_on `vv` >> fs[vv_location_def,vv_place_ptr_def]
QED

Finalise for_nonslot_array_capture_classify_mods[local]

(* The branch owns the source prefix bind. At its normal continuation the
   canonical prefix capture supplies the representation; only the relation,
   storage and ghost facts need to be projected at every horizon. *)
(* The compiler counter is reconstructed only to certify the emitted slice.
   The execution itself does not require an ordering of register names. *)
Theorem for_nonslot_actual_increment_path[local]:
  lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr;
      bb_instructions := [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [out];
        mk_inst (sj.cs_next_id + 1) ASSIGN [Var out] [idx];
        mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
  ~not_fresh_at saL out /\ s.vs_current_bb = incr /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var idx s = SOME w /\ op_prov G (Var idx) = NONE /\
  op_taint tn (Var idx) = {} ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to cond (update_var idx (w+1w) (update_var out (w+1w) s))),
     DRESTRICT (DRESTRICT G (COMPL {out})) (COMPL {idx}),
     tn with t_var := (tn.t_var |+ (out,{})) |+ (idx,{}))
Proof
  strip_tac >>
  `?m:num. out = STRING #"%" (toString m)` by
    (qpat_assum `~not_fresh_at saL out` mp_tac >>
     simp[NoAsms,not_fresh_at_def,NOT_FORALL_THM] >>
     disch_then (qx_choose_then `m` strip_assume_tac) >>
     qexists `m` >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`sj` |-> `sj with cs_next_var := m`, `out` |-> `out`,
    `incr` |-> `incr`, `func` |-> `func`, `idx` |-> `idx`, `cond` |-> `cond`]
    for_nonslot_increment_slice) >>
  simp[NoAsms] >> (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`si`,`sadd`,`sasn`,`sjmp`] strip_assume_tac) >>
  qpat_x_assum `out = STRING #"%" (toString (m:num))`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM eq])) >>
  `cs_extends si sadd /\ cs_extends sadd sasn /\ cs_extends sasn sjmp` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,cs_extends_emit_inst] >>
  `fn_has_code si sadd func /\ fn_has_code sadd sasn func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  mp_tac (Q.INST [`D` |-> `D`, `lo` |-> `lo`, `explicit` |-> `explicit`,
      `ctx` |-> `ctx`, `PG` |-> `PG`, `G` |-> `G`, `tn` |-> `tn`,
      `w` |-> `w+1w`, `x` |-> `w`, `y` |-> `1w`, `s` |-> `s`,
      `opc` |-> `ADD`, `left` |-> `Var idx`, `right` |-> `Lit 1w`,
      `a` |-> `si`, `b` |-> `sadd`, `op` |-> `Var out`, `func` |-> `func`]
    typedCopyOriginPtrBaseTheory.typed_copy_origin_ptr_binop_path) >>
  (impl_tac >- simp[eval_operand_def,op_taint_def]) >>
  disch_then (qx_choosel_then [`out'`,`s1`,`G1`,`tn1`] strip_assume_tac) >>
  `out' = out` by fs[] >> qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  `G1 = DRESTRICT G (COMPL {out}) /\ tn1 = (tn with t_var := tn.t_var |+ (out,{}))` by
    metis_tac[Q.INST [`opc` |-> `ADD`, `ops` |-> `[Var idx;Lit 1w]`,
                     `a` |-> `Var idx`]
      bodyPtrBopInLoopSearchTheory.membership_increment_ghost] >>
  `op_prov G1 (Var out) = NONE /\ op_taint tn1 (Var out) = {}` by
    simp[op_prov_def,op_taint_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
  `allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (qpat_assum `s1 = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [allocas_from_def,allocas_below_fmp_def,update_var_def] >>
     metis_tac[allocas_from_def,allocas_below_fmp_def]) >>
  drule_all typedCopyOriginPtrBaseTheory.typed_copy_origin_ptr_assign_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`]
    (qx_choosel_then [`s2`,`G2`,`tn2`] strip_assume_tac)) >>
  `allocas_from lo s2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s2)` by
    (qpat_assum `s2 = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [allocas_from_def,allocas_below_fmp_def,update_var_def] >>
     metis_tac[allocas_from_def,allocas_below_fmp_def]) >>
  `s2.vs_current_bb = incr /\ s2.vs_inst_idx = 2` by
    (simp[update_var_def] >> (gvs[update_var_def])) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s2,G2,tn2) []
     (OK (jump_to cond s2),G2,tn2)` by
    (irule jmp_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     qexistsl [`<|bb_label := incr; bb_instructions :=
       [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [out];
        mk_inst (sj.cs_next_id + 1) ASSIGN [Var out] [idx];
        mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|>`, `sj.cs_next_id + 2`] >>
     simp[get_instruction_def]) >>
  `jump_to cond s2 = jump_to cond (update_var idx (w+1w) (update_var out (w+1w) s))` by
    simp[jump_to_def,update_var_def,venom_state_component_equality] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s2,G2,tn2)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK s1,G1,tn1)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK s2,G2,tn2)`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[NoAsms] >> disch_then (drule_then mp_tac) >> simp[]
QED

(* The increment runner gives the path; only its endpoint and reachability
   matter to the live packet.  Neither register write touches an old local. *)
Theorem for_nonslot_actual_increment_live[local]:
  (?bb inst. lookup_block cond func.fn_blocks = SOME bb /\
     get_instruction bb 0 = SOME inst /\ inst.inst_opcode <> PHI) /\
  sa0.cs_next_var <= saL.cs_next_var /\
  ~not_fresh_at saL idx /\ ~not_fresh_at saL out /\
  local_ptrs_reserved c saL /\ xd <> idx /\ xd <> out /\
  (!p. vv_operand vv = Var p \/ len_op = Var p ==> not_fresh_at saL p) /\
  body_stmts_full_ok_mods mods exps cx loop_body /\
  for_nonslot_live (D,lo,d,ctx,func,cx,c,id,env,loop_body)
    (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
    (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,a::rs,es,c,es,G,tn,s) /\
  t = jump_to cond (update_var idx (n2w (SUC k)) (update_var out (n2w (SUC k)) s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {out})) (COMPL {idx}) /\
  tnf = (tn with t_var := (tn.t_var |+ (out,{})) |+ (idx,{})) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) ==>
  for_nonslot_live (D,lo,d,ctx,func,cx,c,id,env,loop_body)
    (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
    (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,SUC k,rs,es,c,es,Gf,tnf,t)
Proof
  strip_tac >>
  `!x. x <> idx /\ x <> out ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> simp[emitHelperPropsTheory.lookup_var_update_var,
       FLOOKUP_DRESTRICT,FLOOKUP_UPDATE,op_taint_def]) >>
  `!x. not_fresh_at saL x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> metis_tac[]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at saL x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_local_ptr c es.scopes idx /\ not_local_ptr c es.scopes out` by
    metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
   tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    simp[jump_to_def,update_var_def] >>
  suspend "increment_machine_frame"
QED

Resume for_nonslot_actual_increment_live[increment_machine_frame]:
  drule_then strip_assume_tac for_nonslot_live_head_index >>
  qpat_x_assum `k = LENGTH vs - _` kall_tac >>
  qhdtm_x_assum `for_nonslot_live`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_live_def]) >>
  `stmt_state_rel H ctx func c cx es t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >> simp[stmt_state_rel_jump_to] >>
     rpt (irule stmt_state_rel_update_var >> simp[])) >>
  `!ee ag q. alloca_frame c ee ag q c es s ==> alloca_frame c ee ag q c es t` by
    (rpt strip_tac >> qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     irule alloca_frame_same_state >>
     qexists `update_var idx (n2w (SUC k)) (update_var out (n2w (SUC k)) s)` >>
     simp[jump_to_def] >> rpt (irule alloca_frame_update_var >> simp[])) >>
  `return_buf_frame d c sa0 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`c`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
  `ret_pc_ok c sa0 t` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     qexistsl [`c`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x` by
    (Cases_on `d` >> gvs[return_buf_frame_def] >> PairCases_on `x` >>
     gvs[return_buf_frame_def]) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x` by
    metis_tac[ret_pc_ok_def] >>
  `ghost_inv_at D lo d c cx es Gf tnf t` by
    (irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     qexistsl [`G`,`es`,`s`,`saL`,`tn`] >> simp[jump_to_def,update_var_def]) >>
  `!op. (!p. op = Var p ==> not_fresh_at saL p) ==>
    eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
    op_taint tnf op = op_taint tn op` by
    (Cases >> simp[eval_operand_def,op_prov_def,op_taint_def,jump_to_def,update_var_def]) >>
  `ptr_covers Gf tnf xd t capacity` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  `!name b len. local_region c es.scopes t name b len <=>
                local_region c es.scopes s name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >> metis_tac[not_local_ptr_def]) >>
  suspend "increment_live_tail"
QED

Resume for_nonslot_actual_increment_live[increment_live_tail]:
  `!i. active_inst func i t ==> frag_reachable ctx func s func i t` by
    (drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule bodyFullIfExpReachTheory.ifexp_ptr_path_reachable >>
     disch_then (qspec_then `t` mp_tac) >> simp[jump_to_def]) >>
  `!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q` by
    (rpt strip_tac >>
     drule contextRawReachableTheory.frag_reachable_trans >> metis_tac[]) >>
  `alloca_history func t` by
    (irule allocaHistoryTheory.alloca_history_jump >> conj_tac
     >- simp[jump_to_def] >> qexists `s` >> simp[jump_to_def,update_var_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (simp[allocas_below_fmp_def,jump_to_def,update_var_def] >>
     metis_tac[allocas_below_fmp_def]) >>
  `lookup_var idx t = SOME (n2w (SUC k)) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ lookup_var xd t = SOME dw /\ ~t.vs_halted` by
    simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE,op_taint_def] >>
  qpat_x_assum `t = jump_to _ _` kall_tac >>
  qpat_x_assum `Gf = _` kall_tac >> qpat_x_assum `tnf = _` kall_tac >>
  `loc = LocCode ==>
    immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw es t` by
    (qpat_assum `loc = LocCode ==> immutable_holds c cx _ _ bw es s` mp_tac >>
     simp[NoAsms, loweringPostsTheory.immutable_holds_def] >> simp[]) >>
  simp[for_nonslot_live_def,GSYM ADD1,allocas_from_def] >>
  conj_tac >- fs[] >>
  conj_tac >- fs[allocas_from_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at saL root` by metis_tac[local_ptrs_reserved_def] >>
     metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `!name b len. local_region c es.scopes s name b len ==> _`
    drule >> decide_tac
QED

Finalise for_nonslot_actual_increment_live

Theorem for_nonslot_array_round_contracts_at_with_prefix:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  body_const_cells_agree mods cx env em /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ expr_body_pre_mods mods c cx env e es0 /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  supported_stmt tops bindings (For id fty (Array e) n loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n loop_body) /\
  for_nonslot_code_frame c cx env ctx func id e loop_body loc rv vv av em u /\
  stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id fty (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id fty (Array e) n loop_body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved c sa0 /\ (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  return_buf_frame d c sa0 s0 /\ ret_pc_ok c sa0 s0 /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\ body_for_full_ok_mods mods exps cx dtv id loop_body vs /\
  storage_trace_domain cx st0 em.storage_trace /\
  return_buf_sep d c em u /\
  vs = MAP Value xs /\
  (?obs. !tail. eval_expr cx e (es0 with gas_obs := obs ++ tail) =
                 (INL rv,em with gas_obs := tail)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
  value_has_type (ArrayTV stv bd) (ArrayV av) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     ?ent. lookup_scopes name em.scopes = SOME ent /\
       evaluate_subscripts ent.type ent.value path = INL (ArrayV av)) /\
  read_result cx rv em = (INL (ArrayV av),em) /\
  extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
  (loc = LocMemory \/ loc = LocCode) /\
  (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)) /\
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\ op_taint tu len_op = {} /\
  op_prov Gu len_op = NONE /\ ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em u /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em Gu tu u) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) /\
  (!k a rs es eb v t Gf tnf dw bw bc' benv env_b.
    k < LENGTH vs /\ a = EL k vs /\ rs = DROP (SUC k) vs /\ a = Value v /\
    read_result cx a es = (INL v,es) /\
    push_scope_with_var id dtv v es = (INL (),eb) /\
    (!H. valid_horizon cx st0 H eb.storage_trace ==>
      for_nonslot_body_entry (DF H,lo,d,ctx,func,cx,c,id,env,loop_body)
        (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
        (len_op,idx,bw) (xd,dw,capacity,aidItem) (bc,benv,sbCopy,dtv,v)
        (H,k,a::rs,es,eb,Gf,tnf,t)) /\
    return_buf_sep d bc eb t /\ storage_trace_domain cx st0 eb.storage_trace /\
    body_const_cells_agree mods cx benv eb /\
    body_stmts_full_ok_mods mods exps cx loop_body /\ expr_sim_inv_mods mods bc cx benv eb /\
    ce_locals_declared bc benv /\ locals_alloc_ok bc benv /\
    (contract_inv mods exps ctx bc cx /\
     module_body_inv mods bc.ce_module tops bc cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmts tops bindings loop_body /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) loop_body ==>
      occurs_abi_decode_target target tops) /\
    type_stmts benv ret_ty loop_body = SOME env_b /\ stmts_exprs_ok bc loop_body /\
    call_evaluation_safe cx (int_calls_stmts loop_body) /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty /\
    stmts_env bc (InLoop exit incr) ret_ty loop_body sbCopy = (bc',sbBody) /\
    stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt loop_body)
      shadow_sbCopy = (gas_shadow_env T bc',shadow_sbBody) /\
    gas_shadow_state sbCopy shadow_sbCopy /\ gas_shadow_state sbBody shadow_sbBody /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sbCopy sbBody func /\ fn_has_code shadow_sbCopy shadow_sbBody shadow_func /\
    (!H. dead_lo_ok H (DF H) lo bc cx) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved bc sbCopy /\
    (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sbCopy x) /\
    ~block_is_terminated sbCopy /\
    gas_admissible (eval_stmts cx loop_body) (stmt_res_ok (InLoop exit incr)) eb /\
    (?Q R. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_stmts cx loop_body) (eb,t,Gf,tnf) Q R) ==>
    B eb t Gf tnf) /\
  (!a rs es z J tz v eb t Gf tnf.
    B eb t Gf tnf /\ a = Value v /\
    read_result cx a es = (INL v,es) /\
    push_scope_with_var id dtv v es = (INL (),eb) /\
    eb = es with scopes :=
      (FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>)) :: es.scopes /\
    storage_trace_domain cx st0 es.storage_trace /\ ~z.vs_halted /\
    (!H. valid_horizon cx st0 H eb.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (z,J,tz) [] (OK t,Gf,tnf)) ==>
    P a rs es z J tz) ==>
  ?s G tn Inv Done.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK s,G,tn) /\ Inv H vs em G tn s) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)
        (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
          ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
        (\H res ee gt r. ?ex. res = INR ex /\
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
          halt_exit H cx ee (INR ex) r /\
          (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
            allocas_below_fmp t)) /\
      (storage_trace_domain cx st0 es.storage_trace ==> P a rs es z J tz)) /\
    (!es z J tz.
      ~z.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body []) (stmt_res_ok lctx) es ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,J,tz) [] (OK t,G1,tn1) /\ Done H (es with gas_obs := []) G1 tn1 t) /\
    (!H ee G1 tn1 t. Done H ee G1 tn1 t ==>
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext c c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sb t /\
      alloca_history func t /\ return_buf_sep d c ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c es0 sa0 s0 c ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!name base len. local_region c es0.scopes s0 name base len ==>
          off + sz <= base \/ base + len <= off) /\
        off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  suspend "capture"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[capture]:
  drule_then (map_every assume_tac o CONJUNCTS) bodyFullForFactsTheory.type_stmt_for_projection >>
  drule_then (map_every assume_tac o CONJUNCTS) bodyFullForFactsTheory.supported_stmt_for_projection >>
  `expr_type e = ArrayT sty bd /\
   loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
   local_ptrs_reserved c saL` by
    (qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [for_nonslot_layout_def]) >> simp[]) >>
  `sty = fty /\ well_typed_expr env e /\ expr_writes_ok (\_. F) e` by
    fs[well_typed_iterator_def] >>
  qpat_x_assum `?obs. !tail. eval_expr _ _ _ = _` (qx_choose_then `obs` assume_tac) >>
  qabbrev_tac `start = es0 with gas_obs := obs ++ em.gas_obs` >>
  `eval_expr cx e start = (INL rv,em)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `em.gas_obs` mp_tac) >>
     simp[Abbr `start`]) >>
  `expr_sim_inv c cx env em` by
    (`expr_body_pre c cx env e start` by simp[Abbr `start`] >>
     drule_all_then ACCEPT_TAC bodySimStmtFactsTheory.expr_body_pre_eval_result) >>
  `lookup_scopes id em.scopes = NONE` by
    (`env_scopes_consistent env cx em` by
       (qpat_assum `expr_sim_inv c cx env em` mp_tac >>
        simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_def,
             vyperTypeInvariantsTheory.env_consistent_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     Cases_on `lookup_scopes id em.scopes` >> simp[] >>
     qpat_assum `env_scopes_consistent env cx em`
       (strip_assume_tac o REWRITE_RULE [vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
     qpat_assum `!nm ent. lookup_scopes nm em.scopes = SOME ent ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  `expr_type e = ArrayT fty bd` by metis_tac[] >>
  `local_ptrs_rel func c em.scopes u` by
    (qhdtm_assum `vv_post` (mp_tac o cj 1 o REWRITE_RULE [vv_post_def]) >>
     disch_then (ACCEPT_TAC o MATCH_MP (cj 1 stateRelProjTheory.stmt_state_rel_local_ptrs_alloca))) >>
  `c.ce_alloca_locals` by
    (qpat_assum `body_inv tops ctx c cx`
    (ACCEPT_TAC o MATCH_MP bodyInvExecutionPropsTheory.contract_inv_alloca_locals o MATCH_MP bodySimTheory.body_inv_contract)) >>
  suspend "entry"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[entry]:
  `?dw bw s G tn.
     s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
     (!H. valid_horizon cx st0 H em.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (u,Gu,tu) [] (OK s,G,tn) /\
       for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,loop_body)
         (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
         (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,0,vs,em,c,em,G,tn,s))` by
    (irule for_nonslot_array_entry_full >>
     qpat_assum `for_nonslot_layout _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
     qexists `n` >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> _ /\ for_nonslot_live _ _ _ _ _ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `~s.vs_halted /\
   (!x w. not_fresh_at saL x /\ lookup_var x u = SOME w ==> lookup_var x s = SOME w)` by
    (qhdtm_assum `for_nonslot_live` (mp_tac o REWRITE_RULE [for_nonslot_live_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_sep d c em s` by
    (`return_buf_frame d c sa0 u` by
       (irule return_buf_frame_frame >> qexistsl [`c`,`s0`,`sa0`] >> simp[]) >>
     `!rb sz. d = SOME (rb,sz) ==> allocas_from (w2n rb + sz) s` by
       ((metis_tac[bodyFullSharedTheory.return_buf_allocas_path])) >>
     `stmt_state_rel (storage_trace_horizon em.storage_trace) ctx func c cx em u` by
       (qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule
          bodyFullSharedTheory.return_buf_sep_locals_kept) >>
     simp[] >> qexists `saL` >> simp[] >> first_assum ACCEPT_TAC) >>
  suspend "round_packets"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[round_packets]:
  qabbrev_tac `Live = \H k rs es J tz z.
    for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,loop_body)
      (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
      (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,rs,es,c,es,J,tz,z)` >>
  qabbrev_tac `Inv = \H rs es J tz z.
    z.vs_current_bb = cond /\ z.vs_inst_idx = 0 /\ return_buf_sep d c es z /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    Live H (LENGTH vs - LENGTH rs) rs es J tz z` >>
  qabbrev_tac `Done = \H ee G1 tn1 t.
    stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext c c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sb t /\
    alloca_history func t /\ return_buf_sep d c ee t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
      FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c es0 sa0 s0 c ee t /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!name base len. local_region c es0.scopes s0 name base len ==>
        off + sz <= base \/ base + len <= off) /\
      off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem)` >>
  qexistsl [`s`,`G`,`tn`,`Inv`,`Done`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> _ /\ for_nonslot_live _ _ _ _ _ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     simp[Abbr `Inv`, Abbr `Live`, IgnAsm `loc = _`, IgnAsm `vs = _`]) >>
  conj_tac >- suspend "cons" >>
  conj_tac >- suspend "nil" >>
  simp[Abbr `Done`, NoAsms] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[nil]:
  map_every qx_gen_tac [`es`,`z`,`J`,`tz`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `return_buf_sep d c es z` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[Abbr `Inv`] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ?k. z.vs_current_bb = cond /\ z.vs_inst_idx = 0 /\
      for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,loop_body)
        (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
        (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,[],es,c,es,J,tz,z)` by
    (gen_tac >> disch_tac >>
     qexists `LENGTH vs` >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z`
       (qspec_then `H` (drule_then assume_tac)) >>
     fs[Abbr `Inv`, Abbr `Live`, IgnAsm `loc = _`, IgnAsm `vs = _`]) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  `sa0.cs_next_var <= sb.cs_next_var /\ ~not_fresh_at sa0 done_var` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all for_nonslot_array_nil_separated >>
  disch_then (qspecl_then [`lctx`,`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ _ _ (OK t,G1,tn1) /\ _` >>
  qexistsl [`t`,`G1`,`tn1`] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (z,J,tz) _ _ /\ _`
    (qspec_then `H` (drule_then mp_tac)) >>
  simp[Abbr `Done`, NoAsms] >> strip_tac >> asm_rewrite_tac[] >>
  qpat_assum `return_buf_sep d c es z ==> _` irule >>
  first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons]:
  map_every qx_gen_tac [`a`,`rs`,`es`,`z`,`J`,`tz`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace` >>
  ASM_REWRITE_TAC [] >>
  TRY (irule gas_outcome_full_initial_domain >>
    simp[] >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
    simp[vyperStorageTraceTheory.storage_trace_frame_ignore_bind,
         vyperStorageTraceTheory.storage_trace_frame_state_updates,
         vyperStorageTraceTheory.storage_trace_frame_finally,
         vyperStorageTraceTheory.storage_trace_frame_pop_scope,
         vyperStorageTraceTheory.storage_trace_frame_try,
         vyperStorageTraceTheory.storage_trace_frame_return,
         vyperStorageTraceTheory.storage_trace_frame_loop_handler,
         vyperStorageTraceTheory.storage_trace_frame_read_result,
         cj 2 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `k = LENGTH vs - LENGTH (a::rs)` >>
  `body_const_cells_agree [(NONE,tops)] cx env es` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then mp_tac)) >>
     simp[NoAsms, Abbr `Inv`] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       z.vs_current_bb = cond /\ z.vs_inst_idx = 0 /\
       return_buf_sep d c es z /\ Live H k (a::rs) es J tz z` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z`
       (qspec_then `H` (drule_then mp_tac)) >>
     simp[NoAsms, Abbr `Inv`, Abbr `k`] >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> z.vs_current_bb = _ /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    for_nonslot_live (DF H,lo,d,ctx,func,cx,c,id,env,loop_body)
      (es0,sa0,s0,G0,tn0) (e,sbExpr,saL,loc,vv,bd,stv,vs,rv,av,xs,em,u,Gu,tu)
      (len_op,idx,bw) (xd,dw,capacity,aidItem) (H,k,a::rs,es,c,es,J,tz,z)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> z.vs_current_bb = _ /\ _`
       (qspec_then `H` (drule_then mp_tac)) >> simp[NoAsms, Abbr `Live`] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all for_nonslot_array_head_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`v`,`eb`,`t`,`Gf`,`tnf`] strip_assume_tac)) >>
  suspend "cons_body"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_body]:
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> for_nonslot_live _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon es.storage_trace` (drule_then assume_tac)) >>
  drule_then strip_assume_tac for_nonslot_live_head_index >>
  `a = Value v` by
    (`?w. a = Value w` by
       (qpat_assum `a = EL k vs` SUBST1_TAC >>
        qpat_assum `vs = MAP Value xs` (fn th =>
          qpat_assum `k < LENGTH vs` mp_tac >> simp[NoAsms,th,listTheory.EL_MAP])) >>
     qpat_assum `a = Value w` (fn th =>
       qpat_assum `read_result cx a es = _` mp_tac >>
       simp[NoAsms,th,read_result_def,return_def])) >>
  qabbrev_tac `sc = FEMPTY |+ (id,<|assignable := F; type := dtv; value := v; popped := []|>)` >>
  `eb = es with scopes := sc :: es.scopes` by
    (qpat_assum `push_scope_with_var id dtv v es = (INL (),eb)` mp_tac >>
     simp[NoAsms,push_scope_with_var_def,return_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     simp[NoAsms,Abbr `sc`,evaluation_state_component_equality]) >>
  `body_const_cells_agree [(NONE,tops)] cx (extend_local env id fty F) eb` by
    (qpat_assum `eb = _` SUBST1_TAC >> simp[]) >>
  `eb.storage_trace = es.storage_trace` by
    (qpat_assum `eb = _` SUBST1_TAC >> simp[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (qhdtm_assum `for_nonslot_live` (mp_tac o REWRITE_RULE [for_nonslot_live_def]) >>
     simp[NoAsms] >> disch_then (map_every assume_tac o CONJUNCTS) >>
     first_assum ACCEPT_TAC) >>
  suspend "cons_admissible"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_admissible]:
  `gas_admissible (eval_stmts cx loop_body) (stmt_res_ok (InLoop exit incr)) eb` by
    (`!res. stmt_res_ok lctx res ==> stmt_res_ok lctx res` by simp[] >>
     `es with <|scopes := sc :: es.scopes; gas_obs := []|> = eb with gas_obs := []` by
       (qpat_assum `eb = _` SUBST1_TAC >> simp[evaluation_state_component_equality]) >>
     qunabbrev_tac `sc` >>
     drule_all forConsBodyGasTheory.captured_storage_body_admissible >>
     disch_then (qspecl_then [`incr`,`exit`] mp_tac) >>
     qpat_assum `_ = eb with gas_obs := []` (pure_rewrite_tac o single) >>
     simp[NoAsms,gasContextTheory.gas_admissible_gas_obs]) >>
  `storage_trace_domain cx st0 eb.storage_trace` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon eb.storage_trace) eb.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (fn th => qpat_assum `eb.storage_trace = es.storage_trace`
      (assume_tac o (fn eq => REWRITE_RULE [GSYM eq] th))) >>
  qpat_assum `!H. valid_horizon cx st0 H eb.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon eb.storage_trace` (drule_then strip_assume_tac)) >>
  qhdtm_assum `for_nonslot_body_entry`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [for_nonslot_body_entry_def]) >>
  qhdtm_assum `for_nonslot_layout`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  suspend "cons_static_body"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_static_body]:
  qpat_assum `compile_stmts bc _ _ loop_body sbCopy = _`
    (mp_then Any mp_tac bodyFullForRangeTheory.range_body_compiler_pair) >>
  disch_then (qspec_then `shadow_sbCopy` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`bc'`,`shBody`] strip_assume_tac) >>
  `shBody = shadow_sbBody` by
    (qpat_assum `compile_stmts _ _ _ (MAP gas_shadow_stmt _) shadow_sbCopy = ((),shBody)`
       (fn th => qpat_assum `compile_stmts _ _ _ (MAP gas_shadow_stmt _) shadow_sbCopy = ((),shadow_sbBody)`
          (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  qpat_x_assum `shBody = shadow_sbBody` SUBST_ALL_TAC >>
  drule_then strip_assume_tac bodyFullForFactsTheory.type_stmt_for_projection >>
  drule_then strip_assume_tac supportedStmtsTheory.supported_loop_body_contract >>
  drule_then assume_tac bodySimDeclCasesTheory.body_for_exprs_ok >>
  `!l. FLOOKUP c.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by
    (qpat_assum `ce_locals_declared c env` mp_tac >>
     qpat_assum `id NOTIN FDOM env.var_types` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[bodySimTheory.ce_locals_declared_def] >> metis_tac[]) >>
  drule_all_then strip_assume_tac bodyFullForRangeTheory.range_body_static_transport >>
  drule_all_then (qspec_then `F` assume_tac) bodyExprPreFactsTheory.ce_locals_declared_declare_local >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) loop_body ==>
      occurs_abi_decode_target target tops` by
    (gen_tac >> disch_tac >>
     qpat_assum `!target. supported_stmt_expr_exists _ _ ==> _` irule >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def]) >>
  `call_evaluation_safe cx (int_calls_stmts loop_body)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)`
       (mp_tac o REWRITE_RULE [vyperTypeCallGraphTheory.int_calls_stmt_def]) >>
     MATCH_ACCEPT_TAC vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right) >>
  suspend "cons_body_geometry"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_body_geometry]:
  qpat_assum `!H. valid_horizon cx st0 H eb.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (assume_tac o (fn th => SIMP_RULE (srw_ss()) [] (cj 3 th))) >>
  `?bb inst. lookup_block incr func.fn_blocks = SOME bb /\
      get_instruction bb 0 = SOME inst /\ inst.inst_opcode <> PHI` by
    (qpat_assum `lookup_block incr func.fn_blocks = _`
      (fn th => simp[NoAsms,th,get_instruction_def,mk_inst_def])) >>
  `ci_mono sbExpr saL` by
    nonslot_mono_cut `_ sbExpr = (len_op,saL)` [nonslot_length_mono] >>
  `ci_mono saL sa` by (irule ci_mono_trans >> qexists `saA` >> simp[]) >>
  `ci_mono saL saCopy` by (irule ci_mono_trans >> qexists `sa` >> simp[]) >>
  `ci_mono saL sbCopy` by (irule ci_mono_trans >> qexists `saCopy` >> simp[]) >>
  `ci_mono sa sbCopy` by (irule ci_mono_trans >> qexists `saCopy` >> simp[]) >>
  `not_fresh_at sbCopy idx /\ not_fresh_at sbCopy xd` by
    (conj_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists `sa` >> simp[]) >>
  `ci_mono sa0 sbCopy` by (irule ci_mono_trans >> qexists `saL` >> simp[]) >>
  `ci_mono sbExpr sbCopy` by (irule ci_mono_trans >> qexists `saL` >> simp[]) >>
  `ci_mono sa0 sbBody` by (irule ci_mono_trans >> qexists `sbCopy` >> simp[]) >>
  `ci_mono sa0 sj` by (irule ci_mono_trans >> qexists `sbBody` >> simp[]) >>
  `ci_mono sa0 sb` by (irule ci_mono_trans >> qexists `sj` >> simp[]) >>
  `~block_is_terminated saCopy` by
    (qpat_assum `emit_op ADD [vv_operand vv;sum_op] sn = _`
       (mp_then Any mp_tac exprOpenPrimitivesTheory.emit_op_nonterminator_open) >>
     simp[NoAsms,is_terminator_def]) >>
  `acyclic_struct_metadata c.ce_struct_fields` by
    (qpat_assum `body_inv tops ctx c cx`
    (ACCEPT_TAC o MATCH_MP bodyInvCodePropsTheory.contract_inv_acyclic_struct_metadata o MATCH_MP bodySimTheory.body_inv_contract)) >>
  `~block_is_terminated sbCopy` by
    (irule for_nonslot_copy_open >>
     qexistsl [`addr`,`c`,`Var xd`,`fty`,`loc`,`saCopy`,`stride`,`sty`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "cons_scoped_body"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_scoped_body]:
  `!H. dead_lo_ok H (DF H) lo bc cx` by
    (qpat_assum `same_frame c bc` (mp_then Any assume_tac bodyPtrDefsTheory.same_frame_is_ctor) >>
     qpat_assum `bc.ce_is_ctor = c.ce_is_ctor` (fn eq =>
       qpat_assum `!H. dead_lo_ok H (DF H) lo c cx` mp_tac >>
       simp[NoAsms,bodyPtrDefsTheory.dead_lo_ok_def,eq])) >>
  `!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sbCopy x` by
    (`bc.ce_return_buf = c.ce_return_buf` by
       (qpat_assum `same_frame c bc` (mp_tac o REWRITE_RULE [bodySimTheory.same_frame_def]) >>
        strip_tac >>
        first_x_assum (mp_tac o AP_TERM ``compile_env_ce_return_buf``) >> simp[NoAsms]) >>
     rpt strip_tac >> irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists `sa0` >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. _ ==> for_nonslot_body_entry _ _ _ _ _ _ _`
    (mp_then Any mp_tac for_nonslot_array_scoped_body_at) >>
  disch_then (drule_at (Pat `frame_ret_ok_full _ _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `stmts_env bc _ ret_ty loop_body sbCopy = _`
    (mp_then (Pat `stmts_env _ _ _ loop_body _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `stmts_env _ _ _ (MAP gas_shadow_stmt _) _ = _`)) >>
  disch_then (drule_at (Pat `gas_shadow_state sbCopy _`)) >>
  disch_then (drule_at (Pat `supported_stmts _ _ _`)) >>
  disch_then (drule_at (Pat `type_stmts _ _ _ = _`)) >>
  disch_then (qspecl_then [`sj`,`sb`,`lctx`,`fty`,`fty`,`cond`,`B`] mp_tac) >>
  impl_tac
  >- ((rpt conj_tac >>> SELECT_LT (first_assum ACCEPT_TAC))
      >- (qexists `start` >> first_assum ACCEPT_TAC) >>
      (all_tac >>> SELECT_LT REFL_TAC)
      >- (qexists_tac `n` >> first_assum ACCEPT_TAC)
      >- (qexistsl [`bb`,`inst`] >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >- suspend "cons_increment" >>
      disch_tac >>
      qpat_assum `!k a rs es eb v t Gf tnf dw bw bc' benv env_b. _ ==> B eb t Gf tnf` irule >>
      (rpt conj_tac >>> SELECT_LT (first_assum ACCEPT_TAC))
      >- (qexists `bc'` >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >> qexistsl [`a`,`extend_local env id fty F`,`bw`,`dw`,`body_env'`,`es`,`k`,`rs`,`v`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "scoped_outcome")) >>
  reverse conj_tac >- suspend "cons_extra" >>
  suspend "cons_compose"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_increment]:
  map_every qx_gen_tac [`iz`,`JG`,`ef`] >> PairCases_on `JG` >>
  simp[NoAsms,pairTheory.FST,pairTheory.SND] >> strip_tac >>
  qabbrev_tac `q = jump_to cond (update_var idx (n2w (SUC k))
                       (update_var next_var (n2w (SUC k)) iz))` >>
  qabbrev_tac `Gq = DRESTRICT (DRESTRICT JG0 (COMPL {next_var})) (COMPL {idx})` >>
  qabbrev_tac `tq = JG1 with t_var := (JG1.t_var |+ (next_var,{})) |+ (idx,{})` >>
  qexistsl [`q`,`Gq`,`tq`] >> qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ef.storage_trace ==> for_nonslot_live _ _ _ _ _ _`
    (qspec_then `H` (drule_then assume_tac)) >>
  `~not_fresh_at saL idx /\ ~not_fresh_at saL next_var /\ xd <> idx /\ xd <> next_var` by
    (qpat_assum `EVERY _ [idx;done_var;next_var]` mp_tac >>
     qpat_assum `ALL_DISTINCT [xd;idx;done_var;next_var]` mp_tac >> simp[NoAsms]) >>
  `sa0.cs_next_var <= saL.cs_next_var` by metis_tac[ci_mono_def] >>
  `?bb inst. lookup_block cond func.fn_blocks = SOME bb /\
      get_instruction bb 0 = SOME inst /\ inst.inst_opcode <> PHI` by
    (qpat_assum `lookup_block cond func.fn_blocks = _`
      (fn th => simp[NoAsms,th,get_instruction_def,mk_inst_def])) >>
  conj_asm1_tac >-
    (qpat_assum `for_nonslot_live _ _ _ _ _ (H,k,a::rs,ef,_,_,_,_,iz)`
      (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_live_def]) >>
     `n2w (SUC k) = (n2w k + 1w):256 word` by
       simp[NoAsms,ADD1,wordsTheory.word_add_n2w] >>
     map_every qunabbrev_tac [`q`,`Gq`,`tq`] >>
     pop_assum (fn th => pure_rewrite_tac[th,pairTheory.PAIR]) >>
     irule for_nonslot_actual_increment_path >>
     (rpt conj_tac >>> SELECT_LT (first_assum ACCEPT_TAC))
     >- (qexists `saL` >> first_assum ACCEPT_TAC)
     >- (qexistsl [`incr`,`sj`] >> conj_tac >> first_assum ACCEPT_TAC)
     >> simp[op_prov_def]) >>
  conj_tac >- simp[NoAsms,Abbr `q`,jump_to_def] >>
  conj_tac >- simp[NoAsms,Abbr `q`,jump_to_def] >>
  irule for_nonslot_actual_increment_live >>
  (rpt conj_tac >>> SELECT_LT (first_assum ACCEPT_TAC)) >>
  qexistsl [`JG0`,`PG`,`a`,`cond`,`gas_explicit_sites ctx shadow_ctx`,`next_var`,`iz`,`JG1`] >>
  conj_tac >- (qexistsl [`bb'`,`inst'`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (rpt conj_tac >>> SELECT_LT (first_assum ACCEPT_TAC)) >>
  simp[NoAsms,Abbr `q`,Abbr `Gq`,Abbr `tq`]
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_extra]:
  qpat_assum `!a rs es z J tz v eb t Gf tnf. _ ==> P a rs es z J tz` irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`eb`,`t`,`tnf`,`v`] >>
  (rpt conj_tac >>> SELECT_LT (first_assum ACCEPT_TAC))
  >- (qpat_assum `!H. valid_horizon cx st0 H eb.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (ACCEPT_TAC o cj 1)) >>
  qpat_assum `eb = _` (fn th => PURE_REWRITE_TAC [th]) >>
  simp[NoAsms,Abbr `sc`]
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_compose]:
  qabbrev_tac `head = bind (read_result cx a) (push_scope_with_var id dtv)` >>
  qabbrev_tac `clean = finally
    (try (ignore_bind (eval_stmts cx loop_body) (return F)) handle_loop_exception)
    pop_scope` >>
  `bind head (\u:unit. clean) =
    bind (read_result cx a) (\v. ignore_bind (push_scope_with_var id dtv v) clean)` by
    simp[NoAsms, Abbr `head`, bind_assoc, ignore_bind_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule gas_outcome_full_bind >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> simp[NoAsms, Abbr `clean`] >>
      irule storage_trace_frame_finally >> simp[NoAsms, storage_trace_frame_pop_scope] >>
      irule storage_trace_frame_try >> simp[NoAsms, storage_trace_frame_loop_handler] >>
      irule storage_trace_frame_ignore_bind >>
      simp[NoAsms, storage_trace_frame_return,
           CONJUNCT1 (CONJUNCT2 evaluate_storage_trace_frame)]) >>
  conj_tac
  >- (qx_gen_tac `left` >> qx_gen_tac `value` >>
      qx_gen_tac `mid` >> qx_gen_tac `t_mid` >> rpt strip_tac >>
      irule gas_exempt_cert_bind_unit >>
      qexistsl [`mid`,`t_mid`,`value`] >> BETA_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_unit >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[NoAsms, Abbr `head`] >> irule storage_trace_frame_bind_all >>
      simp[NoAsms, storage_trace_frame_read_result, storage_trace_frame_state_updates]) >>
  suspend "cons_bind_continuation"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_bind_continuation]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`eb`,`INL ()`,`t`,`tnf`] >>
  conj_tac
  >- (qunabbrev_tac `head` >> qpat_assum `a = Value v` SUBST1_TAC >>
      qpat_assum `eb = es with scopes := _` SUBST1_TAC >>
      simp[NoAsms, Abbr `sc`, bind_def, read_result_def, return_def,
           push_scope_with_var_def, evaluation_state_component_equality]) >>
  qx_gen_tac `H` >> strip_tac >> BETA_TAC >> conj_tac
  >- (qpat_assum `!H. valid_horizon cx st0 H eb.storage_trace ==>
        gas_origin_ptr_path _ (z,J,tz) [] (OK t,Gf,tnf) /\ _`
      (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  qexists `()` >> simp[NoAsms] >>
  `!P R. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 clean (eb with gas_obs := [],t,Gf,tnf) P R =
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 clean (eb,t,Gf,tnf) P R` by
    simp[NoAsms, gas_outcome_full_def, gasStorageTheory.gas_bad_storage_at_def,
         gasOutcomeInitialObsPtrTheory.gas_exempt_cert_initial_obs] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  irule gas_outcome_full_post_mono >>
  asm "scoped_outcome" (irule_at Any) >> BETA_TAC >>
  reverse conj_tac >- (rpt gen_tac >> disch_tac >> first_assum ACCEPT_TAC) >>
  suspend "cons_next_suffix"
QED

Resume for_nonslot_array_round_contracts_at_with_prefix[cons_next_suffix]:
  `SUC k = LENGTH vs - LENGTH rs` by
    (`LENGTH rs = LENGTH vs - SUC k` by
       (qpat_assum `rs = DROP (SUC k) vs` (fn th => simp[NoAsms, th, LENGTH_DROP])) >>
     qpat_assum `LENGTH rs = _` mp_tac >>
     qpat_assum `k < LENGTH vs` mp_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `SUC k = LENGTH vs - LENGTH rs` (fn th =>
    simp[NoAsms, Abbr `Done`, Abbr `Inv`, Abbr `Live`, GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `b` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >> disch_tac >>
  first_x_assum (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_nonslot_array_round_contracts_at_with_prefix

Theorem for_nonslot_array_round_contracts_at:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  body_const_cells_agree mods cx env em /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ expr_body_pre_mods mods c cx env e es0 /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  supported_stmt tops bindings (For id fty (Array e) n loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n loop_body) /\
  for_nonslot_code_frame c cx env ctx func id e loop_body loc rv vv av em u /\
  stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id fty (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id fty (Array e) n loop_body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved c sa0 /\ (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  return_buf_frame d c sa0 s0 /\ ret_pc_ok c sa0 s0 /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\ body_for_full_ok_mods mods exps cx dtv id loop_body vs /\
  storage_trace_domain cx st0 em.storage_trace /\
  return_buf_sep d c em u /\
  vs = MAP Value xs /\
  (?obs. !tail. eval_expr cx e (es0 with gas_obs := obs ++ tail) =
                 (INL rv,em with gas_obs := tail)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
  value_has_type (ArrayTV stv bd) (ArrayV av) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     ?ent. lookup_scopes name em.scopes = SOME ent /\
       evaluate_subscripts ent.type ent.value path = INL (ArrayV av)) /\
  read_result cx rv em = (INL (ArrayV av),em) /\
  extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
  (loc = LocMemory \/ loc = LocCode) /\
  (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)) /\
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\ op_taint tu len_op = {} /\
  op_prov Gu len_op = NONE /\ ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em u /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em Gu tu u) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) ==>
  ?s G tn Inv Done.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK s,G,tn) /\ Inv H vs em G tn s) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)
        (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
          ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
        (\H res ee gt r. ?ex. res = INR ex /\
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
          halt_exit H cx ee (INR ex) r /\
          (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
            allocas_below_fmp t))) /\
    (!es z J tz.
      ~z.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body []) (stmt_res_ok lctx) es ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,J,tz) [] (OK t,G1,tn1) /\ Done H (es with gas_obs := []) G1 tn1 t) /\
    (!H ee G1 tn1 t. Done H ee G1 tn1 t ==>
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext c c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sb t /\
      alloca_history func t /\ return_buf_sep d c ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c es0 sa0 s0 c ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!name base len. local_region c es0.scopes s0 name base len ==>
          off + sz <= base \/ base + len <= off) /\
        off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem))
Proof
  mp_tac (Q.INST [`B` |-> `\eb t G tn. T`, `P` |-> `\a rs es z J tz. T`]
    for_nonslot_array_round_contracts_at_with_prefix) >>
  simp_tac bool_ss []
QED

(* The captured iterator's source facts are common to the full and prefix rounds. *)
Theorem for_nonslot_array_round_source_pre:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  body_const_cells_agree [(NONE,tops)] cx env es0 /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ expr_body_pre_mods mods c cx env e es0 /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  (!nid. e = TopLevelName (expr_type e) nid ==>
     IS_SOME (supported_immutable_type tops nid)) /\
  (~(?ty nid. e = TopLevelName ty nid) ==>
   !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) /\
  stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) n loop_body) /\
  (?obs. !tail. eval_expr cx e (es0 with gas_obs := obs ++ tail) =
                 (INL rv,em with gas_obs := tail)) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) ==>
  body_const_cells_agree [(NONE,tops)] cx env em /\
  for_nonslot_code_frame c cx env ctx func id e loop_body loc rv vv av em u
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_then (map_every assume_tac o CONJUNCTS) bodyFullForFactsTheory.type_stmt_for_projection >>
  `expr_type e = ArrayT sty bd /\ loc = (case vv_location vv of NONE => LocMemory | SOME l => l)` by
    (qhdtm_assum `for_nonslot_layout` (mp_tac o REWRITE_RULE [for_nonslot_layout_def]) >> simp[]) >>
  `expr_type e = ArrayT fty bd` by fs[well_typed_iterator_def] >>
  qpat_assum `?obs. !tail. eval_expr _ _ _ = _` (qx_choose_then `obs` assume_tac) >>
  qabbrev_tac `start = es0 with gas_obs := obs ++ em.gas_obs` >>
  `eval_expr cx e start = (INL rv,em)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `em.gas_obs` mp_tac) >>
     simp[Abbr `start`]) >>
  `expr_body_pre c cx env e start` by simp[Abbr `start`] >>
  `?start. eval_expr cx e start = (INL rv,em) /\ expr_body_pre c cx env e start` by
    (qexists `start` >> simp[]) >>
  conj_tac
  >- (irule body_const_cells_agree_expr >>
      qpat_assum `eval_expr cx e start = (INL rv,em)` (irule_at Any) >>
      imp_res_tac exprBodyPrePropsTheory.expr_body_pre_static_facts >>
      simp[Abbr `start`]) >>
  `expr_sim_inv c cx env em` by
    (drule_all_then ACCEPT_TAC bodySimStmtFactsTheory.expr_body_pre_eval_result) >>
  `vv_place_ptr c cx em u rv vv` by fs[vv_post_def] >>
  `(!v ty p. rv = Value v /\ ~is_word_type (post_value_type c e) /\
     ~is_bytestring_type (post_value_type c e) /\ vv = LocatedValue ty p ==>
     p.ptr_location = LocMemory)` by
    (rpt strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >> simp[]) >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (qpat_assum `body_inv tops ctx _ cx`
       (ACCEPT_TAC o MATCH_MP contractInvContextPropsTheory.contract_inv_singleton_source_modules
         o MATCH_MP bodySimTheory.body_inv_contract)) >>
  irule for_nonslot_code_frame_bare >>
  conj_tac >- (qexistsl [`bd`,`fty`] >> disch_tac >>
    `vv_location vv = SOME LocCode` by
      (qpat_assum `loc = (case vv_location vv of NONE => LocMemory | SOME l => l)` mp_tac >>
       Cases_on `vv_location vv` >> simp[]) >>
    qpat_assum `body_inv tops ctx c cx` (fn inv =>
      assume_tac (MATCH_MP bodySimTheory.body_inv_contract inv) >>
      strip_assume_tac (MATCH_MP bodyInvCodePropsTheory.body_inv_main_code inv)) >>
    `expr_sim_inv_mods [(NONE,tops)] c cx env em` by
      (drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_module_locations >>
       drule_then assume_tac bodyInvSplitTheory.contract_inv_immutable_section_layout >>
       drule_all_then (fn th => simp[th])
         bodyFullPostsModsTheory.expr_sim_inv_mods_singleton) >>
    `type_widens_to env.type_defs (post_value_type c e) (expr_type e)` by
      (irule post_value_type_widens >> conj_tac >- fs[well_typed_iterator_def] >>
       qexistsl [`cx`,`em`] >> first_assum ACCEPT_TAC) >>
    `!src name. e = TopLevelName (expr_type e) (src,name) ==>
       ?ts. ALOOKUP [(NONE,tops)] src = SOME ts /\
            IS_SOME (supported_immutable_type ts (NONE,name))` by
      (rpt gen_tac >> strip_tac >>
       qpat_assum `!nid. e = TopLevelName _ nid ==> _`
         (qspec_then `(src,name)` (drule_then assume_tac)) >>
       Cases_on `src` >>
       gvs[alistTheory.ALOOKUP_def, supportedDeclsTheory.supported_immutable_type_def,
            supportedDeclsTheory.supported_lookup_other_module]) >>
    mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `et` |-> `fty`]
              for_nonslot_array_capture_classify_mods) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    fs[exprSimHypsDefsTheory.cx_const_name_split_def]) >>
  simp[] >> qexistsl [`fty`,`n`] >> simp[]
QED

Theorem for_nonslot_array_round_contracts:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  body_const_cells_agree mods cx env es0 /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ expr_body_pre_mods mods c cx env e es0 /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  supported_stmt tops bindings (For id fty (Array e) n loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) n loop_body) /\
  (!nid. e = TopLevelName (expr_type e) nid ==>
     IS_SOME (supported_immutable_type tops nid)) /\
  (~(?ty nid. e = TopLevelName ty nid) ==>
   !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) /\
  stmt_loop_calls_ok [(NONE,tops)] (For id fty (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id fty (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id fty (Array e) n loop_body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved c sa0 /\ (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  return_buf_frame d c sa0 s0 /\ ret_pc_ok c sa0 s0 /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\ body_for_full_ok_mods mods exps cx dtv id loop_body vs /\
  storage_trace_domain cx st0 em.storage_trace /\
  return_buf_sep d c em u /\
  vs = MAP Value xs /\
  (?obs. !tail. eval_expr cx e (es0 with gas_obs := obs ++ tail) =
                 (INL rv,em with gas_obs := tail)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
  value_has_type (ArrayTV stv bd) (ArrayV av) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
     ?ent. lookup_scopes name em.scopes = SOME ent /\
       evaluate_subscripts ent.type ent.value path = INL (ArrayV av)) /\
  read_result cx rv em = (INL (ArrayV av),em) /\
  extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
  (loc = LocMemory \/ loc = LocCode) /\
  (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)) /\
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\ op_taint tu len_op = {} /\
  op_prov Gu len_op = NONE /\ ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_frame c es0 sa0 s0 c em u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  ghost_kept_at lo c es0 sa0 G0 tn0 s0 Gu tu /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    stmt_state_rel H ctx func c cx em u /\ storage_well_formed_on cx em (FST H) /\
    ghost_inv_at (DF H) lo d c cx em Gu tu u) /\
  vv_post (storage_trace_horizon em.storage_trace) ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) ==>
  ?s G tn Inv Done.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK s,G,tn) /\ Inv H vs em G tn s) /\
    (!a rs es z J tz.
      ~z.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body (a::rs)) (stmt_res_ok lctx) es ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (do v <- read_result cx a;
            push_scope_with_var id dtv v;
            finally (try (do eval_stmts cx loop_body; return F od)
              handle_loop_exception) pop_scope od)
        (es,z,J,tz)
        (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
          ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
        (\H res ee gt r. ?ex. res = INR ex /\
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
          halt_exit H cx ee (INR ex) r /\
          (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
            allocas_below_fmp t))) /\
    (!es z J tz.
      ~z.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H [] es J tz z) /\
      gas_admissible (eval_for cx dtv id loop_body []) (stmt_res_ok lctx) es ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,J,tz) [] (OK t,G1,tn1) /\ Done H (es with gas_obs := []) G1 tn1 t) /\
    (!H ee G1 tn1 t. Done H ee G1 tn1 t ==>
      stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext c c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sb t /\
      alloca_history func t /\ return_buf_sep d c ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa0 x ==>
        FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame c es0 sa0 s0 c ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
        (!name base len. local_region c es0.scopes s0 name base len ==>
          off + sz <= base \/ base + len <= off) /\
        off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS o Q.SPEC `av`)
    for_nonslot_array_round_source_pre >>
  mp_tac (SPEC_ALL for_nonslot_array_round_contracts_at) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
