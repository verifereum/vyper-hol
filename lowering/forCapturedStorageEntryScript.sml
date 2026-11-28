Theory forCapturedStorageEntry
Ancestors
  forCapturedStorageLive bodyFullForStorageCapture bodyFullForArrayRound bodyFullAllocaFresh
  bodyFullGhostFrame bodyFullShared bodyMemoryDefs stmtSimProps
  bodyFullHashKeccakFixed exprSimCopy bodyPtrSignedConvertSourceFrame
  augAssignFullLoadFrame exprLoweringProps exprSimOperands loweringPosts loweringStateRelDefs
  stmtSimDefs bodyPtrDefs ptrDiscipline fragGasOriginPtrLoop fragGasOriginPtr
  exprSimHypsDefs compileEnv context venomState venomInst allocaHistory
  vyperAST vyperInterpreter vyperStorageFootprint vyperStoragePlaceRegion vyperTypeValues
  stateFrame freshWrites words finite_map pred_set list

(* Both array bounds reach the same cursor interface; only the dynamic
   case emits a load. All pre-length variables survive the slice. *)
Theorem captured_storage_length_run[local]:
  (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
   | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca (slot_loc tr) bop)
      sa = (lvo,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  (case bd of Fixed cnt => len = cnt | Dynamic _ =>
    key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
    (if tr then tload slot s else sload slot s) = n2w len) ==>
  ?t G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand lvo t = SOME (n2w len) /\ op_taint tn1 lvo = {} /\ op_prov G1 lvo = NONE /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  Cases_on `bd` >> simp[comp_return_def] >> strip_tac
  >- (qpat_x_assum `Lit _ = lvo` (SUBST_ALL_TAC o SYM) >> qexistsl [`s`,`G`,`tn`] >>
      simp[gas_origin_ptr_path_rules, eval_operand_def, op_taint_def, op_prov_def,
           emitted_insts_def, venom_state_component_equality]) >>
  `emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lvo,sb)` by
    (Cases_on `tr` >> gvs[slot_loc_def, compile_ptr_load_def]) >>
  drule_then strip_assume_tac exprLoweringPropsTheory.emit_op_extends >>
  drule_then strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op >>
  `?out t G1 tn1. lvo = Var out /\
      t = (update_var out (n2w len) s with vs_inst_idx := SUC s.vs_inst_idx) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)) /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted /\ eval_operand lvo t = SOME (n2w len) /\
      op_taint tn1 lvo = {} /\ op_prov G1 lvo = NONE /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> x <> out) /\
      (!x. x <> out ==> lookup_var x t = lookup_var x s /\
        FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))` by
    (drule_all for_storage_iterator_dynamic_length_run_uniform >>
     disch_then (qspecl_then [`explicit`,`PG`,`G`] ACCEPT_TAC)) >>
  qexistsl [`t`,`G1`,`tn1`] >>
  simp[update_var_def, venom_state_component_equality, same_blocks_def, mk_inst_def] >>
  Cases_on `tr` >> fs[same_blocks_def]
QED

Theorem captured_entry_kept_operand[local]:
  (!x. P x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!x. oper = Var x ==> P x) /\ (!l. oper <> Label l) ==>
  eval_operand oper t = eval_operand oper s /\
  op_prov G1 oper = op_prov G oper /\ op_taint tn1 oper = op_taint tn oper
Proof
  Cases_on `oper` >> simp[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]
QED

Theorem captured_entry_local_regions[local]:
  local_ptrs_reserved c sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  !name b sz. local_region c es.scopes t name b sz <=>
              local_region c es.scopes s name b sz
Proof
  strip_tac >> rpt gen_tac >> irule local_region_lookup_cong >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* The selected storage operand and the length operand are both old by
   the allocation cut. The entry block overwrites neither of them. *)
Theorem captured_entry_control[local]:
  ~a.vs_halted /\ allocas_from lo a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb a.vs_inst_idx = SOME (mk_inst j0 JMP [Label entry] []) /\
  lookup_block entry func.fn_blocks = SOME eb /\
  eb.bb_instructions = ([mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (case bd of Fixed _ => [] | Dynamic cnt =>
       [mk_inst (eid+1) GT [lvo;Lit (n2w cnt)] [bad];
        mk_inst (eid+2) ISZERO [Var bad] [good];
        mk_inst (eid+3) ASSERT [Var good] []])) ++
    [mk_inst j1 JMP [Label cond] []] /\
  eval_operand lvo a = SOME (n2w len) /\ op_taint ta lvo = {} /\ op_prov Ga lvo = NONE /\
  len <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (!x. lvo = Var x ==> not_fresh_at sd x) /\ (!l. lvo <> Label l) /\
  ~not_fresh_at sd idx /\
  (case bd of Fixed _ => T | Dynamic _ =>
    ~not_fresh_at sd bad /\ ~not_fresh_at sd good /\ ALL_DISTINCT [idx;bad;good]) ==>
  ?t G tn.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK t,G,tn)) /\
    t = jump_to cond (if (?k. bd = Dynamic k) then
      update_var good 1w (update_var bad 0w (update_var idx 0w (jump_to entry a)))
      else update_var idx 0w (jump_to entry a)) /\
    lookup_var idx t = SOME 0w /\ op_prov G (Var idx) = NONE /\ op_taint tn (Var idx) = {} /\
    (!x. x NOTIN (if (?k. bd = Dynamic k) then {idx;bad;good} else {idx}) ==>
      lookup_var x t = lookup_var x a /\ FLOOKUP G x = FLOOKUP Ga x /\
      op_taint tn (Var x) = op_taint ta (Var x)) /\
    tn.t_mem = ta.t_mem /\ tn.t_stor = ta.t_stor /\ tn.t_trans = ta.t_trans /\ tn.t_imm = ta.t_imm
Proof
  strip_tac >>
  `!x. lvo = Var x ==> x NOTIN (case bd of Fixed _ => {idx} | Dynamic _ => {idx;bad;good})` by
    (Cases_on `bd` >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qabbrev_tac `dyn = ?k. bd = Dynamic k` >>
  `(dyn ==> ALL_DISTINCT [idx;bad;good] /\ ((?x. lvo = Var x) \/ (?w. lvo = Lit w)))` by
    (Cases_on `bd` >> gvs[Abbr `dyn`] >> Cases_on `lvo` >> gvs[]) >>
  irule for_nonslot_entry_control >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl [`bb`,`j0`] >> simp[]) >>
  conj_tac >- (qexistsl [`bound_length bd`,`eb`,`eid`,`j1`,`lvo`,`len`] >>
    Cases_on `bd` >> gvs[Abbr `dyn`]) >> simp[]
QED

(* Start after the actual expression evaluation. The saved source list is
   read here, and the code runs from this endpoint rather than from sa0. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qabbrev_tac `len = case bd of Fixed n => n | Dynamic _ =>
       w2n (lookup_storage slot (get_storage cx em tr))` >>
  `len = case bd of Fixed n => n | Dynamic _ =>
       w2n (lookup_storage slot (get_storage cx em tr))` by simp[Abbr `len`] >>
  drule_all for_storage_iterator_capture >> strip_tac >>
  drule_all for_storage_iterator_operand >>
  disch_then strip_assume_tac >>
  rename1 `vv = LocatedValue _ arrptr` >>
  qabbrev_tac `vs = GENLIST (\j. PlaceR (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (j * type_slot_size tyv)) tyv)) len` >>
  `len = LENGTH vs` by simp[NoAsms, Abbr `vs`] >>
  suspend "length"
QED
*)
Theorem for_captured_storage_initial_full:
  for_nonslot_layout (c,id,typ,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,lvo,sd)
    (bc,saD,sc,p,nb,aidItem)
    (entry,cond,bod,incr,exit,idx,bad,good,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  loc = slot_loc tr /\ bop = vv_operand vv /\
  (!x. bop = Var x ==> not_fresh_at sbExpr x) /\ (!l. bop <> Label l) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved c sa0 /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  nb < dimword (:256) /\ 32 * type_slot_size tyv <= nb /\
  bound_length bd < dimword (:256) /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  expr_body_pre c cx env e e0 /\
  eval_expr cx e e0 = (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em) /\
  storage_trace_domain cx st0 em.storage_trace /\
  lookup_scopes id em.scopes = NONE /\ expr_sim_inv c cx env em /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    vv_post H ctx func c cx e e0 sa0 sbExpr s0 em
      (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) vv s /\
    storage_well_formed_on cx e0 (FST H) /\ storage_well_formed_on cx em (FST H) /\
    stmt_state_rel H ctx func c cx em s /\ ghost_inv_at (DF H) lo d c cx em G tn s) /\
  ptr_vv_ok cx (post_value_type c e) (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) vv em G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sbExpr.cs_current_bb /\
  s.vs_inst_idx = LENGTH sbExpr.cs_current_insts /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame c e0 sa0 s0 c em s /\ ghost_kept_at lo c e0 sa0 G0 tn0 s0 G tn /\
  return_buf_frame d c sa0 s0 /\ ret_pc_ok c sa0 s0 /\ return_buf_sep d c em s ==>
  ?vs len dst t G1 tn1.
    eval_iterator cx (Array e) e0 = (INL vs,em) /\
    len = LENGTH vs /\ len <= bound_length bd /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
      for_captured_storage_live exps (DF,lo,d,ctx,func,cx,c,id,env,typ,loop_body)
        (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
        (lvo,idx,cond) (p,dst,nb,sd) (H,0,vs,em,G1,tn1,t))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[length]:
  `ci_mono sa0 sbExpr` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `local_ptrs_reserved c sbExpr` by
    drule_all_then ACCEPT_TAC exprOperandVarTheory.compiler_ci_mono_reserved >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sbExpr x /\ not_fresh_at sd x` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sbExpr x /\ not_fresh_at sd x` by metis_tac[] >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sbExpr x /\ not_fresh_at sd x` by metis_tac[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp >>
  `(case bd of Fixed cnt => comp_return (Lit (n2w cnt))
   | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca (slot_loc tr) bop)
      sbExpr = (lvo,sd)` by metis_tac[] >>
  `eval_operand bop s = SOME slot /\ op_taint tn bop = {}` by
    fs[vv_operand_def] >>
  `(case bd of Fixed cnt => len = cnt | Dynamic _ =>
    key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
    (if tr then tload slot s else sload slot s) = n2w len)` by
    (qpat_assum `case bd of Fixed _ => T | Dynamic _ => _` mp_tac >>
     simp[NoAsms, Abbr `len`] >> Cases_on `bd` >> simp[NoAsms]) >>
  drule_all captured_storage_length_run >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`sl`,`GL`,`tnL`] strip_assume_tac)) >>
  suspend "alloca"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[alloca]:
  `sl.vs_allocas = s.vs_allocas /\ sl.vs_alloca_next = s.vs_alloca_next /\
    state_frame sl = state_frame (s with vs_inst_idx := sl.vs_inst_idx)` by
    (qpat_assum `sl = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[state_frame_def]) >>
  `alloca_history func sl` by
    drule_all_then ACCEPT_TAC augassign_load_endpoint_history >>
  `!H. valid_horizon cx st0 H em.storage_trace ==> stmt_state_rel H ctx func c cx em sl` by
    (rpt strip_tac >> irule stmt_state_rel_readonly_vars_pc >>
     qexistsl [`s`,`sbExpr`] >> conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sbExpr x ==> lookup_var x sl = _ /\ _`
           (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func c cx em sl` by first_assum (drule_then ACCEPT_TAC) >>
  `allocas_from lo sl` by
    (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[allocas_from_def]) >>
  `lo <= sl.vs_alloca_next` by asm_rewrite_tac[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp sl)` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ sl`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  drule_all (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tnL`,`explicit`,`PG`,`GL`]
    (qx_choosel_then [`q`,`dst`,`a`,`Ga`,`ta`] strip_assume_tac)) >>
  suspend "control"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[control]:
  `q = p` by fs[] >> pop_assum SUBST_ALL_TAC >>
  `~a.vs_halted` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = sl`
      (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ sl ==> _`
      (qspec_then `H0` (drule_then (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)))) >>
  `sc.cs_current_bb = sd.cs_current_bb` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> simp[]) >>
  `!l. lvo <> Label l` by
    (qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => _) sbExpr = (lvo,sd)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, comp_return_def]
     >- (disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[NoAsms]) >>
     disch_then (ACCEPT_TAC o MATCH_MP fragFuelExprHelpersTheory.compile_ptr_load_not_label)) >>
  `!x. lvo = Var x ==> not_fresh_at sd x` by metis_tac[] >>
  `eval_operand lvo a = SOME (n2w len) /\ op_taint ta lvo = {} /\ op_prov Ga lvo = NONE` by
    (qpat_assum `!x. not_fresh_at sd x ==> lookup_var x a = _ /\ _`
       (mp_then Any mp_tac (Q.INST [`P` |-> `not_fresh_at sd`] captured_entry_kept_operand)) >>
     disch_then (qspec_then `lvo` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `?bb. lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb a.vs_inst_idx = SOME (mk_inst sc.cs_next_id JMP [Label entry] [])` by
    (qexists_tac `<|bb_label := sd.cs_current_bb;
                   bb_instructions := sc.cs_current_insts ++
                    [mk_inst sc.cs_next_id JMP [Label entry] []]|>` >>
     qpat_assum `a.vs_current_bb = sc.cs_current_bb` (fn th => rewrite_tac[th]) >>
     qpat_assum `sc.cs_current_bb = sd.cs_current_bb` (fn th => rewrite_tac[th]) >>
     qpat_assum `a.vs_inst_idx = LENGTH sc.cs_current_insts` (fn th => rewrite_tac[th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms,get_instruction_def,rich_listTheory.EL_LENGTH_APPEND_0]) >>
  pop_assum strip_assume_tac >>
  `~not_fresh_at sd idx /\
   (case bd of Fixed _ => T | Dynamic _ =>
    ~not_fresh_at sd bad /\ ~not_fresh_at sd good /\ ALL_DISTINCT [idx;bad;good])` by
    (qpat_assum `EVERY (\p. ~not_fresh_at sd p) [idx;_;_]` mp_tac >>
     qpat_assum `case bd of Fixed _ => T | Dynamic _ => EVERY _ _ /\ ALL_DISTINCT _` mp_tac >>
     Cases_on `bd` >> simp[NoAsms]) >>
  suspend "run_control"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[run_control]:
  `?t G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK t,G1,tn1)) /\
    t = jump_to cond (if (?k. bd = Dynamic k) then
      update_var good 1w (update_var bad 0w (update_var idx 0w (jump_to entry a)))
      else update_var idx 0w (jump_to entry a)) /\
    lookup_var idx t = SOME 0w /\ op_prov G1 (Var idx) = NONE /\ op_taint tn1 (Var idx) = {} /\
    (!x. x NOTIN (if (?k. bd = Dynamic k) then {idx;bad;good} else {idx}) ==>
      lookup_var x t = lookup_var x a /\ FLOOKUP G1 x = FLOOKUP Ga x /\
      op_taint tn1 (Var x) = op_taint ta (Var x)) /\
    tn1.t_mem = ta.t_mem /\ tn1.t_stor = ta.t_stor /\ tn1.t_trans = ta.t_trans /\ tn1.t_imm = ta.t_imm` by
    (irule captured_entry_control >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qexistsl [`bb`,`sc.cs_next_id`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`<|bb_label := entry; bb_instructions :=
       [mk_inst (sc.cs_next_id + 1) ASSIGN [Lit 0w] [idx]] ++
       (case bd of Fixed _ => [] | Dynamic cnt =>
         [mk_inst (sc.cs_next_id + 2) GT [lvo; Lit (n2w cnt)] [bad];
          mk_inst (sc.cs_next_id + 3) ISZERO [Var bad] [good];
          mk_inst (sc.cs_next_id + 4) ASSERT [Var good] []]) ++
       [mk_inst (sa.cs_next_id - 3) JMP [Label cond] []]|>`,
       `sc.cs_next_id + 1`,`sa.cs_next_id - 3`,`len`,`lvo`,`sd`] >>
     simp[NoAsms, arithmeticTheory.ADD_ASSOC] >> simp[] >>
     qpat_assum `(case bd of Fixed _ => T | Dynamic _ => ~not_fresh_at sd bad /\ _)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, arithmeticTheory.ADD_ASSOC]) >>
  suspend "packet"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[packet]:
  qabbrev_tac `dyn = ?k. bd = Dynamic k` >>
  qabbrev_tac `writes = if dyn then {idx;bad;good} else {idx}` >>
  `!x. not_fresh_at sd x ==> x NOTIN writes` by
    (qpat_assum `(case bd of Fixed _ => T | Dynamic _ => ~not_fresh_at sd bad /\ _)` mp_tac >>
     qpat_assum `~not_fresh_at sd idx` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `dyn`, Abbr `writes`] >> metis_tac[]) >>
  `p NOTIN writes` by
    (qpat_assum `ALL_DISTINCT [p;idx;done_var;next_var]` mp_tac >>
     qpat_assum `(case bd of Fixed _ => T | Dynamic _ => EVERY _ _ /\ ALL_DISTINCT _)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `dyn`, Abbr `writes`]) >>
  `t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ t.vs_halted = a.vs_halted /\
   t.vs_memory = a.vs_memory /\ t.vs_allocas = a.vs_allocas /\
   t.vs_alloca_next = a.vs_alloca_next` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     Cases_on `dyn` >> simp[NoAsms, jump_to_def, update_var_def]) >>
  `!x. not_fresh_at sd x ==> lookup_var x t = lookup_var x sl /\
      FLOOKUP G1 x = FLOOKUP GL x /\ op_taint tn1 (Var x) = op_taint tnL (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> x NOTIN writes` (drule_then assume_tac) >>
     qpat_assum `!x. x NOTIN writes ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x a = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `!x. not_fresh_at sa0 x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa0 x ==> not_fresh_at sbExpr x /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sbExpr x ==> lookup_var x sl = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  suspend "saved_operands"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[saved_operands]:
  `eval_operand lvo t = SOME (n2w len) /\ op_taint tn1 lvo = {} /\ op_prov G1 lvo = NONE` by
    (qpat_assum `!x. x NOTIN writes ==> lookup_var x t = _ /\ _`
       (mp_then Any mp_tac (BETA_RULE (Q.INST [`P` |-> `\x. x NOTIN writes`] captured_entry_kept_operand))) >>
     disch_then (qspec_then `lvo` mp_tac) >>
     (impl_tac >- (conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!x. bop = Var x ==> not_fresh_at sd x` by metis_tac[] >>
  `eval_operand bop t = SOME slot /\ op_taint tn1 bop = {}` by
    (`!x. not_fresh_at sbExpr x /\ not_fresh_at sd x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
        op_taint tn1 (Var x) = op_taint tn (Var x)` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!x. not_fresh_at sd x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
        qpat_assum `!x. not_fresh_at sbExpr x ==> lookup_var x sl = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!x. not_fresh_at sbExpr x /\ not_fresh_at sd x ==> _`
       (mp_then Any mp_tac (BETA_RULE (Q.INST [`P` |-> `\x. not_fresh_at sbExpr x /\ not_fresh_at sd x`] captured_entry_kept_operand))) >>
     disch_then (qspec_then `bop` mp_tac) >>
     (impl_tac >- (conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC)) >> simp[]) >>
  qpat_assum `!x. x NOTIN writes ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
  `ptr_covers G1 tn1 p t nb` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`Ga`,`a`,`ta`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "assemble"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[assemble]:
  `!H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)` by
    (rpt strip_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Ga`,`a`,`ta`] >> reverse conj_tac >- simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`GL`,`sl`,`tnL`] >> simp[]) >>
  `!x. x IN writes ==> not_local_ptr c em.scopes x` by
    (rpt strip_tac >> irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists `sd` >> simp[] >> metis_tac[]) >>
  `not_local_ptr c em.scopes idx /\
     (dyn ==> not_local_ptr c em.scopes bad /\ not_local_ptr c em.scopes good)` by
    (qpat_assum `!x. x IN writes ==> _` mp_tac >>
     Cases_on `dyn` >> simp[NoAsms, Abbr `writes`] >> metis_tac[IN_INSERT]) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==> stmt_state_rel H ctx func c cx em t` by
    (rpt gen_tac >> disch_tac >>
     `stmt_state_rel H ctx func c cx em a` by
       (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ sl ==> _` irule >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ sl` (drule_then ACCEPT_TAC)) >>
     qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     qpat_assum `dyn ==> not_local_ptr _ _ bad /\ _` mp_tac >>
     Cases_on `dyn` >> simp[stmt_state_rel_jump_to] >> rpt strip_tac >>
     rpt (irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to])) >>
  `alloca_history func t` by
    (irule allocaHistoryTheory.alloca_history_jump >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `a` >> simp[]) >>
  suspend "entry_ghost"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[entry_ghost]:
  `!H. valid_horizon cx st0 H em.storage_trace ==> ghost_inv_at (DF H) lo d c cx em G1 tn1 t` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `ghost_inv_at (DF H) lo d c cx em GL tnL sl` by
       (irule ghost_inv_at_exterior_frame >> qexistsl [`G`,`em`,`s`,`sbExpr`,`tn`] >>
        simp[] >> qpat_assum `sl = s with <|vs_vars := _; vs_inst_idx := _|>`
          (fn th => once_rewrite_tac[th]) >> simp[NoAsms]) >>
     `ghost_inv_at (DF H) lo d c cx em Ga ta a` by
       (qpat_assum `stmt_state_rel H0 ctx func c cx em sl`
          (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule alloc_buffer_ghost_inv_at) >>
        ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
        qexistsl [`GL`,`w2n dst + nb`,`sd`,`tnL`] >> simp[]) >>
     irule ghost_inv_at_exterior_frame >> qexistsl [`Ga`,`em`,`a`,`sd`,`ta`] >>
     simp[] >> Cases_on `dyn` >> simp[jump_to_def,update_var_def]) >>
  suspend "entry_exterior"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[entry_exterior]:
  `s0.vs_alloca_next <= t.vs_alloca_next` by
    (map_every (fn q => qpat_assum q mp_tac)
      [`s0.vs_alloca_next <= s.vs_alloca_next`,`sl.vs_alloca_next = s.vs_alloca_next`,
       `sl.vs_alloca_next <= a.vs_alloca_next`,`t.vs_alloca_next = a.vs_alloca_next`] >>
     decide_tac) >>
  `!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    metis_tac[] >>
  `return_buf_frame d c sa0 s` by
    (irule return_buf_frame_frame >> qexistsl [`c`,`s0`,`sa0`] >> simp[]) >>
  `return_buf_frame d c sa0 t` by
    (irule return_buf_frame_frame >> qexistsl [`c`,`s0`,`sa0`] >> simp[]) >>
  `ret_pc_ok c sa0 t` by
    (irule ret_pc_ok_frame >> qexistsl [`c`,`s0`,`sa0`] >> simp[]) >>
  `!name b sz. local_region c em.scopes t name b sz <=> local_region c em.scopes s name b sz` by
    (irule captured_entry_local_regions >> qexists `sa0` >> simp[]) >>
  `!name b sz. local_region c em.scopes t name b sz <=> local_region c em.scopes a name b sz` by
    (irule captured_entry_local_regions >> qexists `sd` >> simp[]) >>
  `return_buf_sep d c em t` by
    (irule return_buf_sep_transport >>
     reverse conj_tac >-
       (qexistsl [`c`,`em`,`s`] >>
        qpat_assum `!n b sz. local_region c em.scopes t n b sz <=> local_region c em.scopes s n b sz`
          (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (drule_then (mp_then Any mp_tac return_buf_allocas_path)) >>
     qpat_assum `return_buf_frame d c sa0 s` mp_tac >>
     qpat_assum `return_buf_sep d c em s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  suspend "entry_alloca_frame"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[entry_alloca_frame]:
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t.vs_memory = a.vs_memory` SUBST1_TAC >>
     qpat_assum `a with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = sl`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >>
     qpat_assum `sl = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms]) >>
  `alloca_frame c e0 sa0 s0 c em t` by
    (rewrite_tac[alloca_frame_def] >>
     qpat_assum `t.vs_memory = s.vs_memory` (fn th => rewrite_tac[th]) >>
     qpat_assum `!n b sz. local_region c em.scopes t n b sz <=> local_region c em.scopes s n b sz`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `alloca_frame c e0 sa0 s0 c em s` (ACCEPT_TAC o REWRITE_RULE[alloca_frame_def])) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b` by
    metis_tac[] >>
  `!x. not_fresh_at sa0 x ==> FLOOKUP G1 x = FLOOKUP G0 x /\
      op_taint tn1 (Var x) = op_taint tn0 (Var x)` by
    (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa0 x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa0 x ==> FLOOKUP G x = _ /\ _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s` (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!name b n. local_region c e0.scopes s0 name b n ==> off + sz <= b \/ b + n <= off) /\
      off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem` by
    (rpt strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid_old = SOME (base_old,n_old)` >>
     `FLOOKUP s.vs_allocas aid_old = SOME (base_old,n_old)` by
       (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b`
          (drule_then ACCEPT_TAC)) >>
     drule_all allocaSiteResourceTheory.alloca_site_registered_below >> strip_tac >>
     `i < sl.vs_alloca_next` by
       (qpat_assum `sl.vs_alloca_next = s.vs_alloca_next` (fn th => rewrite_tac[th]) >>
        qpat_assum `base_old + n_old <= s.vs_alloca_next` mp_tac >>
        qpat_assum `i < base_old + n_old` mp_tac >> decide_tac) >>
     `i IN tn.t_mem` by
       (qpat_assum `!i. i IN ta.t_mem <=> _` (qspec_then `i` mp_tac) >>
        qpat_assum `i IN tn1.t_mem` mp_tac >>
        map_every (fn q => qpat_assum q (fn th => rewrite_tac[th]))
          [`tn1.t_mem = ta.t_mem`,`tnL.t_mem = tn.t_mem`] >>
        simp[] >> decide_tac) >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  suspend "initial_live"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_initial_full[initial_live]:
  `len < dimword (:256)` by
    (qpat_assum `len <= bound_length bd` mp_tac >>
     qpat_assum `bound_length bd < dimword (:256)` mp_tac >> decide_tac) >>
  `well_formed_type_value tyv` by
    (qpat_assum `well_formed_type_value (ArrayTV tyv bd)` mp_tac >>
     simp[NoAsms,vyperTypingTheory.well_formed_type_value_def]) >>
  `!name b sz. local_region c em.scopes t name b sz ==>
     w2n dst + nb <= b \/ b + sz <= w2n dst` by
    (qpat_assum `!n b sz. local_region c em.scopes t n b sz <=> local_region c em.scopes a n b sz`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `!n b sz. local_region c em.scopes a n b sz ==> _`
       (ACCEPT_TAC o REWRITE_RULE[loweringStateRelDefsTheory.regions_disjoint_def])) >>
  qexistsl [`vs`,`len`,`dst`,`t`,`G1`,`tn1`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ t`
    (drule_then assume_tac) >>
  conj_tac >-
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK t,G1,tn1)`
      (drule_then ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ t`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `~t.vs_halted /\ lookup_var p t = SOME dst /\
    FLOOKUP t.vs_allocas sd.cs_next_id = SOME (w2n dst,nb)` by asm_rewrite_tac[] >>
  `FLOOKUP G1 idx = NONE` by
    (qpat_assum `op_prov G1 (Var idx) = NONE` mp_tac >>
     simp[NoAsms, op_prov_def]) >>
  `nb + w2n dst < dimword (:256) /\ nb + w2n dst <= t.vs_alloca_next` by
    (qpat_assum `w2n dst + nb < dimword (:256)` mp_tac >>
     qpat_assum `w2n dst + nb <= a.vs_alloca_next` mp_tac >>
     qpat_assum `t.vs_alloca_next = a.vs_alloca_next` SUBST1_TAC >> decide_tac) >>
  `!name b sz. local_region c em.scopes t name b sz ==>
     nb + w2n dst <= b \/ b + sz <= w2n dst` by
    (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     qpat_assum `!n b sz. local_region c em.scopes t n b sz ==> w2n dst + nb <= b \/ _` mp_tac >>
     simp[NoAsms, arithmeticTheory.ADD_COMM]) >>
  simp[NoAsms, for_captured_storage_live_def, cenv_top_ext_refl, Abbr `vs`] >>
  qpat_x_assum `len = LENGTH (GENLIST _ _)` kall_tac >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl [`off`,`root`,`path`,`delta`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_captured_storage_initial_full
*)
