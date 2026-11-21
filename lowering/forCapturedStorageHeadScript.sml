Theory forCapturedStorageHead
Ancestors
  forCapturedStorageHeadPrefix bodyFullForStorage bodyFullShared bodySimFull
  forCapturedStorageLive slotCopyExecution freshWrites bodyFullPreds
  bodyPtrDefs stmtSimDefs compileEnv emitHelper venomState venomExecSemantics
  ptrDiscipline venomInst vyperStorageFootprint vyperStoragePlaceObserved
  vyperInterpreter vyperState vyperTypeValues words finite_map list

(* The scalar head and the copy meet at the actual copy-start state. *)
Theorem for_captured_storage_head_full:
  !body. let n = type_slot_size tyv in
  let dyn = (case bd of Fixed _ => F | Dynamic _ => T) in
  let outs = if dyn then [dv;ov;tot;ep] else [dv;ov;ep] in
  let EB = (\ee v. ee with scopes :=
    (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
    ee.scopes) in
  let Fr = (\c ee st G tn.
    alloca_history func st /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp st) /\
    s0.vs_alloca_next <= st.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x st = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP st.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 c ee st /\
    !aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) in
  let Entry = (\H ei v k z Gf tnf.
    push_scope_with_var id tyv v ei = (INL (),EB ei v) /\
    expr_sim_inv bc cx (extend_local env id typ F) (EB ei v) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    cenv_top_ext c0 bc (EB ei v).scopes /\
    stmt_state_rel H ctx func bc cx (EB ei v) z /\
    storage_well_formed_on cx (EB ei v) (FST H) /\
    ghost_inv_at (DF H) lo d bc cx (EB ei v) Gf tnf z /\
    ret_pc_ok bc sb0 z /\ return_buf_frame d bc sb0 z /\
    return_buf_sep d bc (EB ei v) z /\ Fr bc (EB ei v) z Gf tnf /\
    ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ lookup_var p z = SOME dst /\
    eval_operand lvo z = SOME (n2w len) /\ op_prov Gf lvo = NONE /\
    op_taint tnf lvo = {} /\ allocas_from lo z /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
    ptr_covers Gf tnf p z nb /\
    !aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP z.vs_allocas aid = SOME b) in
  0 < n /\ body_for_full_ok cx tyv id body vs /\ id NOTIN FDOM env.var_types /\
  declare_local c0 id typ sd = (bc,st) /\ c0.ce_alloca_locals /\
  type_memory_bytes c0 typ < 2 ** 64 /\
  (!l. FLOOKUP c0.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
  sa0.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
  local_ptrs_reserved c0 sa /\ local_ptrs_reserved bc sa /\
  (!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
  (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
  not_fresh_at sa p /\ not_fresh_at sa idx /\
  (!x. lvo = Var x ==> not_fresh_at sa x) /\ (!lbl. lvo <> Label lbl) /\
  (!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ inst.inst_id = sd.cs_next_id /\
  sa0.cs_next_id <= inst.inst_id /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo c0 cx) /\
  compile_iter_elem_copy bc (Var ep) (Var p) n (slot_loc tr) T typ typ sa = ((),sb0) /\
  compile_slot_to_memory (Var ep) (Var p) n (slot_loc tr) sa = (slot_copy_body sa,sb0) /\
  slot_copy_external sa (Var ep) /\
  lookup_block sa.cs_current_bb func.fn_blocks =
    SOME <|bb_label := sa.cs_current_bb;
           bb_instructions := sa.cs_current_insts ++ slot_copy_init_insts sa|> /\
  lookup_block (slot_copy_cond sa) func.fn_blocks =
    SOME <|bb_label := slot_copy_cond sa; bb_instructions := slot_copy_cond_insts sa n|> /\
  lookup_block (slot_copy_body sa) func.fn_blocks =
    SOME <|bb_label := slot_copy_body sa; bb_instructions :=
      slot_copy_body_insts sa (Var ep) (Var p) (if tr then TLOAD else SLOAD)|> /\
  lookup_block cond func.fn_blocks = SOME cb /\
  cb.bb_instructions =
    [mk_inst (h - 2) EQ [Var idx;lvo] [dv];
     mk_inst (h - 1) JNZ [Var dv;Label exit;Label bod] []] /\
  lookup_block bod func.fn_blocks = SOME bb /\ sa.cs_current_bb = bod /\
  sa.cs_current_insts =
    [mk_inst h MUL [Var idx;Lit (n2w n)] [ov]] ++
    (if dyn then [mk_inst (h + 1) ADD [Lit 1w;Var ov] [tot]] else []) ++
    [mk_inst (h + if dyn then 2 else 1) ADD
       [bop;Var (if dyn then tot else ov)] [ep]] /\
  (!j. j < LENGTH sa.cs_current_insts ==>
       get_instruction bb j = SOME (fEL sa.cs_current_insts j)) /\
  ALL_DISTINCT outs /\ (!x. MEM x outs ==> ~not_fresh_at sa0 x) /\
  ~MEM idx outs /\ ~MEM p outs /\
  (!x. lvo = Var x ==> ~MEM x outs) /\ (!x. bop = Var x ==> ~MEM x outs) /\
  sbExpr.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved c0 sa0 /\
  storage_trace_domain cx st0 ei.storage_trace /\
  (!H. valid_horizon cx st0 H ei.storage_trace ==>
       ?k. for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,body)
         (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
         (lvo,idx,cond) (p,dst,nb,sd) (H,k,a::rs,ei,G,tn,s)) /\
  gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) ei ==>
  (?v. !tail. bind (read_result cx a) (\w. push_scope_with_var id tyv w)
    (ei with gas_obs := tail) = (INL (),EB ei v with gas_obs := tail)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (read_result cx a) (\v. push_scope_with_var id tyv v)) (ei,s,G,tn)
    (\H res eb Gf tnf z. res = INL () /\ eb.gas_obs = [] /\
      ?v k. eb = EB (ei with gas_obs := []) v /\ read_result cx a ei = (INL v,ei) /\
        Entry H (ei with gas_obs := []) v k z Gf tnf /\
        eval_operand bop z = SOME slot /\ op_taint tnf bop = {} /\ a::rs = DROP k vs /\
        body_stmts_full_ok cx body /\
        gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr)) eb)
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s \/ (?ir. r = IntRet ir s) ==>
                                  allocas_below_fmp s))
Proof
  gen_tac >>
  CONV_TAC (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV])) >> strip_tac >>
  qmatch_asmsub_rename_tac `body_for_full_ok cx tyv id loop_body vs` >>
  mp_tac (Q.INST [`saCopy` |-> `sa`]
    (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
      for_captured_storage_head_prefix)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `k` (qx_choose_then `u`
    (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))) >>
  qabbrev_tac `H0 = storage_trace_horizon ei.storage_trace` >>
  `valid_horizon cx st0 H0 ei.storage_trace` by
    simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> for_captured_storage_live _ _ _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ (H0,k,_,_,_,_,_)`
    (strip_assume_tac o REWRITE_RULE [for_captured_storage_live_def]) >>
  `return_buf_sep d c0 ei u` by
    (irule return_buf_sep_transport >> conj_tac
     >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
         qpat_assum `return_buf_sep (SOME _) c0 ei s`
           (mp_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
         asm_rewrite_tac[allocas_from_def]) >>
     qexistsl [`c0`,`ei`,`s`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!name b sz. local_region c0 ei.scopes u name b sz <=> _`
       (rewrite_tac o single)) >>
  MATCH_MP_TAC (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
    for_storage_observed_head_from_prefix) >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var ep) u = SOME addr` >>
  qexistsl [`lctx`,`tr`,`sd`,`ep`,`sa`,`st`,`k`,`addr`,`u`,`Gu`,`tnu`] >>
  `k < LENGTH vs` by
    (qpat_assum `len = LENGTH vs` (rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `w2n dst + nb < 2 ** 256` by
    (qpat_assum `w2n dst + nb < dimword (:256)` mp_tac >> simp[NoAsms, dimword_def]) >>
  `FLOOKUP u.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
   w2n dst + nb <= u.vs_alloca_next` by
    (map_every (fn q => qpat_assum q (rewrite_tac o single))
       [`u.vs_allocas = s.vs_allocas`,`u.vs_alloca_next = s.vs_alloca_next`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b sz. local_region c0 ei.scopes u name b sz ==>
     w2n dst + nb <= b \/ b + sz <= w2n dst` by
    (qpat_assum `!name b sz. local_region c0 ei.scopes u name b sz <=> _`
       (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> for_captured_storage_live _ _ _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
