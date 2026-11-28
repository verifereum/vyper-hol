Theory forCapturedStorageLive
Ancestors
  exprSimHypsDefs[qualified]
  bodyFullPredsMods[qualified]
  bodyFullForStorageCapture bodyFullPreds bodyFullForFrame loweringStateRelDefs
  stmtSimDefs bodyPtrDefs allocaHistory ptrDiscipline compileEnv
  vyperStorageFootprint vyperStoragePlaceObserved vyperStoragePlaceRegion
  vyperInterpreter vyperState vyperTypeValues fragExec venomState venomInst
  words finite_map list

(* The register age of the saved slot is the expression cut, while the
   exterior allocation/register frame is relative to the original entry.
   The captured array is a subregion of an earlier trace root; no equality
   of storage contents between the capture and the loop head is required. *)
Definition for_captured_storage_live_def:
  for_captured_storage_live exps (DF,lo,d,ctx,func,cx,c0,id,env,typ,loop_body)
    (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
    (lvo,idx,cond) (p,dst,nb,sd)
    (H : (bool # 256 word # type_value) list # num list,k,rs,ee,G,tn,s) <=>
    k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
    len < dimword (:256) /\ rs = DROP k vs /\
    vs = GENLIST (\j. PlaceR (StoragePlace tr
      ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
       n2w (j * type_slot_size tyv)) tyv)) len /\
    (?extra. ee.storage_trace = em.storage_trace ++ extra) /\
    (?off root path delta.
      MEM (StorageRoot tr off root) em.storage_trace /\
      storage_subregion root path delta (ArrayTV tyv bd) /\
      slot = n2w off + n2w delta) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ well_formed_type_value tyv /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
    op_taint tn (Var idx) = {} /\
    eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
    op_prov G lvo = NONE /\
    eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
    (!x. bop = Var x ==> not_fresh_at sbExpr x) /\ (!lbl. bop <> Label lbl) /\
    lookup_var p s = SOME dst /\
    FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
    ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
    w2n dst + nb < dimword (:256) /\ w2n dst + nb <= s.vs_alloca_next /\
    (!name b sz. local_region c0 ee.scopes s name b sz ==>
      w2n dst + nb <= b \/ b + sz <= w2n dst) /\
    lookup_scopes id ee.scopes = NONE /\
    expr_sim_inv_mods c0.ce_modules c0 cx env ee /\ ce_locals_declared c0 env /\
    locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
    stmt_state_rel H ctx func c0 cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
    return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\ return_buf_sep d c0 ee s /\
    (k <> 0 ==> body_stmts_full_ok_mods c0.ce_modules exps cx loop_body) /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 c0 ee s /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!name b n. local_region c0 e0.scopes s0 name b n ==>
        off + sz <= b \/ b + n <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)
End

Theorem for_captured_storage_live_child:
  for_captured_storage_live exps (DF,lo,d,ctx,func,cx,c0,id,env,typ,loop_body)
    (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
    (lvo,idx,cond) (p,dst,nb,sd) (H,k,a::rs,ee,G,tn,s) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  k < len /\ rs = DROP (SUC k) vs /\
  a = PlaceR (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (k * type_slot_size tyv)) tyv) /\
  storage_place_observed H (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (k * type_slot_size tyv)) tyv)
Proof
  rewrite_tac[for_captured_storage_live_def] >> BETA_TAC >> strip_tac >>
  qpat_assum `a::rs = DROP k vs` (strip_assume_tac o MATCH_MP DROP_EQ_CONS o SYM) >>
  `k < len` by
    (qpat_assum `len = LENGTH vs` (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- qpat_assum `DROP (SUC k) vs = rs` (ACCEPT_TAC o SYM) >>
  conj_tac
  >- (qpat_assum `EL k vs = a` (rewrite_tac o single o SYM) >>
      qpat_assum `vs = GENLIST _ _` (rewrite_tac o single) >>
      qpat_assum `k < len` (fn th => simp[NoAsms, th])) >>
  irule for_storage_iterator_child_observed >>
  conj_tac >- decide_tac >>
  `MEM (StorageRoot tr off root) ee.storage_trace` by
    (qpat_assum `ee.storage_trace = _` (rewrite_tac o single) >>
     rewrite_tac[MEM_APPEND] >> disj1_tac >> first_assum ACCEPT_TAC) >>
  irule stmtSimAugAssignPlaceStorageTheory.aug_place_storage_rooted_observed >>
  qexistsl [`cx`,`delta`,`off`,`path`,`st0`,`ee.storage_trace`,`root`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
