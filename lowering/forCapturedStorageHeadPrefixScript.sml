Theory forCapturedStorageHeadPrefix
Ancestors
  forCapturedStorageLive bodyFullForStorage forStorageHeadFrame bodyFullShared
  exprPtrUnwrapRuntimeFrame slotCopyExecution freshWrites
  bodyPtrDefs stmtSimDefs compileEnv emitHelper venomState venomExecSemantics ptrDiscipline
  venomInst vyperStorageFootprint vyperStoragePlaceObserved vyperTypeValues
  words finite_map list rich_list

Theorem captured_live_index[local]:
  for_captured_storage_live exps (DF,lo,d,ctx,func,cx,c0,id,env,typ,loop_body)
    (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
    (lvo,idx,cond) (p,dst,nb,sd) (H,k,rs,ei,G,tn,s) ==>
  k = LENGTH vs - LENGTH rs
Proof
  rewrite_tac[for_captured_storage_live_def] >> strip_tac >>
  `LENGTH rs = LENGTH vs - k` by
    (qpat_assum `rs = DROP k vs` (fn th => rewrite_tac[th,LENGTH_DROP])) >>
  map_every (fn q => qpat_assum q mp_tac)
    [`LENGTH rs = LENGTH vs - k`,`k <= len`,`len = LENGTH vs`] >>
  POP_ASSUM_LIST (K decide_tac)
QED

(* Choose the scalar execution once. Only the child observation and its
   relational frame depend on the current horizon. *)
Theorem for_captured_storage_head_prefix:
  lookup_block cond func.fn_blocks = SOME cb /\
  cb.bb_instructions =
    [mk_inst (h - 2) EQ [Var idx;lvo] [dv];
     mk_inst (h - 1) JNZ [Var dv;Label exit;Label bod] []] /\
  lookup_block bod func.fn_blocks = SOME bb /\ saCopy.cs_current_bb = bod /\
  saCopy.cs_current_insts =
    [mk_inst h MUL [Var idx;Lit (n2w (type_slot_size tyv))] [ov]] ++
    (if (case bd of Fixed _ => F | Dynamic _ => T)
     then [mk_inst (h + 1) ADD [Lit 1w;Var ov] [tot]] else []) ++
    [mk_inst (h + if (case bd of Fixed _ => F | Dynamic _ => T) then 2 else 1) ADD
       [bop;Var (if (case bd of Fixed _ => F | Dynamic _ => T) then tot else ov)] [ep]] /\
  (!j. j < LENGTH saCopy.cs_current_insts ==>
       get_instruction bb j = SOME (fEL saCopy.cs_current_insts j)) /\
  ALL_DISTINCT (if (case bd of Fixed _ => F | Dynamic _ => T)
                then [dv;ov;tot;ep] else [dv;ov;ep]) /\
  (!x. MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
              then [dv;ov;tot;ep] else [dv;ov;ep]) ==> ~not_fresh_at sa0 x) /\
  ~MEM idx (if (case bd of Fixed _ => F | Dynamic _ => T)
            then [dv;ov;tot;ep] else [dv;ov;ep]) /\
  ~MEM p (if (case bd of Fixed _ => F | Dynamic _ => T)
          then [dv;ov;tot;ep] else [dv;ov;ep]) /\
  (!x. lvo = Var x ==> ~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
                               then [dv;ov;tot;ep] else [dv;ov;ep])) /\
  (!x. bop = Var x ==> ~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
                               then [dv;ov;tot;ep] else [dv;ov;ep])) /\
  sbExpr.cs_next_var <= saCopy.cs_next_var /\
  local_ptrs_reserved c0 sa0 /\
  (!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
  (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
  storage_trace_domain cx st0 ei.storage_trace /\
  (!H. valid_horizon cx st0 H ei.storage_trace ==>
       ?k. for_captured_storage_live exps (DF,lo,d,ctx,func,cx,c0,id,env,typ,loop_body)
         (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
         (lvo,idx,cond) (p,dst,nb,sd) (H,k,a::rs,ei,G,tn,s)) ==>
  ?k u Gu tnu.
    a::rs = DROP k vs /\ k < len /\ rs = DROP (SUC k) vs /\
    a = PlaceR (StoragePlace tr
      ((if (case bd of Fixed _ => F | Dynamic _ => T) then slot + 1w else slot) +
       n2w (k * type_slot_size tyv)) tyv) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK u,Gu,tnu)) /\
    u.vs_current_bb = saCopy.cs_current_bb /\
    u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var ep) u = SOME
      ((if (case bd of Fixed _ => F | Dynamic _ => T) then slot + 1w else slot) +
       n2w (k * type_slot_size tyv)) /\ op_taint tnu (Var ep) = {} /\
    (eval_operand bop u = SOME slot /\ op_taint tnu bop = {} /\
     slot_copy_external saCopy bop) /\
    !H. valid_horizon cx st0 H ei.storage_trace ==>
      for_captured_storage_live exps (DF,lo,d,ctx,func,cx,c0,id,env,typ,loop_body)
        (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
        (lvo,idx,cond) (p,dst,nb,sd) (H,k,a::rs,ei,G,tn,s) /\
      storage_place_observed H (StoragePlace tr
        ((if (case bd of Fixed _ => F | Dynamic _ => T) then slot + 1w else slot) +
         n2w (k * type_slot_size tyv)) tyv) /\
      stmt_state_rel H ctx func c0 cx ei u /\
      storage_well_formed_on cx ei (FST H) /\
      ghost_inv_at (DF H) lo d c0 cx ei Gu tnu u /\
      (alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       s0.vs_alloca_next <= u.vs_alloca_next /\
       (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
              lookup_var x u = SOME w) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                FLOOKUP u.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP Gu x = FLOOKUP G0 x /\
            op_taint tnu (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c0 ei u /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                       off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tnu.t_mem ==> i IN tn0.t_mem) /\
      return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u /\
      u.vs_current_bb = saCopy.cs_current_bb /\
      u.vs_inst_idx = LENGTH saCopy.cs_current_insts /\ ~u.vs_halted /\
      allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      lookup_var idx u = SOME (n2w k) /\ FLOOKUP Gu idx = NONE /\
      op_taint tnu (Var idx) = {} /\ eval_operand lvo u = SOME (n2w len) /\
      op_prov Gu lvo = NONE /\ op_taint tnu lvo = {} /\
      lookup_var p u = SOME dst /\ ptr_covers Gu tnu p u nb /\
      eval_operand (Var ep) u = SOME
        ((if (case bd of Fixed _ => F | Dynamic _ => T) then slot + 1w else slot) +
         n2w (k * type_slot_size tyv)) /\ op_taint tnu (Var ep) = {} /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_memory = s.vs_memory /\ u.vs_immutables = s.vs_immutables /\
      tnu.t_mem = tn.t_mem /\
      (!name b sz. local_region c0 ei.scopes u name b sz <=>
                   local_region c0 ei.scopes s name b sz) /\
      !x. ~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
                  then [dv;ov;tot;ep] else [dv;ov;ep]) ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
        op_taint tnu (Var x) = op_taint tn (Var x)
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ei.storage_trace` >>
  `valid_horizon cx st0 H0 ei.storage_trace` by
    simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?k. _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `k` assume_tac) >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ _ (H0,k,_,_,_,_,_)`
    (mp_then Any assume_tac captured_live_index) >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ _ (H0,k,_,_,_,_,_)`
    (mp_then Any (qspec_then `st0` mp_tac) for_captured_storage_live_child) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  CONV_TAC (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV])) >> strip_tac >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ _ (H0,k,_,_,_,_,_)`
    (strip_assume_tac o REWRITE_RULE[for_captured_storage_live_def]) >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at (DF H0) _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  `len < 2 ** 256` by
    (qpat_assum `len < dimword (:256)` mp_tac >> simp[NoAsms, wordsTheory.dimword_def]) >>
  drule_all (BETA_RULE (REWRITE_RULE[LET_THM] for_storage_array_head_prefix_at_prov)) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))) >>
  qexistsl [`k`,`u`,`Gu`,`tnu`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `a = PlaceR _` mp_tac >> Cases_on `bd` >> simp[NoAsms]) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "saved_operand" >>
  suspend "framed"
QED

Resume for_captured_storage_head_prefix[saved_operand]:
  Cases_on `bop`
  >- (qpat_assum `eval_operand (Lit _) s = _` mp_tac >>
      simp[NoAsms, eval_operand_def, op_taint_def, slot_copy_external_def])
  >- (rename1 `slot_copy_external saCopy (Var x)` >>
      `not_fresh_at sbExpr x` by
        (qpat_assum `!y. Var x = Var y ==> not_fresh_at sbExpr y`
           (qspec_then `x` mp_tac) >> simp[NoAsms]) >>
      `not_fresh_at saCopy x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists `sbExpr` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      `~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
                then [dv;ov;tot;ep] else [dv;ov;ep])` by
        (qpat_assum `!y. Var x = Var y ==> ~MEM y _`
           (qspec_then `x` mp_tac) >> simp[NoAsms]) >>
      qpat_assum `!y. ~MEM y _ ==> (lookup_var y u = _) /\ _`
        (qspec_then `x` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> qpat_assum `eval_operand (Var x) s = _` mp_tac >>
      qpat_assum `op_taint tn (Var x) = {}` mp_tac >>
      qpat_assum `op_taint tnu (Var x) = op_taint tn (Var x)` (rewrite_tac o single) >>
      qpat_assum `lookup_var x u = lookup_var x s`
        (fn th => simp[NoAsms, eval_operand_def, th]) >>
      rpt strip_tac >> irule slot_copy_not_fresh_external >> first_assum ACCEPT_TAC) >>
  qpat_assum `!lbl. Label _ <> Label lbl` mp_tac >> simp[NoAsms]
QED

Resume for_captured_storage_head_prefix[framed]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?k. _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `j` assume_tac) >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ _ (H,j,_,_,_,_,_)`
    (mp_then Any assume_tac captured_live_index) >>
  `j = k` by
    (qpat_assum `j = LENGTH vs - LENGTH (a::rs)` (rewrite_tac o single) >>
     qpat_assum `k = LENGTH vs - LENGTH (a::rs)` (rewrite_tac o single)) >>
  qpat_x_assum `j = k` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `for_captured_storage_live _ _ _ _ _ _ (H,k,_,_,_,_,_)`
        (mp_then Any (qspec_then `st0` mp_tac) for_captured_storage_live_child) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      Cases_on `bd` >> simp[NoAsms, LET_THM]) >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ _ (H,k,_,_,_,_,_)`
    (strip_assume_tac o REWRITE_RULE[for_captured_storage_live_def]) >>
  MATCH_MP_TAC (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
    for_storage_array_head_prefix_transport_outside) >>
  qexistsl [`bod`,`bb`] >>
  `!x. ~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
               then [dv;ov;tot;ep] else [dv;ov;ep]) ==> FLOOKUP Gu x = FLOOKUP G x` by
    (gen_tac >> disch_tac >>
     qpat_assum `!y. ~MEM y _ ==> (lookup_var y u = _) /\ _`
       (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  `!j. j < LENGTH saCopy.cs_current_insts ==>
       ?inst. get_instruction bb j = SOME inst /\ inst.inst_opcode <> ALLOCA` by
    (qx_gen_tac `j` >> disch_tac >> qexists `EL j saCopy.cs_current_insts` >>
     conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `j < LENGTH saCopy.cs_current_insts` mp_tac >>
     qpat_assum `saCopy.cs_current_insts = _` (rewrite_tac o single) >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bd` >> simp[] >> strip_tac
     >- (`j = 0 \/ j = 1` suffices_by (strip_tac >> simp[EL, mk_inst_def]) >> decide_tac) >>
     `j = 0 \/ j = 1 \/ j = 2` suffices_by (strip_tac >> simp[EL, mk_inst_def]) >> decide_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_captured_storage_head_prefix
