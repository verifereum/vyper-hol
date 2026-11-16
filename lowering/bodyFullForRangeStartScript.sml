Theory bodyFullForRangeStart
Ancestors
  bodyFullForRangeEmpty bodyExprPreFacts fragExec vyperState
  stmtSimForParts stmtSimForRange vyperInterpreter vyperStorageBackend
  bodyFullShared bodyFullUnwrapSlotPost bodyPtrBopInLiteralSuffix forPtrScalarStore
  vyperStorageFootprint list ptrDiscipline venomInst venomState
  venomExecSemantics finite_map pred_set bodyPtrDefs bodyMemoryDefs
  loweringStateRelDefs exprLoweringProps venomMemDefs
  stmtForRangeMemoryParts venomExecProofs exprPtrUnwrapCopyEdges
  instMemFrontier fragGasOriginPtr fragGasOriginPtrLoop ptrSafeRun
  emitHelperProps words fragGasSeqPtr memSafeRun stmtSimProps
  exprSimHypsDefs vyperTypeInvariants stmtSimDeclStore loweringSlice localPtrsProps
  valueEncodingProps valueEncoding exprSimOperands compileEnv stmtSimDefs allocaHistory

Theorem for_range_store_path_canonical_full:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid MSTORE [Var dst; Var cv] []) /\
  ~s.vs_halted /\ lookup_var dst s = SOME addr /\
  lookup_var cv s = SOME value /\ alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (w2n addr,sz) /\ 32 <= sz /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid MSTORE [Var dst; Var cv] [];
      u = mstore (w2n addr) value s in
  !H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> gen_tac >>
  qabbrev_tac `i = mk_inst iid MSTORE [Var dst; Var cv] []` >>
  qabbrev_tac `u = mstore (w2n addr) value s` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`,Abbr `u`] >> irule step_MSTORE >>
     simp[eval_operand_def]) >>
  `inst_mem_below_frontier i s` by
    (simp[Abbr `i`] >> irule for_range_allocated_store_below >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`aid`,`w2n addr`,`sz`] >> simp[eval_operand_def,w2n_lt]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u,step_taint i s u tn)` by
    (simp[Abbr `i`,mk_inst_def] >>
     irule (SRULE [mk_inst_def,is_terminator_def]
       (Q.INST [`i` |-> `mk_inst iid MSTORE [Var dst; Var cv] []`]
          straight_line_origin_ptr_edge)) >>
     simp[GSYM mk_inst_def,inst_dload_in_section_def] >> metis_tac[]) >>
  `~u.vs_halted` by simp[Abbr `u`,mstore_def] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem for_range_literal_entry_packet_full:
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var cv; Var ev] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block body_lbl func.fn_blocks = SOME bbb /\
  get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var q; Var cv] []) /\
  sb0.cs_current_bb = body_lbl /\
  sb0.cs_current_insts = [mk_inst j3 MSTORE [Var q; Var cv] []] /\
  sa.cs_next_var <= sb0.cs_next_var /\
  declare_local cenv id typ sa = (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
  q = STRING #"%" (toString sa.cs_next_var) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) (fn_insts func) /\
  fn_inst_ids_distinct func /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  is_int_type typ /\ type_memory_bytes cenv typ = 32 /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\ n1 <= n2 /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x. not_fresh_at sa x ==> x <> dv) /\ q <> dv /\ cv <> dv /\ ev <> dv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
  ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var q s = SOME w /\ ptr_covers G tn q s 32 /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
  w2n w + 32 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    regions_disjoint (w2n w) 32 b len) /\
  FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  lookup_var ev s = SOME (i2w n2) /\
  (?kk. kk <= Num (n2-n1) /\
    a::rs = DROP kk (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
    lookup_var cv s = SOME (i2w (n1 + &kk)) /\
    n1 + &kk <= n2 /\ Num (n2-n1) < dimword (:256)) /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
  (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP s.vs_allocas aid = SOME bl) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  k < Num (n2-n1) /\ lookup_var cv s = SOME (i2w (n1 + &k)) /\
  value_has_type tyv (IntV (n1 + &k)) ==>
  let ci = mk_inst j1 EQ [Var cv; Var ev] [dv];
      cu = update_var dv 0w s;
      Gc = step_prov PG G ci cu;
      tc = step_taint ci s cu tn;
      sc = jump_to body_lbl cu;
      si = mk_inst j3 MSTORE [Var q; Var cv] [];
      su = mstore (w2n w) (i2w (n1 + &k)) sc;
      ss = su with vs_inst_idx := 1;
      Gs = step_prov PG Gc si su;
      ts = step_taint si sc su tc;
      pushed = (ee with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
          value := IntV (n1 + &k); popped := []|>)) :: ee.scopes)
        with gas_obs := [] in
  (expr_sim_inv bc cx (extend_local env id typ F) pushed /\
   stmt_state_rel H ctx func bc cx pushed ss /\
   storage_well_formed_on cx pushed (FST H) /\
   return_buf_frame d bc sb0 ss /\ alloca_history func ss /\
   ghost_inv_at (DF H) lo d bc cx pushed Gs ts ss /\
   ~ss.vs_halted /\ ss.vs_current_bb = sb0.cs_current_bb /\
   ss.vs_inst_idx = LENGTH sb0.cs_current_insts /\
   ret_pc_ok bc sb0 ss /\ allocas_from lo ss /\
   lookup_var q ss = SOME w /\ ptr_covers Gs ts q ss 32 /\
   FLOOKUP ss.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
   w2n w + 32 < dimword (:256) /\ w2n w + 32 <= ss.vs_alloca_next /\
   (!name b len. local_region cenv ee.scopes ss name b len ==>
     regions_disjoint (w2n w) 32 b len) /\
   FLOOKUP Gs cv = NONE /\ FLOOKUP Gs ev = NONE /\
   op_taint ts (Var cv) = {} /\ op_taint ts (Var ev) = {} /\
   lookup_var ev ss = SOME (i2w n2) /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
   (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x ss = SOME v) /\
   (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP ss.vs_allocas aid = SOME bl) /\
   (!x. not_fresh_at sa x ==> FLOOKUP Gs x = FLOOKUP G0 x /\
     op_taint ts (Var x) = op_taint tn0 (Var x))) /\
  lookup_var cv ss = SOME (i2w (n1 + &k))
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `jump_to body_lbl cu` >>
  qmatch_goalsub_abbrev_tac `mstore (w2n w) (i2w (n1 + &k)) sc` >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx func bc cx pushed ss` >>
  `lookup_scopes id ee.scopes = NONE` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     simp[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def] >>
     strip_tac >> Cases_on `lookup_scopes id ee.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = SOME _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `not_local_ptr cenv ee.scopes dv` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := FEMPTY :: ee.scopes) sc` by
    (simp[Abbr `sc`,Abbr `cu`,stmt_state_rel_jump_to,stmt_state_rel_push_scope] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `bc.ce_module_vars = cenv.ce_module_vars /\ bc.ce_module = cenv.ce_module /\
   bc.ce_is_ctor = cenv.ce_is_ctor /\ bc.ce_imm_alloca = cenv.ce_imm_alloca /\
   bc.ce_module_var_type = cenv.ce_module_var_type` by
    (qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
       mp_tac >> simp[compile_env_component_equality]) >>
  `stmt_state_rel H ctx func bc cx (ee with scopes := FEMPTY :: ee.scopes) sc` by
    (irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >> simp[] >>
     rpt strip_tac >> Cases_on `n = id` >> gvs[lookup_scopes_def] >>
     res_tac >> gvs[]) >>
  `is_word_type typ` by
    (Cases_on `typ` >> fs[vyperTypeSystemTheory.is_int_type_def,is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[vyperTypeSystemTheory.is_int_type_def,is_word_type_def]) >>
  `type_memory_size tyv = 32 /\ word_memory_type tyv` by
    (drule_all store_lays_out_typed >> simp[store_lays_out_def]) >>
  `memory_value_rel tyv (IntV (n1 + &k)) (w2n w)
     (mstore (w2n w) (i2w (n1 + &k)) sc).vs_memory` by
    (irule (SRULE [word_value_def,val_to_w256_def]
       (Q.SPECL [`tyv`,`IntV (n1 + &k)`] word_value_memory_rel)) >> simp[]) >>
  `val_wf tyv (IntV (n1 + &k))` by
    (irule word_value_wf >> simp[word_value_def]) >>
  `stmt_state_rel H ctx func bc cx pushed ss` by
    (simp[Abbr `ss`,Abbr `pushed`,stmt_state_rel_inst_idx,stmt_state_rel_start_gas_obs] >>
     irule (SRULE [] (Q.INST [`es` |-> `ee with scopes := FEMPTY :: ee.scopes`]
       (SPEC_ALL stmt_state_rel_declare_store))) >>
     simp[lookup_scopes_def] >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]` >>
     simp[mk_inst_def,lookup_scopes_def,Abbr `sc`,Abbr `cu`,
          jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
     conj_tac
     >- gvs[lookup_var_def] >>
     `not_local_ptr cenv ee.scopes q` by
       (irule fresh_not_local_ptr >> qexists_tac `sa` >>
        simp[not_fresh_at_def]) >>
     fs[not_local_ptr_def,lookup_scopes_def] >>
     rpt strip_tac >> Cases_on `name = id` >> gvs[] >>
     metis_tac[]) >>
  `alloca_history func ss /\ allocas_from lo ss /\
   ~ss.vs_halted /\ ss.vs_current_bb = body_lbl /\ ss.vs_inst_idx = 1 /\
   ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
   (!x. x <> dv ==> lookup_var x ss = lookup_var x s)` by
    (fs[alloca_history_def,allocas_from_def] >>
     simp[Abbr `ss`,Abbr `sc`,Abbr `cu`,mstore_def,jump_to_def,
          update_var_def,lookup_var_def,FLOOKUP_UPDATE,
          alloca_history_def,allocas_from_def] >>
     rpt strip_tac >> simp[EQ_SYM_EQ] >>
     qpat_x_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
       irule >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `ghost_inv_at (DF H) lo d bc cx pushed Gs ts ss` >>
  `Gs = DRESTRICT G (COMPL {dv})` by
    simp[Abbr `Gs`,step_prov_def,out_prov_def,set_prov_def,mk_inst_def] >>
  `expr_sim_inv bc cx (extend_local env id typ F) pushed` by
    (simp[Abbr `pushed`,expr_sim_inv_gas_obs] >>
     irule expr_sim_inv_for_scope >> metis_tac[]) >>
  `!x. x <> dv ==> op_taint ts (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `ts`] >> rpt strip_tac >>
     simp[decoderGhostFramePtrTheory.step_taint_other_output,mk_inst_def]) >>
  `bc.ce_return_buf = cenv.ce_return_buf /\ bc.ce_return_pc = cenv.ce_return_pc` by
    (qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
       mp_tac >> simp[compile_env_component_equality]) >>
  `return_buf_frame d bc sb0 ss` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[] >>
     metis_tac[]) >>
  `ret_pc_ok bc sb0 ss` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     metis_tac[]) >>
  simp[FLOOKUP_DRESTRICT] >>
  conj_tac
  >- fs[Abbr `pushed`,vyperStorageFootprintTheory.storage_well_formed_on_def,oneline get_storage_def] >>
  reverse conj_tac
  >- (conj_tac
      >- (qpat_x_assum `ptr_covers G tn q s 32` mp_tac >>
          simp[ptr_covers_def,FLOOKUP_DRESTRICT] >> metis_tac[]) >>
      rpt strip_tac >> qpat_x_assum `!name b len. local_region _ _ s _ _ _ ==> _` irule >>
      qexists_tac `name` >>
      fs[local_region_def,not_local_ptr_def] >> metis_tac[]) >>
  `ts.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
   ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\ ts.t_imm = tn.t_imm` by
    (simp[Abbr `ts`,step_taint_def,mk_inst_def,Abbr `sc`,Abbr `cu`,
          jump_to_def,update_var_def,eval_operand_def,lookup_var_def,
          FLOOKUP_UPDATE,op_taint_def,set_var_taint_def,mem_taint_def,
          imm_taint_def,new_site_bytes_def,step_writes_def,
          written_taint_def,range_bytes_def,
          store_taint_def,adopt_reset_def,mstore_def,write_memory_with_expansion_def] >>
     gvs[lookup_var_def,op_taint_def,codegenRelTheory.source_memory_write_ranges_def,
         codegenRelTheory.fixed_source_write_range_def,eval_operand_def,
         FLOOKUP_UPDATE,FLOOKUP_DEF,EXTENSION,FAPPLY_FUPDATE_THM] >>
     simp[EQ_SYM_EQ] >> metis_tac[]) >>
  `!off len. off+len <= w2n w \/ w2n w+32 <= off ==>
    mem_bytes_at off len ss.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `ss`] >>
     `mem_bytes_at off len (mstore (w2n w) (i2w (n1 + &k)) sc).vs_memory =
      mem_bytes_at off len sc.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
     simp[Abbr `sc`,Abbr `cu`,jump_to_def,update_var_def]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee (DRESTRICT G (COMPL {dv})) ts ss` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     conj_tac >- fs[ghost_inv_at_def] >>
     conj_tac >- simp[] >>
     conj_tac
     >- (fs[ghost_inv_at_def,stor_taint_ok_at_def] >>
         simp[Abbr `ss`,Abbr `sc`,Abbr `cu`,mstore_def,jump_to_def,update_var_def] >>
         metis_tac[]) >>
     qexistsl_tac [`G`,`func`,`32`,`s`,`sa`,`w2n w`,`tn`] >>
     simp[FLOOKUP_DRESTRICT] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b len. local_region _ _ s _ _ _ ==> _`
           (qspecl_then [`name`,`b`,`len`] mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     conj_tac >- (qpat_x_assum `ret_pc_ok cenv sa s0` mp_tac >>
                  simp[loweringPostsTheory.ret_pc_ok_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
     fs[stmt_state_rel_def,state_rel_def]) >>
  qpat_x_assum `ghost_inv_at (DF H) lo d cenv cx ee _ ts ss` mp_tac >>
  simp[ghost_inv_at_def,Abbr `pushed`] >>
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `name = id`
      >- (gvs[lookup_scopes_def,FLOOKUP_UPDATE] >> conj_tac
          >- (qpat_x_assum `ptr_covers G tn _ s 32` mp_tac >>
              simp[ptr_covers_def,FLOOKUP_DRESTRICT] >> metis_tac[]) >>
          rpt strip_tac >> irule scalar_mstore_robust >>
          simp[valueEncodingTheory.val_to_w256_def] >>
          qexistsl_tac [`sc`,`tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32}`] >>
          gvs[Abbr `ss`]) >>
      gvs[lookup_scopes_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair) bc _ _ _` >>
  PairCases_on `pair` >> gvs[return_buf_ptr_def] >> metis_tac[]
QED

val range_entry_packet_normal =
  SIMP_RULE bool_ss [LET_THM,expr_sim_inv_gas_obs,stmt_state_rel_start_gas_obs]
    for_range_literal_entry_packet_full;

Theorem for_range_literal_body_start_full:
  (!PG G tn j1 j2 cv ev dv cc a b bb lbl exit_lbl body_lbl ctx func lo explicit.
    let i = mk_inst j1 EQ [Var cv; Var ev] [dv];
        u = update_var dv (bool_to_word (a=b)) cc;
        Gf = step_prov PG G i u;
        tf = step_taint i cc u tn
    in
    bb = <|bb_label := lbl; bb_instructions :=
      [i; mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    ~ctx_has_dalloca ctx /\ allocas_from lo cc ==>
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (cc,G,tn) []
      (OK (jump_to (if a=b then exit_lbl else body_lbl) u),Gf,tf)) /\
  (!s func bb iid dst cv addr value aid sz G tn lo ctx DF explicit.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst iid MSTORE [Var dst; Var cv] []) /\
    ~s.vs_halted /\ lookup_var dst s = SOME addr /\
    lookup_var cv s = SOME value /\ alloca_inv s /\
    FLOOKUP s.vs_allocas aid = SOME (w2n addr,sz) /\ 32 <= sz /\
    ptr_covers G tn dst s 32 /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn'. !H.
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (mstore (w2n addr) value s with vs_inst_idx := SUC s.vs_inst_idx),G',tn')) /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var cv; Var ev] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> /\
  lookup_block body_lbl func.fn_blocks = SOME bbb /\
  get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var q; Var cv] []) /\
  sb0.cs_current_bb = body_lbl /\
  sb0.cs_current_insts = [mk_inst j3 MSTORE [Var q; Var cv] []] /\
  sa.cs_next_var <= sb0.cs_next_var /\
  declare_local cenv id typ sa = (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
  q = STRING #"%" (toString sa.cs_next_var) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) (fn_insts func) /\
  fn_inst_ids_distinct func /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  is_int_type typ /\ type_memory_bytes cenv typ = 32 /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\ n1 <= n2 /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x. not_fresh_at sa x ==> x <> dv) /\ q <> dv /\ cv <> dv /\ ev <> dv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx ==>
  let Inv = \H rs ee G tn s.
    expr_sim_inv cenv cx env ee /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    lookup_var q s = SOME w /\ ptr_covers G tn q s 32 /\
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    lookup_var ev s = SOME (i2w n2) /\
    (?k. k <= Num (n2-n1) /\
      rs = DROP k (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
      lookup_var cv s = SOME (i2w (n1 + &k)) /\
      n1 + &k <= n2 /\ Num (n2-n1) < dimword (:256)) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x));
      BodyStart = \ee v H sstart Gstart tnstart.
    let pushed = (ee with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: ee.scopes)
      with gas_obs := [] in
    expr_sim_inv bc cx (extend_local env id typ F) pushed /\
    stmt_state_rel H ctx func bc cx pushed sstart /\
    storage_well_formed_on cx pushed (FST H) /\
    return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
    ghost_inv_at (DF H) lo d bc cx pushed Gstart tnstart sstart /\
    ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
    sstart.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    ret_pc_ok bc sb0 sstart /\ allocas_from lo sstart /\
    lookup_var q sstart = SOME w /\ ptr_covers Gstart tnstart q sstart 32 /\
    FLOOKUP sstart.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ w2n w + 32 <= sstart.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes sstart name b len ==>
      regions_disjoint (w2n w) 32 b len) /\
    FLOOKUP Gstart cv = NONE /\ FLOOKUP Gstart ev = NONE /\
    op_taint tnstart (Var cv) = {} /\ op_taint tnstart (Var ev) = {} /\
    lookup_var ev sstart = SOME (i2w n2) /\
    s0.vs_alloca_next <= sstart.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x sstart = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP sstart.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gstart x = FLOOKUP G0 x /\
      op_taint tnstart (Var x) = op_taint tn0 (Var x))
  in !a rs ee s G tn.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Inv H (a::rs) ee G tn s) ==>
    ?k sstart Gstart tnstart.
      k < Num (n2-n1) /\ a = Value (IntV (n1 + &k)) /\
      rs = DROP (SUC k) (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1))) /\
      read_result cx a ee = (INL (IntV (n1 + &k)),ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK sstart,Gstart,tnstart) /\
        BodyStart ee (IntV (n1 + &k)) H sstart Gstart tnstart /\
        lookup_var cv sstart = SOME (i2w (n1 + &k)))
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  `k < Num (n2-n1) /\ a = Value (IntV (n1 + &k)) /\
   rs = DROP (SUC k) (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2-n1)))` by
    (qpat_x_assum `_::_ = DROP _ _` (mp_tac o GSYM) >>
     disch_then (strip_assume_tac o MATCH_MP DROP_EQ_CONS) >> gvs[EL_GENLIST]) >>
  `value_has_type tyv (IntV (n1 + &k))` by
    (irule range_value_has_type >> metis_tac[]) >>
  `i2w (n1 + &k) <> (i2w n2 : bytes32)` by
    (irule i2w_counter_ne >> simp[]) >>
  qabbrev_tac `ci = mk_inst j1 EQ [Var cv; Var ev] [dv]` >>
  qabbrev_tac `cu = update_var dv 0w s` >>
  qabbrev_tac `Gc = step_prov PG G ci cu` >>
  qabbrev_tac `tc = step_taint ci s cu tn` >>
  qabbrev_tac `sc = jump_to body_lbl cu` >>
  `!D. gas_origin_ptr_path
      (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK sc,Gc,tc)` by
    (qpat_assum `!PG G tn j1 j2 cv ev dv cc a b bb lbl exit_lbl body_lbl ctx func lo explicit. _`
       (mp_tac o Q.INST [`cc` |-> `s`, `a` |-> `i2w (n1 + &k) : bytes32`,
          `b` |-> `i2w n2 : bytes32`,
          `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
          o SPEC_ALL o SRULE [LET_THM]) >>
     simp[Abbr `ci`, Abbr `cu`, Abbr `Gc`, Abbr `tc`, Abbr `sc`]) >>
  `tc = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tc`,Abbr `ci`,Abbr `cu`,membership_scalar_ghost_frame] >>
  `!x. x <> dv ==> FLOOKUP Gc x = FLOOKUP G x /\
        op_taint tc (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `Gc`,Abbr `ci`,step_prov_def,out_prov_def,set_prov_def,
          mk_inst_def,FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `lookup_var q sc = SOME w /\
   lookup_var cv sc = SOME (i2w (n1 + &k)) /\
   sc.vs_current_bb = body_lbl /\ sc.vs_inst_idx = 0 /\ ~sc.vs_halted /\
   FLOOKUP sc.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
   allocas_from lo sc` by
    (fs[Abbr `sc`,Abbr `cu`,jump_to_def,update_var_def,lookup_var_def,
         FLOOKUP_UPDATE,allocas_from_def] >> metis_tac[]) >>
  `ptr_covers Gc tc q sc 32` by
    (fs[ptr_covers_def] >> gvs[]) >>
  `alloca_inv sc` by
    (`stmt_state_rel H0 ctx func cenv cx ee s` by metis_tac[] >>
     fs[stmt_state_rel_def] >>
     fs[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def,
        Abbr `sc`,Abbr `cu`,jump_to_def,update_var_def] >> metis_tac[]) >>
  qabbrev_tac `si = mk_inst j3 MSTORE [Var q; Var cv] []` >>
  qabbrev_tac `su = mstore (w2n w) (i2w (n1 + &k)) sc` >>
  qabbrev_tac `ss = su with vs_inst_idx := 1` >>
  qabbrev_tac `Gs = step_prov PG Gc si su` >>
  qabbrev_tac `ts = step_taint si sc su tc` >>
  `!H. gas_origin_ptr_path
      (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (sc,Gc,tc) [] (OK ss,Gs,ts)` by
    (simp[Abbr `ss`,Abbr `su`,Abbr `Gs`,Abbr `ts`,Abbr `si`] >>
     gen_tac >>
     qpat_assum `sc.vs_inst_idx = 0` (fn th =>
       irule (SRULE [LET_THM,th] (Q.INST [`s` |-> `sc`]
         for_range_store_path_canonical_full))) >>
     gvs[] >> qexistsl_tac [`sa.cs_next_id`,`32`] >> simp[]) >>
  qexistsl_tac [`k`,`ss`,`Gs`,`ts`] >>
  pure_rewrite_tac[read_result_def,return_def,LET_THM] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[read_result_def,return_def] >>
  gen_tac >> strip_tac >>
  conj_tac >- (irule gas_origin_ptr_path_trans >>
    qexistsl_tac [`Gc`,`sc`,`tc`] >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  simp_tac pure_ss [Abbr `ss`,Abbr `Gs`,Abbr `ts`,Abbr `su`,
       Abbr `si`,Abbr `sc`,Abbr `Gc`,Abbr `tc`,Abbr `cu`,Abbr `ci`] >>
  qpat_x_assum `q = STRING _ _` SUBST_ALL_TAC >>
  qpat_assum `sb0.cs_current_bb = _` (fn bb_th =>
    qpat_assum `sb0.cs_current_insts = _` (fn is_th =>
      qpat_assum `w2n w + 32 < dimword (:256)` (fn bound_th =>
        irule (REWRITE_RULE [bb_th,is_th,bound_th,LENGTH,GSYM arithmeticTheory.ONE,
          evaluation_state_fupdcanon] range_entry_packet_normal)))) >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`a`,`rs`,`k`] >> gvs[]) >>
  conj_tac >- (qpat_x_assum `!x. not_fresh_at sa x ==> x <> dv`
    (qspec_then `dv` mp_tac) >> simp[]) >>
  conj_tac >- (qexistsl_tac [`exit_lbl`,`j2`] >> simp[]) >>
  gvs[]
QED
