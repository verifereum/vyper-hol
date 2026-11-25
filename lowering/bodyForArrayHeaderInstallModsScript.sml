(* From the length endpoint to the Array condition: one ALLOCA and
   scalar entry control. Route-specific observations are transported separately. *)
Theory bodyForArrayHeaderInstallMods
Ancestors
  bodyForArrayHeaderMods bodyForRangeScalarFrameMods bodyFullForArrayRound
  bodyFullPostsMods bodyInvSplit bodyForRangeHeaderMods vyperStorageFootprint
  bodyFullAllocaFresh bodyFullHashKeccakFixed bodyFullIfExpReach bodyFullShared
  assignTuplePtrCopyLen robustCopyTransportPtr loweringHalt stateRelProj
  loweringStateRelDefs exprSimOperands fragGasOriginPtrLoop fragGasOriginPtr
  fragFuelExprHelpers allocaHistory contextRawReachable exprLoweringProps
  bodyMemoryDefs bodyFullShadowBodyInv stmtSimDefs stmtSimProps freshWrites
  stmtLowering compileEnv venomExecSemantics venomState venomInst venomMemDefs
  ptrDiscipline bodyPtrDefs loweringPosts fragExec finite_map words list
  vyperAST rich_list arithmetic
Libs
  monadsyntax

(* The parts of the length-endpoint frame needed by all three routes.
   Full memory equality does not imply full taint equality: the allocation
   can add taint above the old frontier. *)
Definition for_array_install_frame_mods_def[nocompute]:
  for_array_install_frame_mods saL u Gu tu G tn t <=>
    t.vs_memory = u.vs_memory /\ t.vs_data_section = u.vs_data_section /\
    t.vs_labels = u.vs_labels /\ t.vs_immutables = u.vs_immutables /\
    t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
    t.vs_call_ctx = u.vs_call_ctx /\ u.vs_alloca_next <= t.vs_alloca_next /\
    (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==>
               FLOOKUP t.vs_allocas aid = SOME row) /\
    (!x. not_fresh_at saL x ==>
         lookup_var x t = lookup_var x u /\ FLOOKUP G x = FLOOKUP Gu x /\
         op_taint tn (Var x) = op_taint tu (Var x)) /\
    tn.t_stor = tu.t_stor /\ tn.t_trans = tu.t_trans /\ tn.t_imm = tu.t_imm /\
    (!i. i < u.vs_alloca_next ==> (i IN tn.t_mem <=> i IN tu.t_mem))
End

Theorem array_install_operand[local]:
  for_array_install_frame_mods saL u Gu tu G tn t /\
  (!x. op = Var x ==> not_fresh_at saL x) ==>
  eval_operand op t = eval_operand op u /\ op_prov G op = op_prov Gu op /\
  op_taint tn op = op_taint tu op
Proof
  Cases_on `op` >> simp[for_array_install_frame_mods_def, eval_operand_def,
                        op_prov_def, op_taint_def] >>
  strip_tac >> first_x_assum drule >> simp[op_taint_def]
QED

Theorem array_install_row_taint[local]:
  alloca_inv u /\ for_array_install_frame_mods saL u Gu tu G tn t /\
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b + sz /\
  i IN tn.t_mem ==> i IN tu.t_mem
Proof
  simp[alloca_inv_def, alloca_next_valid_def, for_array_install_frame_mods_def] >>
  strip_tac >>
  qpat_assum `!a b z. FLOOKUP u.vs_allocas a = _ ==> _` (drule_then assume_tac) >>
  `i < u.vs_alloca_next` by decide_tac >>
  qpat_assum `!i. i < u.vs_alloca_next ==> _` (drule_then mp_tac) >> simp[]
QED

Theorem array_install_regions[local]:
  local_ptrs_reserved cenv saL /\ cenv'.ce_vars = cenv.ce_vars /\
  (!x. not_fresh_at saL x ==> lookup_var x t = lookup_var x u) ==>
  (local_region cenv' scopes t n b sz <=> local_region cenv' scopes u n b sz)
Proof
  strip_tac >> irule local_region_lookup_cong >> simp[] >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem array_install_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx em Gu tu u /\
  local_ptrs_rel func cenv em.scopes u /\ local_ptrs_reserved cenv saL /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x) /\
  for_array_install_frame_mods saL u Gu tu G tn t /\ allocas_from lo t ==>
  ghost_inv_at_mods D lo d cenv cx em G tn t
Proof
  strip_tac >> fs[for_array_install_frame_mods_def] >>
  `!p sz. not_fresh_at saL p /\ ptr_covers Gu tu p u sz ==>
          ptr_covers G tn p t sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gu tu p u sz` (irule_at Any) >> simp[]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at saL p` by metis_tac[local_ptrs_reserved_def] >>
      qpat_assum `!name entry p sz. _ ==> ptr_covers Gu tu p u sz /\ _`
        (drule_all_then strip_assume_tac) >>
      conj_tac >- simp[] >>
      rpt strip_tac >> `lookup_var p u = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\
       w2n w + val_footprint entry.type entry.value <= u.vs_alloca_next` by
        (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
         simp[local_ptrs_rel_def] >> strip_tac >>
         first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
         drule exprSimPropsTheory.val_footprint_le >> strip_tac >> decide_tac) >>
      irule robust_val_in_memory_decreasing_taint_transport >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`u.vs_memory`, `t.vs_memory`, `val_footprint entry.type entry.value`,
                `w2n w`, `tu.t_mem`, `tn.t_mem`] >>
      simp[] >> rpt strip_tac >>
      `i + w2n w < u.vs_alloca_next` by decide_tac >>
      qpat_assum `!i. i < u.vs_alloca_next ==> _` (drule_then mp_tac) >> simp[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- metis_tac[]
  >- fs[stor_taint_ok_at_def]
  >- (rpt strip_tac >> `i < u.vs_alloca_next` by decide_tac >> metis_tac[])
  >- metis_tac[local_ptrs_reserved_imm_base]
  >- first_assum ACCEPT_TAC
  >- decide_tac
QED

Theorem array_install_immutable[local]:
  immutable_frame_mods func cenv cx em u /\ local_ptrs_reserved cenv saL /\
  exec_alloca ins u (n : bytes32) = OK raw /\
  t.vs_allocas = raw.vs_allocas /\ t.vs_alloca_next = raw.vs_alloca_next /\
  t.vs_memory = raw.vs_memory /\ raw.vs_memory = u.vs_memory /\
  t.vs_data_section = u.vs_data_section /\
  (!x. not_fresh_at saL x ==> lookup_var x t = lookup_var x u /\
                              lookup_var x raw = lookup_var x u) ==>
  immutable_frame_mods func cenv cx em t
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  `!id b z. local_region (cenv with ce_module := src) em.scopes raw id b z <=>
            local_region (cenv with ce_module := src) em.scopes u id b z` by
    (rpt gen_tac >> irule array_install_regions >>
     qpat_assum `local_ptrs_reserved cenv saL` (irule_at Any) >> simp[]) >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx em raw` by
    (irule immutable_alloca_sep_exec_alloca >>
     qexistsl [`ins`, `n`, `u`] >> simp[] >> metis_tac[]) >>
  irule immutable_alloca_sep_fields >> qexistsl [`raw`, `em`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  `local_region (cenv with ce_module := src) em.scopes t id b sz <=>
   local_region (cenv with ce_module := src) em.scopes u id b sz` by
    (irule array_install_regions >>
     qpat_assum `local_ptrs_reserved cenv saL` (irule_at Any) >> simp[]) >>
  fs[]
QED

(* The index assignment and dynamic check preserve any operand whose
   register is outside the emitted writes. *)
Theorem array_entry_control[local]:
  ~s.vs_halted /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j0 JMP [Label entry] []) /\
  lookup_block entry func.fn_blocks = SOME eb /\
  eb.bb_instructions = ([mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (if dyn then
       [mk_inst (eid+1) GT [len_op;Lit (n2w cap)] [bad];
        mk_inst (eid+2) ISZERO [Var bad] [good];
        mk_inst (eid+3) ASSERT [Var good] []] else [])) ++
    [mk_inst j1 JMP [Label cond] []] /\
  eval_operand len_op s = SOME (n2w len) /\ op_prov G len_op = NONE /\
  op_taint tn len_op = {} /\ len <= cap /\ cap < dimword (:256) /\
  (!x. len_op = Var x ==> x NOTIN (if dyn then {idx;bad;good} else {idx})) /\
  (dyn ==> ALL_DISTINCT [idx;bad;good] /\
           ((?x. len_op = Var x) \/ (?w. len_op = Lit w))) /\
  (!x. x IN (if dyn then {idx;bad;good} else {idx}) ==>
       not_local_ptr cenv em.scopes x) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    lookup_var idx t = SOME 0w /\ FLOOKUP G' idx = NONE /\
    op_taint tn' (Var idx) = {} /\
    (!x. x NOTIN (if dyn then {idx;bad;good} else {idx}) ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    (!H. stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx em s ==>
         stmt_state_rel H ctx func cenv cx em t)
Proof
  strip_tac >>
  drule_all_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) for_nonslot_entry_control >>
  qexistsl [`t`,`G'`,`tn'`] >>
  `!H. stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx em s ==>
         stmt_state_rel H ctx func cenv cx em t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     Cases_on `dyn` >> fs[stmt_state_rel_jump_to] >> rpt strip_tac >>
     rpt (irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to])) >>
  qpat_x_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` mp_tac >>
  qpat_x_assum `t = jump_to _ _` mp_tac >>
  `FLOOKUP G' idx = NONE` by
    (qpat_assum `op_prov G' (Var idx) = NONE` (mp_tac o REWRITE_RULE[op_prov_def]) >> simp[]) >>
  Cases_on `dyn` >> simp[jump_to_def, update_var_def]
QED

Theorem for_array_header_install_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  fn_inst_ids_distinct func /\ capacity < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  eval_operand (vv_operand vv) u = SOME bw /\ op_taint tu (vv_operand vv) = {} /\
  eval_operand len_op u = SOME (n2w (LENGTH vs)) /\
  op_prov Gu len_op = NONE /\ op_taint tu len_op = {} /\
  ~u.vs_halted /\ u.vs_current_bb = saL.cs_current_bb /\
  u.vs_inst_idx = LENGTH saL.cs_current_insts /\
  storage_trace_domain cx st0 em.storage_trace /\
  body_const_cells_agree_mods mods cx env em /\
  expr_sim_inv_mods mods c cx env em /\ lookup_scopes id em.scopes = NONE /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  ret_pc_ok c sa0 u /\ return_buf_frame d c sa0 u /\ return_buf_sep d c em u /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
       stmt_state_rel H ctx func c cx em u /\ immutable_frame_mods func c cx em u /\
       storage_well_formed_on cx em (FST H) /\ ghost_inv_at_mods (DF H) lo d c cx em Gu tu u) /\
  (!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q) /\
  for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 em Gu tu u ==>
  ?dw G tn t.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,G,tn)) /\
    ~t.vs_halted /\ for_array_install_frame_mods saL u Gu tu G tn t /\
    lo <= w2n dw /\
    (!aid b len. aid < aidItem /\ FLOOKUP u.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n dw) capacity b len) /\
    (!H. valid_horizon cx st0 H em.storage_trace /\ Route H vs em G tn t ==>
      for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,aidItem)
        vs (vv_operand vv,bw,len_op,idx) cond Route H vs em G tn t)
Proof
  strip_tac >>
  qpat_x_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[for_nonslot_layout_def]) >>
  qpat_assum `for_array_outer_frame_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[for_array_outer_frame_mods_def,range_outer_frame_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `ghost_inv_at_mods (DF H0) lo d c cx em Gu tu u`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  drule_all_then (qspecl_then [`tu`,`explicit`,`PG`,`Gu`]
    (qx_choosel_then [`q`,`dw`,`a`,`Ga`,`ta`,`raw`] strip_assume_tac))
    (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  rename1 `lookup_var q a = SOME dw` >>
  `q = xd` by fs[] >> qpat_x_assum `q = xd` SUBST_ALL_TAC >>
  rename1 `a = raw with vs_inst_idx := _` >>
  `saA.cs_current_bb = saL.cs_current_bb` by
    (drule compile_alloc_buffer_insts >> simp[]) >>
  `~a.vs_halted /\ a.vs_memory = u.vs_memory /\
   a.vs_data_section = u.vs_data_section /\ a.vs_labels = u.vs_labels /\
   a.vs_immutables = u.vs_immutables /\ a.vs_call_ctx = u.vs_call_ctx /\
   a.vs_accounts = u.vs_accounts /\ a.vs_transient = u.vs_transient` by
    (qpat_assum `~u.vs_halted` mp_tac >>
     qpat_assum `a with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = u`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by
    (`stmt_state_rel H0 ctx func c cx em a` by simp[] >>
     qpat_assum `stmt_state_rel H0 ctx func c cx em a`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  suspend "control"
QED

Resume for_array_header_install_mods[control]:
  qabbrev_tac `dyn = ?cap. bd = Dynamic cap` >>
  qabbrev_tac `writes = if dyn then {idx;invalid;valid} else {idx}` >>
  `!x. x IN writes ==> ~not_fresh_at saL x` by
    (qpat_assum `EVERY _ [idx;done_var;next_var]` mp_tac >>
     qpat_assum `(case bd of Fixed _ => T | Dynamic _ => _)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `dyn`, Abbr `writes`] >> metis_tac[]) >>
  `xd NOTIN writes` by
    (qpat_assum `ALL_DISTINCT [xd;idx;done_var;next_var]` mp_tac >>
     qpat_assum `(case bd of Fixed _ => T | Dynamic _ => _)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `writes`, Abbr `dyn`]) >>
  `!x. x IN writes ==> not_local_ptr c em.scopes x` by
    (rpt strip_tac >> irule fresh_not_local_ptr >> qexists `saL` >> simp[]) >>
  `!x. len_op = Var x ==> x NOTIN writes` by
    (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
     qpat_assum `!p. vv_operand vv = Var p \/ _ ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `dyn ==> ALL_DISTINCT [idx;invalid;valid] /\
    ((?x. len_op = Var x) \/ (?w. len_op = Lit w))` by
    (qpat_assum `(case bd of Fixed _ => T | Dynamic _ => _)` mp_tac >>
     qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => compile_ptr_load _ _ _ _)
                  sbExpr = (len_op,saL)` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, Abbr `dyn`] >> strip_tac >> strip_tac >>
     Cases_on `len_op` >> simp[] >>
     metis_tac[fragFuelExprHelpersTheory.compile_ptr_load_not_label]) >>
  `for_array_install_frame_mods saL u Gu tu Ga ta a` by
    (simp[for_array_install_frame_mods_def] >> rpt strip_tac >> decide_tac) >>
  `eval_operand len_op a = SOME (n2w (LENGTH vs)) /\
   op_prov Ga len_op = NONE /\ op_taint ta len_op = {}` by
    (qpat_assum `for_array_install_frame_mods saL u Gu tu Ga ta a`
       (mp_then Any (qspec_then `len_op` mp_tac) array_install_operand) >> simp[]) >>
  suspend "execute"
QED

Resume for_array_header_install_mods[execute]:
  `?t G tn.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK t,G,tn)) /\
    t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    lookup_var idx t = SOME 0w /\ FLOOKUP G idx = NONE /\
    op_taint tn (Var idx) = {} /\
    (!x. x NOTIN writes ==> lookup_var x t = lookup_var x a /\
         FLOOKUP G x = FLOOKUP Ga x /\ op_taint tn (Var x) = op_taint ta (Var x)) /\
    tn.t_mem = ta.t_mem /\ tn.t_stor = ta.t_stor /\
    tn.t_trans = ta.t_trans /\ tn.t_imm = ta.t_imm /\
    t.vs_memory = a.vs_memory /\ t.vs_labels = a.vs_labels /\
    t.vs_data_section = a.vs_data_section /\ t.vs_call_ctx = a.vs_call_ctx /\
    t.vs_accounts = a.vs_accounts /\ t.vs_transient = a.vs_transient /\
    t.vs_immutables = a.vs_immutables /\ t.vs_allocas = a.vs_allocas /\
    t.vs_alloca_next = a.vs_alloca_next /\
    (!H. stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func c cx em a ==>
         stmt_state_rel H ctx func c cx em t)` by
    (qpat_assum `Abbrev (writes = _)`
       (pure_once_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     irule array_entry_control >>
     conj_tac >- fs[Abbr `writes`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- simp[] >>
     qrefinel [`<|bb_label := saL.cs_current_bb;
                   bb_instructions := saA.cs_current_insts ++
                     [mk_inst saA.cs_next_id JMP [Label entry] []]|>`,
               `bound_length bd`, `_`, `saA.cs_next_id + 1`, `entry`,
               `saA.cs_next_id`, `sa.cs_next_id - 3`, `LENGTH vs`, `len_op`] >>
     qpat_assum `lookup_block entry func.fn_blocks = SOME _` (irule_at Any) >>
     Cases_on `bd` >> fs[Abbr `dyn`, Abbr `writes`, bound_length_def,
                         get_instruction_def, EL_LENGTH_APPEND_0, ADD_ASSOC]) >>
  suspend "exit_frame"
QED

Resume for_array_header_install_mods[exit_frame]:
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
  `exec_alloca (mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd])
      u (n2w capacity : bytes32) = OK raw` by
    (`saA.cs_current_insts = saL.cs_current_insts ++
           [mk_inst saL.cs_next_id ALLOCA [Lit (n2w capacity)] [xd]]` by
       (drule compile_alloc_buffer_insts >> simp[]) >>
     qpat_x_assum `run_inst_seq _ u = OK raw` mp_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def,
          step_inst_base_def, mk_inst_def, AllCaseEqs()]) >>
  `raw.vs_memory = u.vs_memory /\ raw.vs_allocas = a.vs_allocas /\
   raw.vs_alloca_next = a.vs_alloca_next /\
   (!x. lookup_var x raw = lookup_var x a)` by
    (qpat_assum `a.vs_memory = u.vs_memory` mp_tac >>
     qpat_assum `a = raw with vs_inst_idx := _` SUBST1_TAC >> simp[lookup_var_def]) >>
  qpat_x_assum `a = raw with vs_inst_idx := _` kall_tac >>
  `!x. not_fresh_at saL x ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP G x = FLOOKUP Gu x /\
      op_taint tn (Var x) = op_taint tu (Var x)` by
    (rpt strip_tac >> `x NOTIN writes` by
       (CCONTR_TAC >> gvs[] >> qpat_assum `!x. x IN writes ==> _` (drule_then mp_tac) >> simp[]) >>
     simp[]) >>
  `for_array_install_frame_mods saL u Gu tu G tn t` by
    (simp[for_array_install_frame_mods_def] >> first_assum ACCEPT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,G,tn)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Ga`,`a`,`ta`] >> simp[]) >>
  `allocas_from lo t` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = a.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo a` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo a` (irule o REWRITE_RULE[allocas_from_def]) >>
     qexistsl [`saL.cs_next_id`,`capacity`] >> simp[]) >>
  qexistsl [`dw`,`G`,`tn`,`t`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `aidItem = saL.cs_next_id` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> _`
    (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
  suspend "header"
QED

Resume for_array_header_install_mods[header]:
  `ci_mono sbExpr saL` by
    (qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => _) sbExpr = _` mp_tac >>
     Cases_on `bd` >> simp[NoAsms, comp_return_def, ci_mono_def, cs_extends_refl] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[ci_mono_compile_ptr_load, ci_mono_def, pairTheory.SND]) >>
  `sa0.cs_next_id <= saL.cs_next_id /\ sbExpr.cs_next_id <= saL.cs_next_id /\
   sa0.cs_next_var <= saL.cs_next_var` by fs[ci_mono_def] >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at saL x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa0` >> simp[]) >>
  `(!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x) /\
   (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x)` by
    fs[ret_pc_ok_def] >>
  `!x. not_fresh_at sa0 x ==> lookup_var x t = lookup_var x u /\
       FLOOKUP G x = FLOOKUP Gu x /\ op_taint tn (Var x) = op_taint tu (Var x)` by simp[] >>
  `ret_pc_ok c sa0 t` by
    (qpat_assum `ret_pc_ok c sa0 u` (mp_then Any irule ret_pc_ok_frame) >> simp[]) >>
  `return_buf_frame d c sa0 t` by
    (qpat_assum `return_buf_frame d c sa0 u` (mp_then Any irule return_buf_frame_frame) >> simp[] >> decide_tac) >>
  `stmt_state_rel H ctx func c cx em t` by
    (`stmt_state_rel H ctx func c cx em a` by simp[] >>
     qpat_assum `!h. stmt_state_rel h ctx func c cx em a ==> stmt_state_rel h ctx func c cx em t`
       (qspec_then `H` (fn th => drule_then ACCEPT_TAC th))) >>
  `local_ptrs_rel func c em.scopes u /\ alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func c cx em u`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `immutable_frame_mods func c cx em t` by
    (irule array_install_immutable >>
     qpat_assum `exec_alloca _ u _ = OK raw` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved c saL` (irule_at Any) >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d c cx em G tn t` by
    (irule array_install_ghost >>
     qpat_assum `for_array_install_frame_mods saL u Gu tu G tn t` (irule_at Any) >>
     qpat_assum `local_ptrs_rel func c em.scopes u` (irule_at Any) >> simp[]) >>
  `return_buf_sep d c em t` by suspend "return_sep" >>
  suspend "memory_frames"
QED

Resume for_array_header_install_mods[return_sep]:
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
  reverse conj_tac >-
    (qpat_assum `stmt_state_rel H ctx func c cx em u` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved c saL` (irule_at Any) >> simp[]) >>
  rpt strip_tac >> rename1 `d = SOME (bw',capacity')` >>
  `allocas_from (w2n bw' + capacity') u /\ w2n bw' + capacity' <= u.vs_alloca_next` by
    fs[bodySimFullTheory.return_buf_sep_def,return_buf_frame_def] >>
  `allocas_from (w2n bw' + capacity') raw` by
    (qpat_assum `exec_alloca _ u _ = OK raw`
       (mp_then Any irule decoderAllocationBoundsPtrTheory.exec_alloca_preserves_allocas_from) >>
     simp[]) >>
  qpat_x_assum `allocas_from (w2n bw' + capacity') raw` mp_tac >>
  simp[allocas_from_def]
QED

Resume for_array_header_install_mods[memory_frames]:
  `alloca_frame c em saL u c em t` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel H ctx func c cx em u` (irule_at Any) >> simp[]) >>
  `alloca_frame c em sbExpr u c em t` by
    (pure_rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_frame c em saL u c em t`
       (irule o REWRITE_RULE[alloca_frame_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[] >> decide_tac) >>
  `alloca_frame c es0 sa0 s0 c em t` by
    (irule alloca_frame_trans >>
     qpat_assum `alloca_frame c em saL u c em t` (irule_at Any) >> simp[]) >>
  `!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
     b <= i /\ i < b + len /\ i IN tn.t_mem ==> i IN tu.t_mem` by
    (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC array_install_row_taint) >>
  `for_array_capture_frame_mods c (em,sbExpr,saL,u,tu) em tn t` by
    (simp[for_array_capture_frame_mods_def] >> rpt strip_tac >>
     qpat_assum `!aid b len i. _ ==> i IN tu.t_mem` irule >>
     qpat_assum `FLOOKUP u.vs_allocas aid = SOME (b,sz)` (irule_at Any) >> simp[]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `a` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H ctx func c cx em t`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 em G tn t` by suspend "outer" >>
  suspend "initial"
QED

Resume for_array_header_install_mods[outer]:
  qpat_x_assum `tn.t_mem = ta.t_mem` kall_tac >>
  simp[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (off,z)` by simp[] >>
  `i IN tu.t_mem` by
    (qpat_assum `!aid b len i. _ ==> i IN tu.t_mem` irule >>
     qpat_assum `FLOOKUP u.vs_allocas aid = SOME (off,z)` (irule_at Any) >> simp[]) >>
  qpat_assum `!aid off z i. _ ==> i IN tn0.t_mem` irule >>
  qpat_assum `FLOOKUP s0.vs_allocas aid = SOME (off,z)` (irule_at Any) >> simp[] >>
  first_assum ACCEPT_TAC
QED

Resume for_array_header_install_mods[initial]:
  `for_array_item_mods c sa0 sbExpr (xd,dw,capacity,aidItem) em G tn t` by suspend "item" >>
  `!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q` by
    suspend "headroom" >>
  `eval_operand len_op t = SOME (n2w (LENGTH vs)) /\ op_prov G len_op = NONE /\
   op_taint tn len_op = {}` by
    (qpat_assum `for_array_install_frame_mods saL u Gu tu G tn t`
       (mp_then Any (qspec_then `len_op` mp_tac) array_install_operand) >> simp[]) >>
  `eval_operand (vv_operand vv) t = SOME bw /\ op_taint tn (vv_operand vv) = {}` by
    (qpat_assum `for_array_install_frame_mods saL u Gu tu G tn t`
       (mp_then Any (qspec_then `vv_operand vv` mp_tac) array_install_operand) >> simp[]) >>
  `LENGTH vs < dimword (:256) /\ lo <= t.vs_alloca_next` by decide_tac >>
  simp[for_array_header_mods_def, for_array_header_init_mods] >> first_assum ACCEPT_TAC
QED

Resume for_array_header_install_mods[item]:
  `ptr_covers G tn xd t capacity` by
    (qpat_assum `ptr_covers Ga ta xd a capacity` (mp_then Any irule ptr_covers_lookup_frame) >> simp[]) >>
  `!name b len. local_region c em.scopes t name b len <=>
                local_region c em.scopes a name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at saL p` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
  simp[for_array_item_mods_def] >>
  rpt strip_tac >>
  qpat_assum `!name b len. local_region c em.scopes a name b len ==> _`
    (drule_then (mp_tac o REWRITE_RULE[loweringStateRelDefsTheory.regions_disjoint_def])) >> simp[]
QED

Resume for_array_header_install_mods[headroom]:
  `?bb ins. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME ins /\ ins.inst_opcode <> PHI` by
    (qpat_assum `lookup_block cond func.fn_blocks = SOME _`
       (fn th => simp[th,get_instruction_def,mk_inst_def])) >>
  `!i. active_inst func i t ==> frag_reachable ctx func u func i t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK t,G,tn)`
       (qspec_then `DF H`
          (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
     drule ifexp_ptr_path_reachable >> disch_then (qspec_then `t` mp_tac) >> simp[] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `frag_reachable ctx func u fn inst q` by
    (drule contextRawReachableTheory.frag_reachable_trans >> metis_tac[]) >>
  qpat_assum `!fn inst q. frag_reachable ctx func u fn inst q ==> _`
    (drule_then ACCEPT_TAC)
QED

Finalise for_array_header_install_mods
