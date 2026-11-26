(* The two read-only instructions following a linked RawCreate snapshot. *)
Theory bodyCreateRawHeaderMods
Ancestors
  bodyFullCreateHeld bodyForRangeScalarFrameMods bodyFullPostsMods
  bodyInvSplit exprLoweringProps compileEnv bodyPtrDefs loweringPosts
  venomState venomMemDefs ptrDiscipline gasShadow
  vyperStorageFootprint fragGasOriginPtr stateFrame loweringStateRelDefs
  assignTuplePtrLoadStep bodyFullIfExpReach bodyFullPathHistory bodyMemoryDefs
  exprSimWordArgs wordArgsPtr reasonCopySourcePtr memoryReadProps
  entryDecodeStructure stateRelProj
Libs horizonTypeLib

Theorem raw_create_header_frames[local]:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ci_mono sa sm /\ wb_frame cenv es em sa s m /\ wb_frame cenv em ee sm m t /\
  ghost_kept_at lo cenv es sa G tn s Gm tm /\
  ghost_kept_at lo cenv em sm Gm tm m G1 tn1 ==>
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by
    fs[wb_frame_def,locals_kept_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  conj_asm1_tac
  >- (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
      qpat_assum `stmt_state_rel _ _ _ _ _ es s` (irule_at Any) >>
      qpat_assum `wb_frame cenv em ee sm m t` (irule_at Any) >> simp[]) >>
  irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
  qpat_assum `stmt_state_rel H _ _ _ _ es s` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv em sm Gm tm m G1 tn1` (irule_at Any) >>
  qpat_assum `wb_frame cenv es em sa s m` (irule_at Any) >> simp[]
QED

Theorem raw_create_header_lands_mods:
  contract_inv mods exps ctx cenv cx /\ MEM func ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ ci_mono sa a /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!fn i y. frag_reachable ctx func s fn i y ==> dalloca_fmp_headroom i y) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1)) /\
  wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  compile_create_snapshot cenv vv (lowered_value_type cenv code) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap;Lit 32w] c = (data,sb) /\
  fn_has_code b c func /\ fn_has_code c sb func /\
  LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code) /\
  32 + LENGTH bs <= cap /\
  snap = Var owner /\ MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
  site.inst_id = a.cs_next_id /\ site.inst_outputs = [owner] /\
  not_local_ptr cenv ee.scopes owner /\ not_fresh_at b owner /\
  FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
  eval_operand snap u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
  pbase + cap < dimword (:256) /\ pbase + cap <= u.vs_alloca_next /\
  mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase + 32) (LENGTH bs) u = bs /\
  (!i. pbase <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tu.t_mem) /\
  wb_frame cenv ee ee a t u /\ ghost_kept_at lo cenv ee a G1 tn1 t Gu tu /\
  alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\
  return_buf_frame d cenv b u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gu,tu)) ==>
  ?z Gz tz src.
    LENGTH bs <= bytelike_type_bound (lowered_value_type cenv code) /\
    wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    s.vs_alloca_next <= z.vs_alloca_next /\ alloca_history func z /\ return_buf_frame d cenv sb z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn i y. frag_reachable ctx func z fn i y ==> dalloca_fmp_headroom i y) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
      immutable_frame_mods func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK z,Gz,tz)) /\
    MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\ site.inst_outputs = [owner] /\
    not_local_ptr cenv ee.scopes owner /\ site.inst_id < sb.cs_next_id /\
    FLOOKUP z.vs_allocas site.inst_id = SOME (pbase,cap) /\
    pbase + cap <= z.vs_alloca_next /\ pbase + cap < dimword (:256) /\ 32 + LENGTH bs <= cap /\
    data = Var src /\ not_fresh_at sb src /\ lookup_var src z = SOME (n2w (pbase + 32)) /\
    ptr_covers Gz tz src z (LENGTH bs) /\ op_taint tz (Var src) = {} /\
    (!x. len = Var x ==> not_fresh_at sb x) /\ (!l. len <> Label l) /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE /\
    read_memory (pbase + 32) (LENGTH bs) z = bs /\
    (!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tz.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `snap = Var owner` SUBST_ALL_TAC >>
  `ptr_covers Gu tu owner u (32 + LENGTH bs)` by
    (irule ptr_covers_mono >> qexists `cap` >> simp[]) >>
  `pbase + 32 < dimword (:256) /\ pbase + 32 + LENGTH bs <= u.vs_alloca_next` by
    (qpat_assum `pbase + cap < dimword (:256)` mp_tac >>
     qpat_assum `pbase + cap <= u.vs_alloca_next` mp_tac >>
     qpat_assum `32 + LENGTH bs <= cap` mp_tac >> numLib.ARITH_TAC) >>
  `mem_bytes_at (pbase + 32) (LENGTH bs) u.vs_memory = bs` by
    (qpat_assum `read_memory (pbase + 32) (LENGTH bs) u = bs`
       (ACCEPT_TAC o REWRITE_RULE [read_memory_eq_mem_bytes_at])) >>
  drule_all blueprint_raw_header_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`l`,`src`,`z`,`Gz`,`tz`] strip_assume_tac)) >>
  suspend "readonly"
QED

Resume raw_create_header_lands_mods[readonly]:
  qpat_assum `z with <|vs_vars := _; vs_inst_idx := _|> = u`
    (mp_tac o Q.AP_TERM `\r. (r.vs_memory,r.vs_data_section,r.vs_allocas,r.vs_alloca_next,
        r.vs_fmp,r.vs_initial_fmp,r.vs_call_ctx,r.vs_accounts,
        r.vs_transient,r.vs_immutables,r.vs_halted)`) >> simp[] >> strip_tac >>
  `state_frame z = state_frame (u with vs_inst_idx := z.vs_inst_idx)` by
    (qpat_assum `z with <|vs_vars := _; vs_inst_idx := _|> = u`
      (mp_tac o Q.AP_TERM `\r:venom_state. r with <|vs_vars := FEMPTY; vs_inst_idx := z.vs_inst_idx|>`) >>
     simp[state_frame_def,venom_state_component_equality]) >>
  qpat_assum `tz with t_var := _ = tu`
    (mp_tac o Q.AP_TERM `\r. (r.t_mem,r.t_stor,r.t_trans,r.t_imm)`) >> simp[] >> strip_tac >>
  `ci_mono a b` by
    (qmatch_asmsub_rename_tac `compile_create_snapshot cenv vv sty a` >>
     qspecl_then [`cenv`,`vv`,`sty`,`a`] mp_tac ci_mono_compile_create_snapshot >> simp[]) >>
  `b.cs_next_id < sb.cs_next_id /\ b.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `emit_op MLOAD _ b = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >>
     qpat_assum `emit_op ADD _ c = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >> simp[]) >>
  `sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv a` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `local_ptrs_reserved cenv b` by
    (irule local_ptrs_reserved_next_var >> qexists `a` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at b x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at b x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> numLib.ARITH_TAC) >>
  suspend "paths"
QED

Resume raw_create_header_lands_mods[paths]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,Gu,tu)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
    immutable_frame_mods func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tz z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK z,Gz,tz)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >> simp[] >>
     conj_tac
     >- (irule stmt_state_rel_old_vars_frame_ptr >>
         qpat_assum `stmt_state_rel H ctx func cenv cx ee u` (irule_at Any) >>
         qpat_assum `state_frame z = _` (irule_at Any) >>
         qexists `b` >> simp[] >> rpt strip_tac >>
         qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _` (drule_then strip_assume_tac)) >>
     conj_tac
     >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`u`,`b`] >> simp[] >>
         rpt strip_tac >>
         qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _` (drule_then strip_assume_tac)) >>
     conj_tac
     >- (irule ghost_inv_at_mods_exterior_frame >>
         qexistsl [`Gu`,`ee`,`u`,`b`,`tu`] >> simp[]) >>
     qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK t,G1,tn1)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`t`,`G1`,`tn1`,`[]`,`OK z`,`Gz`,`tz`] mp_tac) >> simp[]) >>
  suspend "frames"
QED

Resume raw_create_header_lands_mods[frames]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee u` by
    (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t /\
   stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    (conj_tac
     >- (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >> simp[]) >>
  `wb_frame cenv ee ee b u z` by
    (irule wb_frame_readonly_tail >> qexistsl [`b`,`u`] >>
     simp[wb_frame_refl] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _` (drule_then strip_assume_tac)) >>
  `ghost_kept_at lo cenv ee b Gu tu u Gz tz` by simp[ghost_kept_at_def] >>
  `wb_frame cenv ee ee a t z /\ ghost_kept_at lo cenv ee a G1 tn1 t Gz tz` by
    (irule raw_create_header_frames >>
     qpat_assum `wb_frame cenv ee ee b u z` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx ee t` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee b Gu tu u Gz tz` (irule_at Any) >> simp[]) >>
  `wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz` by
    (irule raw_create_header_frames >>
     qpat_assum `wb_frame cenv ee ee a t z` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv ee a G1 tn1 t Gz tz` (irule_at Any) >> simp[]) >>
  `alloca_history func z` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] (OK z,Gz,tz)`
       (qspecl_then [`DF (storage_trace_horizon ee.storage_trace)`,`gas_explicit_sites ctx shadow_ctx`]
         (irule_at Any)) >> simp[] >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx ee u`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `return_buf_frame d cenv sb z` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv b u` (irule_at Any) >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _` (drule_then strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (simp[allocas_below_fmp_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  suspend "finish"
QED

Resume raw_create_header_lands_mods[finish]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `contract_inv mods exps ctx cenv cx` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     POP_ASSUM_LIST kall_tac >> metis_tac[body_inv_no_phi_mods]) >>
  `!fn i y. frag_reachable ctx func z fn i y ==> dalloca_fmp_headroom i y` by
    (qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks (OK z,Gz,tz)`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
         gas_origin_ptr_path_dalloca_fmp_headroom)) >> simp[] >>
     disch_then (fn th =>
       qpat_assum `!fn i y. frag_reachable ctx func s fn i y ==> _`
         (ACCEPT_TAC o MATCH_MP th))) >>
  `site.inst_id < sb.cs_next_id` by
    (simp[] >> qpat_assum `a.cs_next_id <= b.cs_next_id` mp_tac >>
     qpat_assum `b.cs_next_id < sb.cs_next_id` mp_tac >> numLib.ARITH_TAC) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by
    (simp[] >> qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     qpat_assum `t.vs_alloca_next <= u.vs_alloca_next` mp_tac >> numLib.ARITH_TAC) >>
  `op_taint tz (Var src) = {}` by
    (qpat_assum `ptr_covers Gz tz src z (LENGTH bs)` mp_tac >> simp[NoAsms,ptr_covers_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> immutable_frame_mods func cenv cx ee z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> valid_horizon cx st0 H es.storage_trace /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `data = Var src` SUBST_ALL_TAC >>
  qpat_x_assum `len = Var l` SUBST_ALL_TAC >>
  qpat_x_assum `site.inst_id = a.cs_next_id` SUBST_ALL_TAC >>
  qexistsl [`z`,`Gz`,`tz`] >>
  qpat_x_assum `eval_operand (Var src) z = SOME _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  qpat_x_assum `eval_operand (Var l) z = SOME _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  simp[eval_operand_def,read_memory_eq_mem_bytes_at] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_create_header_lands_mods
