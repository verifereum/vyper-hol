(* Land the raw linked body result before converting it to a loop boolean. *)
Theory bodyForArrayRawLandingMods
Ancestors
  bodyForArrayControlFrameMods bodyForArrayHeaderMods bodyForRangeHeaderMods
  bodyFullForRange bodyFullPostsMods bodyFullShared bodyFullShadowBodyInv
  bodyMemoryDefs allocaHistory stmtSimDefs stmtSimProps exprLoweringProps
  loweringPosts loweringStateRelDefs loweringShapeDefs ptrDiscipline bodyPtrDefs
  fragGasOriginPtr fragExec venomState venomInst finite_map words list
  bodyFullPredsMods exprSimHypsDefs vyperStorageTrace vyperStorageFootprint
  typedMemoryCopy bodySimFull bodyInvSplit bodyFullIfExpReach arithmetic compileEnv

Theorem array_landing_outer_jump[local]:
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn t ==>
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn (jump_to lbl t)
Proof
  simp[for_array_outer_frame_mods_def, range_outer_frame_mods_def] >> strip_tac >>
  `alloca_history func (jump_to lbl t)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `t` >> simp[]) >>
  `alloca_frame c es0 sa s0 c ee (jump_to lbl t)` by
    (irule alloca_frame_same_state >> qexists_tac `t` >> simp[jump_to_def]) >>
  `allocas_below_fmp (jump_to lbl t) = allocas_below_fmp t` by
    simp[jump_to_def, allocas_below_fmp_def] >>
  simp[] >> simp[jump_to_def, lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem array_landing_capture_jump[local]:
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ee tn t ==>
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ee tn (jump_to lbl t)
Proof
  simp[for_array_capture_frame_mods_def] >> strip_tac >>
  conj_tac >- (irule alloca_frame_same_state >> qexists_tac `t` >> simp[jump_to_def]) >>
  fs[jump_to_def, lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem array_landing_item_jump[local]:
  for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee G tn (jump_to lbl t) <=>
  for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee G tn t
Proof
  simp[for_array_item_mods_def, ptr_covers_def, local_region_def, jump_to_def, lookup_var_def]
QED

Theorem array_landing_immutable_jump[local]:
  immutable_frame_mods func c cx ee (jump_to lbl t) <=> immutable_frame_mods func c cx ee t
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_def, immutable_alloca_sep_def, jump_to_def, local_region_def, lookup_var_def]
QED

Theorem array_landing_ghost_jump[local]:
  ghost_inv_at_mods D lo d c cx ee G tn (jump_to lbl t) <=>
  ghost_inv_at_mods D lo d c cx ee G tn t
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem array_landing_increment_run[local]:
  s.vs_current_bb = incr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var idx s = SOME w /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr; bb_instructions :=
       [mk_inst jid ADD [Var idx;Lit 1w] [next_var];
        mk_inst (jid + 1) ASSIGN [Var next_var] [idx];
        mk_inst (jid + 2) JMP [Label cond] []]|> ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to cond (update_var idx (w+1w) (update_var next_var (w+1w) s))),
     DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx}),
     tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{}))
Proof
  strip_tac >> irule range_full_increment_path >> simp[op_prov_def] >>
  qmatch_asmsub_abbrev_tac `lookup_block incr func.fn_blocks = SOME bb` >>
  qexistsl_tac [`jid`,`jid+1`,`jid+2`] >> simp[Abbr `bb`, get_instruction_def]
QED

(* The back-edge writes only idx and next_var. In particular the saved
   base may carry provenance: preservation does not require it to be NONE. *)
Theorem array_landing_increment_header[local]:
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\ rs = DROP (SUC k) vs /\
  s.vs_current_bb = incr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand base_op s = SOME bw /\ op_taint tn base_op = {} /\
  eval_operand len_op s = SOME (n2w (LENGTH vs)) /\ op_prov G len_op = NONE /\
  op_taint tn len_op = {} /\
  (!q. base_op = Var q \/ len_op = Var q ==> not_fresh_at saLen q) /\
  ~not_fresh_at saLen idx /\ ~not_fresh_at saLen next_var /\ xd <> idx /\ xd <> next_var /\
  lookup_block incr func.fn_blocks = SOME
    <|bb_label := incr; bb_instructions :=
       [mk_inst jid ADD [Var idx;Lit 1w] [next_var];
        mk_inst (jid + 1) ASSIGN [Var next_var] [idx];
        mk_inst (jid + 2) JMP [Label cond] []]|> /\
  sa.cs_next_var <= saLen.cs_next_var /\ local_ptrs_reserved c sa /\
  (!q sz. c.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  (!q sz. c.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
  for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee G tn s /\
  stmt_state_rel H ctx func c cx ee s /\ immutable_frame_mods func c cx ee s /\
  valid_horizon cx st0 H ee.storage_trace /\ storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok c sa s /\ return_buf_frame d c sa s /\ return_buf_sep d c ee s /\
  ghost_inv_at_mods (DF H) lo d c cx ee G tn s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn s /\
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ee tn s /\
  body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods c cx env ee /\
  lookup_scopes id ee.scopes = NONE /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst q. frag_reachable ctx func s fn inst q ==> dalloca_fmp_headroom inst q) ==>
  let w = n2w k + 1w;
      f = jump_to cond (update_var idx w (update_var next_var w s));
      Gf = DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx});
      tf = tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{})
  in
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK f,Gf,tf) /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) (xd,dw,cap,aid)
      vs (base_op,bw,len_op,idx) cond (\H rs ee G tn t. T) H rs ee Gf tf f
Proof
  strip_tac >> simp[LET_THM, Excl "DRESTRICT_DRESTRICT"] >>
  qabbrev_tac `w = n2w k + (1w:bytes32)` >>
  qabbrev_tac `f = jump_to cond (update_var idx w (update_var next_var w s))` >>
  qabbrev_tac `Gf = DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx})` >>
  qabbrev_tac `tf = tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{})` >>
  conj_asm1_tac
  >- (simp[Abbr `w`, Abbr `f`, Abbr `Gf`, Abbr `tf`, Excl "DRESTRICT_DRESTRICT"] >>
      irule array_landing_increment_run >> simp[] >>
      conj_tac >- (qexists_tac `jid` >> simp[]) >>
      fs[for_array_outer_frame_mods_def, range_outer_frame_mods_def]) >>
  `!fn inst q. frag_reachable ctx func f fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK f,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `!fn inst q. frag_reachable ctx func s fn inst q ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  suspend "fields"
QED

Resume array_landing_increment_header[fields]:
  `!op. (!q. op = Var q ==> not_fresh_at saLen q) ==>
       eval_operand op f = eval_operand op s /\ op_prov Gf op = op_prov G op /\
       op_taint tf op = op_taint tn op` by
    (Cases >> simp[Abbr `f`, Abbr `Gf`, Abbr `tf`, eval_operand_def, op_prov_def, op_taint_def,
                  jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     rpt strip_tac >> `s' <> idx /\ s' <> next_var` by (conj_tac >> CCONTR_TAC >> gvs[]) >> simp[]) >>
  `eval_operand len_op f = SOME (n2w (LENGTH vs)) /\ op_prov Gf len_op = NONE /\
   op_taint tf len_op = {} /\ eval_operand base_op f = SOME bw /\ op_taint tf base_op = {}` by
    (qpat_assum `!op. _ ==> eval_operand op f = _ /\ _`
       (fn th => map_every (fn tm => qspec_then tm mp_tac th) [`base_op`,`len_op`]) >> simp[]) >>
  `for_array_index_mods vs idx rs f /\ FLOOKUP Gf idx = NONE /\ op_taint tf (Var idx) = {}` by
    (simp[for_array_index_mods_def, Abbr `f`, Abbr `w`, Abbr `Gf`, Abbr `tf`, jump_to_def,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def, FLOOKUP_DRESTRICT] >>
     qexists_tac `SUC k` >> simp[ADD1, GSYM word_add_n2w]) >>
  rename1 `for_array_item_mods cenv sa saExpr (xd,dw,capacity,aidItem) ee G tn s` >>
  rename1 `Abbrev (f = jump_to cond (update_var x w (update_var y w s)))` >>
  (* Name the written registers explicitly: the symmetric freshness
     premises by themselves do not distinguish the two writes. *)
  mp_tac (Q.INST [`vx` |-> `w`, `vy` |-> `w`, `lbl` |-> `cond`, `D` |-> `DF H`]
          (INST_TYPE [alpha |-> ``:256``] for_array_control_scalar_frame_mods)) >>
  (impl_tac >- simp[]) >>
  simp[LET_THM, Excl "DRESTRICT_DRESTRICT", for_array_header_mods_def,
       Abbr `f`, Abbr `Gf`, Abbr `tf`] >>
  strip_tac >> conj_tac
  >- (qpat_assum `rs = _` (pure_once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise array_landing_increment_header

(* The witness triple depends on the raw machine landing, not on H.
   Route is supplied at the actual next header, with its physical frame. *)
Theorem for_array_raw_landing_mods:
  stmt_lands (InLoop exit incr) sbBody raw t /\ ~t.vs_halted /\
  (raw = INL () ==> ~block_is_terminated sbBody) /\
  (~block_is_terminated sbBody ==>
      sj.cs_blocks = sbBody.cs_blocks /\ sj.cs_current_bb = sbBody.cs_current_bb /\
      sj.cs_current_insts = sbBody.cs_current_insts ++
        [mk_inst sbBody.cs_next_id JMP [Label incr] []] /\ fn_has_code sbBody sj func) /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel H ctx func c cx ee t /\ immutable_frame_mods func c cx ee t /\
  valid_horizon cx st0 H ee.storage_trace /\ storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c sa t /\
  return_buf_sep d c ee t /\ ghost_inv_at_mods (DF H) lo d c cx ee G tn t /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee G tn t /\
  allocas_from lo t /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q) /\
  (raw <> INR BreakException ==>
    k < LENGTH vs /\ LENGTH vs < dimword (:256) /\ rs = DROP (SUC k) vs /\
    lookup_var idx t = SOME (n2w k) /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    eval_operand base_op t = SOME bw /\ op_taint tn base_op = {} /\
    eval_operand len_op t = SOME (n2w (LENGTH vs)) /\ op_prov G len_op = NONE /\
    op_taint tn len_op = {} /\
    (!q. base_op = Var q \/ len_op = Var q ==> not_fresh_at saLen q) /\
    ~not_fresh_at saLen idx /\ ~not_fresh_at saLen next_var /\ xd <> idx /\ xd <> next_var /\
    lookup_block incr func.fn_blocks = SOME
      <|bb_label := incr; bb_instructions :=
         [mk_inst sj.cs_next_id ADD [Var idx;Lit 1w] [next_var];
          mk_inst (sj.cs_next_id + 1) ASSIGN [Var next_var] [idx];
          mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    sa.cs_next_var <= saLen.cs_next_var /\ local_ptrs_reserved c sa /\
    (!q sz. c.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
    (!q sz. c.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa q) /\
    for_array_item_mods c sa saExpr (xd,dw,cap,aid) ee G tn t /\
    for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ee tn t /\
    ret_pc_ok c sa t /\ lo <= t.vs_alloca_next /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods c cx env ee /\
    lookup_scopes id ee.scopes = NONE /\ storage_trace_domain cx st0 ee.storage_trace) /\
  (!f Gf tf. for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) (xd,dw,cap,aid)
      vs (base_op,bw,len_op,idx) cond (\H rs ee G tn t. T) H rs ee Gf tf f /\
      (!q. not_fresh_at saLen q ==>
        FLOOKUP Gf q = FLOOKUP G q /\ op_taint tf (Var q) = op_taint tn (Var q)) ==>
    Route H rs ee Gf tf f) ==>
  let land = if raw = INL () then jump_to incr t else t;
      w = n2w k + 1w;
      f = jump_to cond (update_var idx w (update_var next_var w land));
      Gf = DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx});
      tf = tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{})
  in
    if raw = INR BreakException then
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK t,G,tn) /\
      for_array_done_mods DF lo d ctx func c cx lctx sa sb es0 s0 G0 tn0 H ee G tn t
    else
      (raw = INL () \/ raw = INR ContinueException) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK f,Gf,tf) /\
      for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) (xd,dw,cap,aid)
        vs (base_op,bw,len_op,idx) cond Route H rs ee Gf tf f
Proof
  strip_tac >> simp[LET_THM, Excl "DRESTRICT_DRESTRICT"] >>
  Cases_on `raw = INR BreakException`
  >- suspend "break" >>
  `raw <> INL () ==> raw = INR ContinueException` by
    (strip_tac >> qpat_assum `stmt_lands _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def]) >> gvs[]) >>
  qpat_x_assum `raw <> INR BreakException ==> _` (drule_then strip_assume_tac) >>
  qabbrev_tac `land = if raw = INL () then jump_to incr t else t` >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK land,G,tn) /\
   land.vs_inst_idx = 0 /\ land.vs_current_bb = incr` by suspend "fallthrough" >>
  `!fn inst q. frag_reachable ctx func land fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK land,_,_)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `!fn inst q. frag_reachable ctx func t fn inst q ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  suspend "continue"
QED

Resume for_array_raw_landing_mods[break]:
  `return_buf_frame d c sb t` by
    (irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ sa _`)) >> simp[]) >>
  gvs[for_array_done_mods_def, stmt_lands_def, block_is_terminated_def,
      cenv_top_ext_refl, gas_origin_ptr_path_rules]
QED

Resume for_array_raw_landing_mods[fallthrough]:
  markerLib.RESUME_TAC >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
     fs[for_array_outer_frame_mods_def, range_outer_frame_mods_def] >>
  simp[Abbr `land`, NoAsms] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) []
      (OK (if raw = INL () then jump_to incr t else t),G,tn) /\
    (if raw = INL () then jump_to incr t else t).vs_inst_idx = 0 /\
    (raw = INR BreakException ==> t.vs_current_bb = exit) /\
    (raw <> INR BreakException ==> (if raw = INL () then jump_to incr t else t).vs_current_bb = incr)` by
      (irule range_full_body_lands_path >> simp[] >>
       conj_tac >- (Cases_on `raw = INL ()` >> simp[]) >>
       qexistsl_tac [`sbBody`,`sj`] >> simp[]) >>
  simp[]
QED

Resume for_array_raw_landing_mods[continue]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `w = n2w k + (1w:bytes32)` >>
  qabbrev_tac `f = jump_to cond (update_var idx w (update_var next_var w land))` >>
  qabbrev_tac `Gf = DRESTRICT (DRESTRICT G (COMPL {next_var})) (COMPL {idx})` >>
  qabbrev_tac `tf = tn with t_var := tn.t_var |+ (next_var,{}) |+ (idx,{})` >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (land,G,tn) [] (OK f,Gf,tf) /\
   for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) (xd,dw,cap,aid)
      vs (base_op,bw,len_op,idx) cond (\H rs ee G tn t. T) H rs ee Gf tf f` by suspend "backedge" >>
  simp[] >>
  conj_tac >- (Cases_on `raw = INL ()` >> simp[]) >>
  conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ (t,G,tn) [] (OK land,G,tn)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >> simp[]) >>
  `Route H rs ee Gf tf f` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `q <> idx /\ q <> next_var` by (conj_tac >> CCONTR_TAC >> gvs[]) >>
     simp[Abbr `Gf`, Abbr `tf`, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  qpat_assum `rs = _` (pure_once_rewrite_tac o single o SYM) >>
  qhdtm_x_assum `for_array_header_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
  simp[for_array_header_mods_def] >> first_assum ACCEPT_TAC
QED

Resume for_array_raw_landing_mods[backedge]:
  markerLib.RESUME_TAC >>
  simp[Abbr `w`, Abbr `f`, Abbr `Gf`, Abbr `tf`, Excl "DRESTRICT_DRESTRICT"] >>
  irule (SRULE [LET_THM, Excl "DRESTRICT_DRESTRICT"] array_landing_increment_header) >>
  `!x. lookup_var x land = lookup_var x t` by
    (Cases_on `raw = INL ()` >> simp[Abbr `land`, jump_to_def, lookup_var_def]) >>
  simp[] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  `allocas_from lo (jump_to incr t) /\ (jump_to incr t).vs_alloca_next = t.vs_alloca_next /\
   (jump_to incr t).vs_halted = t.vs_halted` by
    (qpat_assum `allocas_from lo t` mp_tac >> simp[NoAsms, allocas_from_def, jump_to_def]) >>
  Cases_on `raw = INL ()` >>
  simp[Abbr `land`, stmt_state_rel_jump_to, array_landing_immutable_jump,
       ret_pc_ok_jump_to, return_buf_frame_jump_to, return_buf_sep_jump,
       array_landing_ghost_jump, array_landing_outer_jump, array_landing_capture_jump,
       array_landing_item_jump, typed_copy_eval_operand_jump] >>
  qexists_tac `sj.cs_next_id` >> simp[]
QED

Finalise for_array_raw_landing_mods
