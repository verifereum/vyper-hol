(* The caller's zero-register, positive-capacity result uses the allocation
   whose address was passed as the first argument of the reached INVOKE. *)
Theory bodySelectedCallerSretMods
Ancestors
  bodyFullPostsMods intCallFrame exprSimProps valueCopyBytes vyperTypeArgFits
  valueEncodingTyping exprSimMemDefs words venomState loweringStateRelDefs
  loweringPosts bodyPtrDefs context ptrDiscipline vyperState vyperAST
  exprLowering vyperExprEffects finite_map pred_set list

Theorem sret_post_type[local]:
  evaluate_type tenv ret = SOME rtv /\ value_has_type rtv v /\
  type_widens_to tenv ret ann /\
  pt = (if is_word_type ann \/ is_bytestring_type ann then ann else ret) /\
  evaluate_type tenv pt = SOME tv /\
  (!mem. P mem ==> val_in_memory rtv v off mem) ==>
  value_has_type tv v /\ val_footprint tv v <= type_memory_size rtv /\
  val_store_size tv v <= type_memory_size rtv /\
  (!mem. P mem ==> val_in_memory tv v off mem)
Proof
  strip_tac >>
  `val_wf rtv v` by metis_tac[value_has_type_val_wf] >>
  `val_footprint rtv v <= type_memory_size rtv` by metis_tac[val_footprint_le] >>
  `val_store_size rtv v <= type_memory_size rtv` by metis_tac[val_store_size_le] >>
  Cases_on `is_word_type ann`
  >- (`ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[]) >>
  Cases_on `is_bytestring_type ann` >> gvs[] >>
  `is_bytestring_type ret` by
    metis_tac[compileEnvTheory.arg_type_fits_bytestring_source, vyperTypeSystemTheory.type_widens_to_def] >>
  `value_has_type tv v` by metis_tac[type_widens_to_value_has_type, optionTheory.SOME_11] >>
  simp[] >> conj_tac
  >- (irule bytestring_val_footprint_le >>
      conj_tac >- (qexistsl [`ann`,`ret`,`tenv`] >> simp[]) >> simp[]) >>
  conj_tac
  >- (`val_store_size tv v = val_store_size rtv v` by
        (irule bytestring_val_store_size_eq >>
         conj_tac >- (qexistsl [`ann`,`ret`,`tenv`] >> simp[]) >> simp[]) >> simp[]) >>
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
  conj_tac >- simp[] >> qexistsl [`ret`,`ann`,`tenv`,`rtv`] >> simp[]
QED

(* From the raw return binding, only the instruction index advances. In
   particular, ownership is still over the original caller allocation. *)
Theorem sret_reached_buffer[local]:
  a = u with vs_inst_idx := SUC t.vs_inst_idx /\
  bind_outputs [] ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  eval_operand buf.buf_operand t = SOME (n2w off) /\ buf.buf_operand = Var root /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,buf.buf_size) /\
  (!n b sz. local_region ce ee.scopes t n b sz ==>
            b + sz <= off \/ off + buf.buf_size <= b) ==>
  a.vs_memory = cs.vs_memory /\ a.vs_alloca_next = t.vs_alloca_next /\
  eval_operand buf.buf_operand a = SOME (n2w off) /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (off,buf.buf_size) /\
  (!n b sz. local_region ce ee.scopes a n b sz ==>
            b + sz <= off \/ off + buf.buf_size <= b)
Proof
  strip_tac >> drule intCallFrameTheory.invoke_return_frame >> simp[] >> strip_tac >>
  `!x. lookup_var x a = lookup_var x t` by fs[lookup_var_def] >>
  `!n b sz. local_region ce ee.scopes a n b sz <=> local_region ce ee.scopes t n b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> simp[]) >>
  `eval_operand buf.buf_operand a = SOME (n2w off)` by fs[eval_operand_def, lookup_var_def] >>
  gvs[eval_operand_def, lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem sret_buffer_at_own[local]:
  eval_operand buf.buf_operand a = SOME (n2w off) /\ off < dimword (:256) /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (off,buf.buf_size) /\
  sa.cs_next_id < sb.cs_next_id /\
  (!n b sz. local_region ce ee.scopes a n b sz ==>
            b + sz <= off \/ off + buf.buf_size <= b) /\
  (!tv. evaluate_type (get_tenv cx) pt = SOME tv ==>
        value_has_type tv v /\ val_footprint tv v <= buf.buf_size) ==>
  vv_at ce cx pt sa sb ee (Value v) (LocatedValue ret (base_ptr buf)) a /\
  vv_own ce cx pt sa sb ee (Value v) (LocatedValue ret (base_ptr buf)) a
Proof
  strip_tac >>
  `!tv. evaluate_type (get_tenv cx) pt = SOME tv ==> val_wf tv v` by
    (rpt gen_tac >> strip_tac >> first_x_assum drule >>
     metis_tac[value_has_type_val_wf]) >>
  simp[vv_at_def, vv_own_def, base_ptr_def, read_result_def, return_def] >>
  conj_tac >> gen_tac >> strip_tac >> disj1_tac >>
  qexistsl [`sa.cs_next_id`,`off`,`buf.buf_size`] >> simp[] >> metis_tac[]
QED

Theorem selected_caller_sret_post_mods:
  nreturns = 0 /\ 0 < rbs /\ LENGTH outs = nreturns /\
  ce.ce_func_return_type (nsid_to_string fid) = ret /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v /\
  type_widens_to (get_tenv cx) ret ann /\
  type_memory_bytes ce ret = type_memory_size rtv /\
  vv = LocatedValue ret (base_ptr buf) /\ buf.buf_operand = Var root /\
  eval_operand buf.buf_operand t = SOME (n2w off) /\
  HD argv = (n2w off : bytes32) /\ off < dimword (:256) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (off,buf.buf_size) /\
  FLOOKUP G root = SOME (off,buf.buf_size) /\ op_taint tn (Var root) = {} /\
  sa.cs_next_id < sb.cs_next_id /\ type_memory_size rtv <= buf.buf_size /\
  w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next /\
  (!n b sz. local_region ce ee.scopes t n b sz ==>
            b + sz <= off \/ off + buf.buf_size <= b) /\
  (!mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
         val_in_memory rtv v (w2n (HD argv)) mem) /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  a = u with vs_inst_idx := SUC t.vs_inst_idx /\
  J = DRESTRICT G (COMPL (set outs)) /\
  N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) /\
  stmt_state_rel H ctx func ce cx ee a /\ immutable_frame_mods func ce cx ee a /\
  storage_well_formed_on cx ee (FST H) /\
  locals_kept ce es ee s0 a /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x a = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP a.vs_allocas aid = SOME b) /\
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n lb cap. local_region ce es.scopes s0 n lb cap ==> b + sz <= lb \/ lb + cap <= b) ==>
     mem_bytes_at b sz a.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  a.vs_current_bb = sb.cs_current_bb /\ a.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  s0.vs_alloca_next <= a.vs_alloca_next /\ ghost_inv_at_mods D lo d ce cx ee J N a /\
  ghost_kept_at lo ce es sa G0 tn0 s0 J N ==>
  let e = Call ann (IntCall fid) args drv in
  let pt = post_value_type ce e in
    vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v) vv a /\
    vv_store_bound cx pt (lowered_value_type ce e) ee (Value v) vv a /\
    a.vs_current_bb = sb.cs_current_bb /\ a.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    s0.vs_alloca_next <= a.vs_alloca_next /\ ghost_inv_at_mods D lo d ce cx ee J N a /\
    ptr_vv_ok cx pt (Value v) vv ee J N a /\
    (~is_word_type pt /\ ~is_bytestring_type pt ==>
       vv_own ce cx pt sa sb ee (Value v) vv a /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx (Value v) ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) pt = SOME rt /\
                    eval_operand (vv_operand vv) a = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside N.t_mem a.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type pt ==> ptr_buf_ok ce e op J a) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok ce e p.ptr_operand J a) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 J N
Proof
  strip_tac >>
  `(outs : string list) = []` by metis_tac[LENGTH_NIL] >>
  qpat_x_assum `outs = []` SUBST_ALL_TAC >>
  drule_all sret_reached_buffer >> strip_tac >>
  `J = G /\ N.t_mem = tc.t_mem /\ op_taint N (Var root) = {}` by
    fs[op_taint_def, DRESTRICT_UNIV] >>
  `w2n (HD (argv : bytes32 list)) = off` by simp[] >>
  `!m. mem_agree_outside N.t_mem a.vs_memory m ==> val_in_memory rtv v off m` by
    (qpat_assum `w2n (HD argv) = off` (fn addr =>
       qpat_assum `!m. mem_agree_outside tc.t_mem cs.vs_memory m ==> _`
         (mp_tac o PURE_REWRITE_RULE [addr])) >> simp[]) >>
  `off + type_memory_size rtv <= a.vs_alloca_next` by
    (qpat_assum `w2n (HD argv) + _ <= _` mp_tac >> simp[]) >>
  qpat_x_assum `a = u with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `J = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `N = tc with t_var := _` kall_tac >>
  qpat_x_assum `a.vs_memory = cs.vs_memory` kall_tac >>
  qpat_x_assum `a.vs_alloca_next = t.vs_alloca_next` kall_tac >>
  pure_rewrite_tac[LET_THM] >>
  qabbrev_tac `e = Call ann (IntCall fid) args drv` >>
  qabbrev_tac `pt = post_value_type ce e` >>
  `lowered_value_type ce e = ret` by simp[Abbr `e`, lowered_value_type_def] >>
  `pt = if is_word_type ann \/ is_bytestring_type ann then ann else ret` by
     simp[Abbr `pt`, Abbr `e`, lowered_value_type_def] >>
  `!tv. evaluate_type (get_tenv cx) pt = SOME tv ==>
    value_has_type tv v /\ val_footprint tv v <= type_memory_size rtv /\
    val_store_size tv v <= type_memory_size rtv /\
    (!m. mem_agree_outside N.t_mem a.vs_memory m ==> val_in_memory tv v off m)` by
    (gen_tac >> strip_tac >>
     irule sret_post_type >> asm_rewrite_tac[] >>
     qexistsl [`ann`,`pt`,`ret`,`get_tenv cx`] >> asm_rewrite_tac[]) >>
  `ret = pt \/ is_bytestring_type pt /\ is_bytestring_type ret` by
    (Cases_on `is_word_type ann` >> fs[] >-
      metis_tac[compileEnvTheory.type_widens_to_word] >>
     Cases_on `is_bytestring_type ann` >> fs[] >>
     metis_tac[compileEnvTheory.arg_type_fits_bytestring_source, vyperTypeSystemTheory.type_widens_to_def]) >>
  qpat_x_assum `pt = if _ then _ else _` kall_tac >>
  `vv_at ce cx pt sa sb ee (Value v) vv a /\ vv_own ce cx pt sa sb ee (Value v) vv a` by
    (qpat_assum `vv = _` (fn th => PURE_REWRITE_TAC [th]) >>
     irule sret_buffer_at_own >> asm_rewrite_tac[] >>
     reverse conj_tac >- (qexists_tac `off` >> asm_rewrite_tac[]) >>
     gen_tac >> strip_tac >>
     qpat_assum `!tv. evaluate_type _ pt = SOME tv ==> _` drule >>
     strip_tac >> asm_rewrite_tac[] >> decide_tac) >>
  `eval_operand (Var root) a = SOME (n2w off)` by
    (qpat_assum `buf.buf_operand = Var root` (fn root_eq =>
       qpat_assum `eval_operand buf.buf_operand a = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [root_eq]))) >>
  `vv_holds_mods ce cx pt (Value v) vv ee a` by (
    simp[vv_holds_mods_def, vv_holds_def, base_ptr_def, read_result_def, return_def] >>
    gen_tac >> strip_tac >>
    qpat_assum `!tv. evaluate_type _ pt = SOME tv ==> _` drule >> strip_tac >>
    `val_in_memory tvt v off a.vs_memory` by
      (first_x_assum irule >> simp[mem_agree_outside_def]) >>
    simp[] >> strip_tac >> irule val_in_memory_word_type >> metis_tac[]) >>
  `vv_store_bound cx pt ret ee (Value v) vv a` by (
    simp[vv_store_bound_def, base_ptr_def, read_result_def, return_def] >>
    gen_tac >> strip_tac >>
    qpat_assum `!tv. evaluate_type _ pt = SOME tv ==> _` drule >> strip_tac >> decide_tac) >>
  `ptr_vv_ok cx pt (Value v) vv ee J N a` by (
    simp[ptr_vv_ok_def, ptr_mem_ok_def, base_ptr_def, read_result_def, return_def] >>
    rpt gen_tac >> strip_tac >>
    qpat_assum `!tv. evaluate_type _ pt = SOME tv ==> _` drule >> strip_tac >>
    simp[] >> strip_tac >> qexistsl [`root`,`off`,`buf.buf_size`] >> simp[] >> decide_tac) >>
  `ptr_buf_ok ce e buf.buf_operand J a` by (
    simp[ptr_buf_ok_def] >> metis_tac[]) >>
  `expr_has_effect e` by simp[Abbr `e`, supportedExprTraverseTheory.expr_has_effect_def] >>
  `vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v) vv a` by
    (pure_rewrite_tac[vv_post_mods_def] >>
     simp[vv_place_ptr_mods_def, vv_place_ptr_def] >> metis_tac[]) >>
  map_every (fn p => qpat_x_assum p mp_tac)
    [`vv_store_bound _ _ _ _ _ _ _`, `ptr_vv_ok _ _ _ _ _ _ _ _`,
     `vv_own _ _ _ _ _ _ _ _ _`, `ptr_buf_ok _ _ _ _ _`] >>
  simp[base_ptr_def, vv_location_def]
QED
