(* Physical owned values can be relocated without exposing allocation regions
   to expression consumers.  No expression syntax occurs in this boundary. *)
Theory exprSimIfExpWidenedAdapter
Ancestors
  exprSimIfExp exprSimHyps exprSimTypedAlloc valueEncodingTyping loweringPosts
  vyperTypeSystem valueEncodingProps vyperValue valueEncoding vyperMisc
  exprSimVVFrame exprSimAggregateChildren exprSimUnwrap context venomState
  vyperState exprSimDefs exprSimMemorySource gasContext gasSummary
  exprSimProps exprSimAlloc loweringHalt freshWrites fragExec stmtSimDefs
  compileEnv loweringStateRelDefs exprLoweringProps

Theorem normalize_owned_value_framed_frag:
  compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf, sm) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((), sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx sty origin sa es v src s /\
  expr_val_own ce cx sty origin sa es v src s /\
  ~is_word_type sty /\
  val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv /\
  eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory ==>
  frag_exec ctx sa sb (\z. z = s)
    (\u. ?w. stmt_state_rel ctx func ce cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) u.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w, type_memory_size dtv) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      (!name b len. local_region ce es.scopes s name b len ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len)) R
Proof
  strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all expr_val_at_bound >> simp[]) >>
  `?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\
    b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len` by
    (fs[expr_val_own_def] >>
     qpat_x_assum `!tv. evaluate_type _ sty = SOME tv ==> _`
       (qspec_then `stv` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 value_has_type_val_wf] >>
  drule compile_return_normalize_framed_frag >>
  disch_then irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`stv`, `sty`, `sw`, `src`] >> simp[] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `len`] >> simp[]
QED

Theorem ifexp_changed_aggregate_source:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') /\
  post_value_type ce e <> expr_type e /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  expr_post ctx func ce cx e es sa sb s0 es' v src s ==>
  ?stv dtv sw.
    type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_footprint stv v = type_memory_size stv /\
    0 < type_memory_size stv /\
    stmt_state_rel ctx func ce cx es' s /\
    expr_val_at ce cx (post_value_type ce e) sa sb es' v src s /\
    expr_val_own ce cx (post_value_type ce e) sa sb es' v src s /\
    eval_operand src s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory
Proof
  strip_tac >>
  `(!sty dty. arg_type_fits sty dty ==>
      !tenv stv. evaluate_type tenv sty = SOME stv /\
        type_memory_size stv = 0 ==> sty = dty) /\
   (!stys dtys. arg_types_fit stys dtys ==>
      !tenv stvs. OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
        type_memory_size_list stvs = 0 ==> stys = dtys)` by
    (ho_match_mp_tac arg_type_fits_ind >>
     rw[arg_type_fits_def] >>
     gvs[evaluate_type_def, evaluate_types_OPT_MMAP, listTheory.OPT_MMAP_def,
         AllCaseEqs(), type_memory_size_def] >>
     metis_tac[cj 1 type_memory_size_pos]) >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    (spose_not_then assume_tac >>
     `post_value_type ce e = expr_type e` by
       (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
  gvs[] >>
  `~is_word_type ty /\ ~is_bytestring_type ty` by
    metis_tac[post_value_type_word, post_value_type_bytestring,
              vyperASTTheory.expr_type_def] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  `0 < type_memory_size stv` by
    (gvs[type_widens_to_def] >> metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `val_footprint stv v = type_memory_size stv` by
    (qpat_x_assum `evaluate_type _ (lowered_value_type _ _) = _` mp_tac >>
     qpat_x_assum `~is_bytestring_type (lowered_value_type _ _)` mp_tac >>
     qmatch_goalsub_abbrev_tac `evaluate_type tenv sty` >>
     Cases_on `sty` >>
     simp[compileEnvTheory.is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> Cases_on `v` >>
     gvs[val_footprint_def] >>
     gvs[compileEnvTheory.is_bytestring_type_def]) >>
  gvs[expr_post_def, expr_val_rel_def] >>
  gvs[vyperASTTheory.expr_type_def]
QED


(* Conditional adaptation cannot turn a readable result into an admissible
   failure: its only new failures are type errors. *)
Theorem conditional_readable_admissible:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. res = INL tv /\ ss = ee /\
       read_result cx tv ee = (INL v,ee)
Proof
  Cases_on `raw` >>
  simp[read_result_def, conditional_result_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), expr_vv_res_ok_def] >>
  gvs[read_result_def, return_def, raise_def] >>
  imp_res_tac place_type_value_state >> gvs[] >>
  gvs[COND_RATOR, COND_RAND, COND_EXPAND, bind_def, return_def, raise_def] >>
  Cases_on `p` >>
  gvs[place_type_value_def, get_scopes_def, get_immutables_def,
      lift_option_type_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[option_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  gvs[read_place_def, get_immutables_def, bind_def]
QED


Theorem place_type_value_gas_obs:
  place_type_value cx p ee = (INL pt,ee) ==>
  !tail. place_type_value cx p (ee with gas_obs := tail) =
    (INL pt,ee with gas_obs := tail)
Proof
  Cases_on `p` >>
  simp[place_type_value_def, get_scopes_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, bind_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def])
QED

Theorem conditional_result_gas_obs:
  conditional_result cx raw ee = (INL tv,ee) ==>
  !tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)
Proof
  Cases_on `raw`
  >- simp[conditional_result_def, return_def]
  >- (simp[conditional_result_def, bind_def] >>
      strip_tac >>
      gvs[AllCaseEqs()] >>
      imp_res_tac place_type_value_state >> gvs[] >>
      drule place_type_value_gas_obs >> strip_tac >> simp[] >>
      qmatch_goalsub_abbrev_tac `if keep then _ else _` >>
      Cases_on `keep` >> gvs[return_def, bind_def, AllCaseEqs()] >>
      rename1 `read_place cx p ee = (INL v,ee)` >>
      `read_result cx (PlaceR p) ee = (INL v,ee)` by
        simp[read_result_def] >>
      drule read_result_gas_obs >> simp[read_result_def]) >>
  simp[conditional_result_def, raise_def]
QED

Theorem gas_marked_continuation_admissible:
  gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) mid (OK t) /\
  gas_admissible (bind a k) admissible es ==>
  gas_admissible (k v) admissible (mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def, gas_admissible_def] >>
  rpt strip_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then
    `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  simp[bind_def] >> metis_tac[]
QED

Theorem vv_at_alloc_mono_frame:
  vv_at cenv cx ty sa sm es tv vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_at cenv cx ty sa sn es tv vv t
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        metis_tac[]) >>
  metis_tac[]
QED

Theorem vv_own_alloc_mono_frame:
  vv_own cenv cx ty sa sm es tv vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_own cenv cx ty sa sn es tv vv t
Proof
  Cases_on `vv` >>
  simp[vv_own_def, vv_operand_def, expr_val_own_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        metis_tac[]) >>
  metis_tac[]
QED

(* Allocation changes provenance monotonically, but not the represented value. *)
Theorem vv_post_alloc_mono_frame:
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  stmt_state_rel ctx func ce cx ee u /\
  u.vs_memory = s.vs_memory /\
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region ce ee.scopes u n b sz <=>
            local_region ce ee.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post ctx func ce cx e es sa sn s0 ee tv vv u
Proof
  strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee u` by
    (irule vv_holds_vars_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_at ce cx (post_value_type ce e) sa sn ee tv vv u` by
    (irule vv_at_alloc_mono_frame >> qexistsl [`s`, `sm`] >> simp[]) >>
  `post_value_type ce e <> expr_type e ==>
    vv_own ce cx (post_value_type ce e) sa sn ee tv vv u` by
    (strip_tac >> irule vv_own_alloc_mono_frame >>
     qexistsl [`s`, `sm`] >> simp[]) >>
  `locals_kept ce es ee s0 u` by
    (irule locals_kept_mem_tail >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_storage_live cx vv ee s ==> vv_storage_live cx vv ee u` by
    (Cases_on `vv` >> fs[contextTheory.vv_operand_def]) >>
  simp[vv_post_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem alloc_unwrap_physical_post_frag:
  compile_alloc_buffer sz sm = (buf,sn) /\
  unwrap_value ce vv sn = (op,sb) /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ sz < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  read_result cx tv ee = (INL v,ee) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
     ~is_word_type (post_value_type ce e) ==>
     type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  eval_operand (vv_operand vv) s = SOME a ==>
  frag_exec ctx sm sb (\z. z = s)
    (\u. expr_post ctx func ce cx e es sa sb s0 ee v op u) R
Proof
  strip_tac >>
  `cs_extends sm sn /\ cs_extends sn sb` by
    metis_tac[compile_alloc_buffer_extends, unwrap_value_extends] >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (qspec_then `sz` (qspec_then `sm` mp_tac) ci_mono_compile_alloc_buffer >>
     simp[ci_mono_def]) >>
  `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `!n b k. local_region ce ee.scopes u n b k <=>
           local_region ce ee.scopes s n b k` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >>
         conj_tac
         >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sm`, `ee.scopes`, `u`] >> simp[] >> metis_tac[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`s`, `sm`, `ee.scopes`] >> simp[] >> metis_tac[]) >>
  `vv_post ctx func ce cx e es sa sn s0 ee tv vv u` by
    (irule vv_post_alloc_mono_frame >> simp[] >>
     qexistsl [`s`, `sm`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
  irule frag_exec_seq >> qexistsl [`(\z. z = u)`, `sn`] >> simp[] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by
    decide_tac >>
  qpat_x_assum `local_ptrs_reserved ce sm` kall_tac >>
  drule_all unwrap_value_materialise_physical_sim >>
  disch_then (qspecl_then [`ctx`, `s0`, `R`] mp_tac) >>
  strip_tac >> irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[]
QED

(* Common endpoint decomposition, before distinguishing typed and byte copies. *)
Theorem compile_ifexp_copy_parts:
  ~is_word_type dty /\ ~same_memory_layout ce sty dty /\
  compile_ifexp_arm ce dty sty vv sa = (op,sb) ==>
  ?buf sm src sn.
    compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) /\
    unwrap_value ce vv sm = (src,sn) /\
    compile_store_memory ce src buf.buf_operand dty sty sn = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  gvs[exprLoweringTheory.compile_ifexp_arm_def, comp_ignore_bind_def,
      comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED
