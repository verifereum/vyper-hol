(* The empty declaration reads the default on the raw RHS run; the
   following store initializes one word and only then installs the binding. *)
Theory bodyAnnEmptyContinuationMods
Ancestors
  bodyAnnCopyEmptyRhsMods bodyAnnCopyInstallMods bodyLocalEmptyWriteMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  stmtSimDeclSource exprSimMemorySource stmtSimProps haltExitProj
  reasonCopySourcePtr bodyFullUnwrapRun loweringShapeRules stmtSimDeclMem
  vyperTyping vyperStorageTrace vyperStorageFootprint emittedSeqComposePtr
  exprSimDefs bodyFullPostsMods bodyMemoryDefs bodyPtrDefs
  vyperInterpreter vyperState venomExecSemantics venomState venomInst
  valueEncodingProps bodyFullShadowBodyInv stateRelProj ptrDiscipline
  finite_map pred_set words arithmetic

(* The successful read is a pure step on the raw result at the same cut. *)
Theorem ann_empty_read_outcome[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,entry,Ga,tna)
    (\H res mid G tn s. res = INL (Value v) /\ P H mid G tn s)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna)
    (\H res mid G tn s. res = INL v /\ P H mid G tn s)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`!u. storage_trace_frame (read_result _ u)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v'`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[]) >>
  qexists_tac `\H res mid G tn s.
    res = INL (Value v) /\ P H mid G tn s /\ ~s.vs_halted /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      simp[GSYM expr_exit_def] >>
      metis_tac[expr_exit_INR_type,halt_exit_INR_type]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[storage_trace_domain_def]) >> strip_tac >> gvs[] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G1`,`mid`,`INL v`,`t`,`tn1`] >>
  simp[read_result_def,return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ann_empty_store_history[local]:
  emit_void MSTORE [Var p;Lit 0w] b = ((),sf) /\ fn_has_code b sf func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  lookup_var p s = SOME w ==>
  alloca_history func (mstore (w2n w) 0w s with vs_inst_idx := LENGTH sf.cs_current_insts)
Proof
  strip_tac >>
  `sf.cs_current_bb = b.cs_current_bb /\
   sf.cs_current_insts = b.cs_current_insts ++
       [mk_inst b.cs_next_id MSTORE [Var p;Lit 0w] []]` by gvs[emit_void_eq] >>
  `step_inst_base (mk_inst b.cs_next_id MSTORE [Var p;Lit 0w] []) s =
     OK (mstore (w2n w) 0w s)` by simp[mk_inst_def,step_inst_base_opcode_eqs,
       exec_write2_def,eval_operand_def] >>
  irule emitted_alloca_history >> simp[] >>
  qexistsl_tac [`[mk_inst b.cs_next_id MSTORE [Var p;Lit 0w] []]`,`s`,`b`] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,mk_inst_def,is_terminator_def]
QED

(* Resources at the reached raw/read endpoint, independent of its result type. *)
val empty_read_frame = ``
  stmt_state_rel H ctx func ce cx mid s /\
  immutable_frame_mods func ce cx mid s /\
  storage_well_formed_on cx mid (FST (H : (bool # 256 word # type_value) list # num list)) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ghost_inv_at_mods (DF H) lo d ce cx mid G tn s /\
  return_buf_frame d ce b s /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  w2n w + sz <= s.vs_alloca_next /\
  (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q s = SOME z) /\
  (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==> FLOOKUP s.vs_allocas ad = SOME ent) /\
  (!q. not_fresh_at sa q ==> FLOOKUP G q = FLOOKUP G0 q /\
        op_taint tn (Var q) = op_taint tn0 (Var q)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_frame old es sa s0 ce mid s /\
  (!ad off len i.
    FLOOKUP s0.vs_allocas ad = SOME (off,len) /\ ad < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
      off + len <= x \/ x + cap <= off) /\
    off <= i /\ i < off + len /\ i IN tn.t_mem ==> i IN tn0.t_mem)``;

val empty_install_static = ``
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  sa.cs_next_id <= inst.inst_id /\
  local_ptrs_reserved ce b /\ (!q. not_fresh_at sa q ==> not_fresh_at b q) /\
  (!q cap. ce.ce_return_buf = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  (!q cap. ce.ce_return_pc = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  type_memory_size tyv <= sz /\ fn_inst_ids_distinct func /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\ fn_has_code b sf func /\
  return_buf_sep d old es s0 /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list) ctx func old cx es s0 /\
  local_ptrs_reserved old sa``;

val empty_installed = ``
  stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
  cenv_top_ext old ce out.scopes /\
  stmt_state_rel H ctx func ce cx out t /\ immutable_frame_mods func ce cx out t /\
  storage_well_formed_on cx out (FST (H : (bool # 256 word # type_value) list # num list)) /\
  return_buf_frame d ce sf t /\ alloca_history func t /\ return_buf_sep d ce out t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx out G tf t /\
  (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q t = SOME z) /\
  (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==> FLOOKUP t.vs_allocas ad = SOME ent) /\
  (!q. not_fresh_at sa q ==> FLOOKUP G q = FLOOKUP G0 q /\
      op_taint tf (Var q) = op_taint tn0 (Var q)) /\
  alloca_frame old es sa s0 ce out t /\
  (!ad off len i.
    FLOOKUP s0.vs_allocas ad = SOME (off,len) /\ ad < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
      off + len <= x \/ x + cap <= off) /\
    off <= i /\ i < off + len /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem ann_empty_installed_suffix:
  ^empty_install_static /\
  has_length_word typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
     (INL (default_value tyv),mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ^empty_read_frame) ==>
  ?out t tf.
    (!tail. new_variable id tyv (default_value tyv) (mid with gas_obs := tail) =
       (INL (),out with gas_obs := tail)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tf)) /\
    (out with gas_obs := [] = out) /\
    (!H. valid_horizon cx st0 H out.storage_trace /\
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw+cap) t) ==>
      ^empty_installed)
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) =
     (INL (default_value tyv),mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     pop_assum (fn norm => qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [norm,listTheory.APPEND_NIL])))) >>
  drule_all_then strip_assume_tac annassign_continuation_success >>
  qabbrev_tac `out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := default_value tyv; popped := []|>))::rest` >>
  `!tail. new_variable id tyv (default_value tyv) (mid with gas_obs := tail) =
     (INL (),out with gas_obs := tail)` by (irule new_variable_success_gas_obs >> simp[]) >>
  `out.storage_trace = mid.storage_trace` by simp[Abbr `out`] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `32 <= type_memory_size tyv` by
    (qspecl_then [`get_tenv cx`,`typ`,`tyv`,`0`,`(mstore 0 0w s).vs_memory`]
       mp_tac memory_length_word_layout >> simp[mstore_mem_word_at_same]) >>
  `ptr_covers G tn p s 32` by (irule ptr_covers_mono >> qexists_tac `sz` >> simp[] >> decide_tac) >>
  `w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  suspend "write"
QED

Resume ann_empty_installed_suffix[write]:
  drule_at (Pat `emit_void _ _ _ = _`) local_empty_write_path_mods >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspecl_then [`w`,`default_value tyv`,`lo`,`func`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `out with gas_obs := [] = out` by simp[Abbr `out`,evaluation_state_component_equality] >>
  qexistsl_tac [`out`,`t`,`tf`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel _ _ _ ce _ mid s`
       (fn th => ACCEPT_TAC
          (CONJUNCT2 (MATCH_MP stmt_state_rel_local_ptrs_alloca th)))) >>
  `alloca_history func t` by
    (qpat_assum `t = _` (once_rewrite_tac o single) >>
     drule_all_then ACCEPT_TAC ann_empty_store_history) >>
  `~block_is_terminated sf` by
    (irule emit_void_nonterminator_open >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[is_terminator_def]) >>
  `b.cs_next_var <= sf.cs_next_var` by gvs[emit_void_eq] >>
  `return_buf_frame d ce sf t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`b`] >>
     simp[mstore_def,lookup_var_def]) >>
  suspend "install"
QED

Resume ann_empty_installed_suffix[install]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `out.storage_trace = mid.storage_trace` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!HH. valid_horizon _ _ HH _ ==> stmt_state_rel HH _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  mp_tac (Q.INST [`n` |-> `32`,`D` |-> `DF H`, `Gf` |-> `G`,
                  `v` |-> `default_value tyv`]
    (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] ann_copy_install_post_mods)) >>
  (impl_tac >- suspend "install_inputs") >> simp[arithmeticTheory.ADD_COMM]
QED

Resume ann_empty_installed_suffix[install_inputs]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (`allocas_below_fmp t <=> allocas_below_fmp s` by
       simp[allocas_below_fmp_def,mstore_def] >>
     qpat_assum `allocas_below_fmp t <=> _` (once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) s` by
    (`!n. allocas_from n t <=> allocas_from n s` by simp[allocas_from_def] >>
     qpat_assum `!n. allocas_from n t <=> _` (once_rewrite_tac o single o GSYM) >>
     first_assum ACCEPT_TAC) >>
  simp[default_value_well_typed,op_taint_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!ad off len i. _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then irule >> rpt strip_tac >>
  qpat_assum `!name a cap. local_region _ _ _ name a cap ==> _`
    (drule_then mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Finalise ann_empty_installed_suffix[local]

Theorem ann_copy_empty_continuation_mods:
  ^empty_install_static /\
  compile_expr ce (expr_type e) e a = (vv,b) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a =
    (vv,shadow_b) /\
  gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code shadow_a shadow_b shadow_func /\
  local_ptrs_reserved ce a /\ (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  return_buf_frame d ce a entry /\ alloca_history func entry /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp entry) /\
  (!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es entry /\ immutable_frame_mods func ce cx es entry /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es Ga tna entry) /\
  ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
  entry.vs_inst_idx = LENGTH a.cs_current_insts /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  expr_body_pre_mods mods ce cx env e es /\
  is_empty_value_expr e /\ has_length_word typ /\
  type_widens_to env.type_defs (expr_type e) typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  lookup_scopes id es.scopes = NONE /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
  FLOOKUP entry.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  w2n w + sz < dimword (:256) /\ w2n w + sz <= entry.vs_alloca_next /\
  sa.cs_next_id <= a.cs_next_id /\ (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x entry = SOME z) /\
  (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==> FLOOKUP entry.vs_allocas ad = SOME ent) /\
  alloca_frame old es sa s0 ce es entry /\ ghost_kept_at lo old es sa G0 tn0 s0 Ga tna ==>
  ?P.
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      ce.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna)
      P (\H res mid gt r. expr_exit res r /\ halt_exit H cx mid res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
    (!marks res mid G tn s.
      (!tail. bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
         (res,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        P H res mid G tn s /\ ~s.vs_halted /\ mid.gas_obs = []) ==>
      ?v out t Gf tf. res = INL v /\
        (!tail. new_variable id tyv v (mid with gas_obs := tail) = (INL (),out with gas_obs := tail)) /\
        (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) [] (OK t,Gf,tf)) /\
        (!H. valid_horizon cx st0 H out.storage_trace ==>
          (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw+cap) t) ==>
          (\out G. ^empty_installed) (out with gas_obs := []) Gf))
Proof
  strip_tac >>
  drule_then assume_tac annassign_admissible_rhs >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qexists_tac `\H res mid G tn s. res = INL (default_value tyv) /\ ^empty_read_frame` >>
  conj_tac
  >- (ho_match_mp_tac ann_empty_read_outcome >> suspend "raw") >>
  suspend "suffix"
QED

Resume ann_copy_empty_continuation_mods[raw]:
  mp_tac (Q.INST [`aid` |-> `inst.inst_id`, `ty` |-> `expr_type e`] ann_copy_empty_rhs_mods) >>
  (impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    rpt gen_tac >> strip_tac >> irule gas_outcome_full_mods_post_source >>
    qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >> simp[])) >>
  strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> fs[vv_post_mods_def] >>
  qpat_assum `!ad off len i. _ ==> i IN tn0.t_mem` (drule_all_then ACCEPT_TAC)
QED

Resume ann_copy_empty_continuation_mods[suffix]:
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  mp_tac (Q.INST [`prefix` |-> `gas_explicit marks entry.vs_gas_readings`]
    ann_empty_installed_suffix) >>
  (impl_tac >- (simp[] >> rpt gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (drule_then strip_assume_tac) >> simp[])) >>
  disch_then (qx_choosel_then [`out`,`t`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`out`,`t`,`G`,`tf`] >>
  rpt (conj_tac >- simp[]) >> rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_assum `out with gas_obs := [] = out` (once_rewrite_tac o single) >>
  qpat_assum `!H. valid_horizon _ _ H out.storage_trace /\ _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> simp[arithmeticTheory.ADD_COMM] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Finalise ann_copy_empty_continuation_mods
