(* Install a word at the selected local subplace, after the operand unwrap. *)
Theory bodyAssignLocalWordInstallAtPathMods
Ancestors
  bodyAssignLocalPreStoreMods bodyAssignLocalStoreCutsMods
  bodyAssignLocalWordPathMods stmtLowering stmtSimDeclStore abiValueEncoding
  vyperPlaceFrames stmtSimProps venomState

Theorem assign_local_word_install_at_path_mods:
  local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw)
    ee cur s G tn /\
  local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw) (op,sw)
    sa ee cur s G tn /\
  compile_assign_value cenv (FST dst) LocMemory op (is_word_type dty)
    (vv_location vv) dty (lowered_value_type cenv e) (type_memory_bytes cenv dty)
    cur = ((),sb) /\
  is_word_type dty /\ fn_has_code cur sb func /\ fn_inst_ids_distinct func /\
  ee.gas_obs = [] /\ write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?t Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf) /\
    (\ef. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
      ~block_is_terminated sb /\ cenv_top_ext cenv cenv ef.scopes /\
      stmt_state_rel H ctx func cenv cx ef t /\
      immutable_frame_mods func cenv cx ef t /\
      storage_well_formed_on cx ef (FST H) /\
      return_buf_frame d cenv sb t /\ alloca_history func t /\
      return_buf_sep d cenv ef t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
               FLOOKUP t.vs_allocas aid = SOME a) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv ef t /\
      (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
         (!name b' sz. local_region cenv es.scopes s0 name b' sz ==>
                        a + n <= b' \/ b' + sz <= a) /\
         a <= i /\ i < a+n /\ i IN tf.t_mem ==> i IN tn0.t_mem)) (ff with gas_obs := [])
Proof
  BETA_TAC >> pure_once_rewrite_tac[GSYM local_assign_normal_at_cut_mods] >>
  strip_tac >>
  `ff.storage_trace = ee.storage_trace /\ (ff with gas_obs := []) = ff` by
    (drule_then (qx_choose_then `sc` SUBST1_TAC) write_memory_place_frame >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_x_assum `local_assign_here_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
  qpat_x_assum `local_assign_store_source_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [local_assign_store_source_mods_def]) >>
  simp[LET_THM] >> strip_tac >>
  `type_memory_size ptv = 32` by drule_all_then ACCEPT_TAC abi_word_type_size >>
  `?q. FST dst = Var q /\ ptr_covers G tn q s 32` by
    (qpat_x_assum `0 < type_memory_size ptv ==> _` mp_tac >>
     simp[] >> disch_then (qx_choose_then `q` strip_assume_tac) >> qexists `q` >> simp[]) >>
  `emit_void MSTORE [Var q;op] cur = ((),sb) /\ lookup_var q s = SOME dw` by
    fs[compile_assign_value_def,eval_operand_def] >>
  `off + 32 <= cap /\ eval_operand op s = SOME (typed_val_to_w256 etv v)` by simp[] >>
  qabbrev_tac `t = mstore (w2n dw) (typed_val_to_w256 etv v) s with
                    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `tf = tn with t_mem := tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` >>
  qexistsl [`t`,`G`,`tf`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `t = (mstore (w2n dw) (typed_val_to_w256 etv v) s with
        vs_inst_idx := LENGTH sb.cs_current_insts)` by simp[Abbr `t`] >>
  `tf = (tn with t_mem := tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32})` by
    simp[Abbr `tf`] >>
  drule_all assign_local_word_write_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `alloca_history func t` by
    (qpat_assum `_ /\ _ ==> alloca_history func t` irule >> simp[]) >>
  `storage_well_formed_on cx ff (FST H)` by
    (qpat_assum `_ ==> storage_well_formed_on cx ff _` irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
  simp[NoAsms,local_assign_normal_mods_def,loweringPostsTheory.stmt_lands_def,cenv_top_ext_refl] >>
  conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `t.vs_alloca_next = _` (once_rewrite_tac o single) >>
               first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `!x. lookup_var x t = _` (once_rewrite_tac o single) >>
               first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `t.vs_allocas = _` (once_rewrite_tac o single) >>
               first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `!x. op_taint tf (Var x) = _` (once_rewrite_tac o single) >>
               first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `i IN tn.t_mem` by
    (qpat_assum `tf.t_mem SUBSET tn.t_mem` (irule o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    (drule_all_then ACCEPT_TAC)
QED
