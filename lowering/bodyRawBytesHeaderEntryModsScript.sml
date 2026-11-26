(* The readonly MLOAD/ADD cut between the bytes read and keyword evaluation. *)
Theory bodyRawBytesHeaderEntryMods
Ancestors
  bodyFullRawCallHeader bodyFullRawCallHeaderView bodyForRangeScalarFrameMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullIfExpReach bodyPtrDefs
  exprSimHash exprSimHashBoundary exprSimMemDefs exprSimProps exprLoweringProps
  stateRelProj loweringPosts loweringStateRelDefs vyperStorageFootprint
  valueEncodingDefs vyperValue vyperAST venomState words compileEnv
  bodyMemoryDefs ptrDiscipline loweringShapeDefs fragExec gasOutcomeFull
  gasContext fragGasOriginPtr venomInst finite_map

val _ = Parse.hide "ptr";

Triviality raw_bytes_header_address:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  alloca_room ctx func t /\
  expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data t /\
  expr_store_bound cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data t ==>
  ?b. eval_operand data t = SOME (n2w b) /\
      b + 32 + LENGTH bs <= t.vs_alloca_next /\
      b + 32 + LENGTH bs < dimword (:256)
Proof
  simp[alloca_room_def, expr_val_rel_def, expr_store_bound_def,
       is_word_type_def, val_store_size_def] >>
  rpt strip_tac >> gvs[val_store_size_def, is_word_type_def] >>
  qexists_tac `w2n w` >> simp[] >>
  qspec_then `LENGTH bs` assume_tac le_word_size_mul >> decide_tac
QED

Triviality raw_bytes_header_value_at:
  local_ptrs_reserved cenv s2 /\ not_fresh_at s2 x /\
  (!x. not_fresh_at s2 x ==> lookup_var x t4 = lookup_var x tD) /\
  t4.vs_allocas = tD.vs_allocas /\
  eval_operand (Var x) tD = SOME w /\
  expr_val_at cenv cx ty s1 s2 es (BytesV bs) (Var x) tD ==>
  eval_operand (Var x) t4 = SOME w /\
  expr_val_at cenv cx ty s1 s2 es (BytesV bs) (Var x) t4
Proof
  strip_tac >>
  `eval_operand (Var x) t4 = eval_operand (Var x) tD` by
    fs[eval_operand_def] >>
  `!n lb sz. local_region cenv es.scopes t4 n lb sz <=>
             local_region cenv es.scopes tD n lb sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rw[] >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> first_x_assum drule >> simp[]) >>
  conj_tac >- simp[] >>
  `expr_val_at cenv cx ty s1 s2 es (BytesV bs) (Var x) t4 <=>
   expr_val_at cenv cx ty s1 s2 es (BytesV bs) (Var x) tD` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ tD` kall_tac >>
     simp[expr_val_at_def]) >>
  fs[]
QED

Theorem raw_bytes_header_entry_mods:
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  storage_trace_domain cx st0 esD.storage_trace /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_post_mods H ctx func cenv cx e esA s1 s2 tA esD (BytesV bs) data tD /\
    ghost_inv_at_mods (DF H) lo d cenv cx esD GD tnD tD) /\
  expr_store_bound cx (post_value_type cenv e) (BytesV bs) data tD /\
  ptr_val_ok cx (post_value_type cenv e) (BytesV bs) data GD tnD tD /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr,s4) /\
  (!x. data = Var x ==> not_fresh_at s2 x) /\
  local_ptrs_reserved cenv s2 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  fn_has_code s2 s4 func /\ fn_inst_ids_distinct func /\
  ~tD.vs_halted /\ tD.vs_current_bb = s2.cs_current_bb /\
  tD.vs_inst_idx = LENGTH s2.cs_current_insts /\ alloca_history func tD /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp tD) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst s. frag_reachable ctx func tD fn inst s ==> dalloca_fmp_headroom inst s) ==>
  ?b t4 G4 tn4.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (tD,GD,tnD) [] (OK t4,G4,tn4)) /\
    (!H. valid_horizon cx st0 H esD.storage_trace ==>
      stmt_state_rel H ctx func cenv cx esD t4 /\
      immutable_frame_mods func cenv cx esD t4 /\
      storage_well_formed_on cx esD (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx esD G4 tn4 t4) /\
    eval_operand data t4 = SOME (n2w b) /\
    expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data t4 /\
    eval_operand len t4 = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr t4 = SOME (n2w (b+32)) /\
    b + 32 + LENGTH bs < dimword (:256) /\
    b + 32 + LENGTH bs <= t4.vs_alloca_next /\
    mem_bytes_at (b+32) (LENGTH bs) t4.vs_memory = bs /\
    (!mem. mem_agree_outside tn4.t_mem t4.vs_memory mem ==>
        mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
    op_taint tn4 len = {} /\ op_prov G4 len = NONE /\ op_taint tn4 ptr = {} /\
    (?p base size. ptr = Var p /\ op_prov G4 ptr = SOME (base,size) /\
       base <= b + 32 /\ b + 32 + LENGTH bs <= base + size /\
       (bs <> [] ==> ptr_covers G4 tn4 p t4 (LENGTH bs))) /\
    (!x. not_fresh_at s2 x ==>
       lookup_var x t4 = lookup_var x tD /\ FLOOKUP G4 x = FLOOKUP GD x /\
       op_taint tn4 (Var x) = op_taint tnD (Var x)) /\
    (!x. len = Var x \/ ptr = Var x ==> not_fresh_at s4 x) /\
    t4.vs_alloca_next = tD.vs_alloca_next /\ t4.vs_allocas = tD.vs_allocas /\
    t4.vs_memory = tD.vs_memory /\
    ~t4.vs_halted /\ t4.vs_current_bb = s4.cs_current_bb /\
    t4.vs_inst_idx = LENGTH s4.cs_current_insts /\ alloca_history func t4 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t4) /\ local_ptrs_reserved cenv s4 /\
    (!fn inst s. frag_reachable ctx func t4 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!sa es s0. sa.cs_next_var <= s2.cs_next_var /\ wb_frame cenv es esD sa s0 tD ==>
       wb_frame cenv es esD sa s0 t4) /\
    (!sa es s0 G0 tn0. sa.cs_next_var <= s2.cs_next_var /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD ==>
       ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4) /\
    (!sa df. sa.cs_next_var <= s2.cs_next_var /\ return_buf_frame df cenv sa tD ==>
       return_buf_frame df cenv sa t4 /\ return_buf_frame df cenv s4 t4)
Proof
  strip_tac >>
  `post_value_type cenv e = BaseT (BytesT (Dynamic cap))` by
    simp[post_value_type_bytestring,is_bytestring_type_def] >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esD tD /\
    immutable_frame_mods func cenv cx esD tD /\
    storage_well_formed_on cx esD (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx esD GD tnD tD /\
    expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data tD /\
    expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data tD` by
      (rpt strip_tac >> first_x_assum drule >> simp[expr_post_mods_def,expr_post_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    fs[storage_trace_domain_def] >>
  pop_assum (fn horizon => first_assum (strip_assume_tac o C MATCH_MP horizon)) >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  `expr_store_bound cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data tD /\
   ptr_val_ok cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data GD tnD tD` by fs[] >>
  drule_all_then strip_assume_tac raw_bytes_header_address >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac raw_call_header_bytes_view >>
  `b < dimword (:256)` by decide_tac >>
  drule_all_then strip_assume_tac hash_data_prefix_run >>
  `allocas_from lo tD /\ lo <= tD.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all_then (qspecl_then [`PG`,`esD`,`explicit`] strip_assume_tac)
    raw_call_header_joint >>
  suspend "assemble"
QED

Resume raw_bytes_header_entry_mods[assemble]:
  `t4.vs_fmp = tD.vs_fmp /\ t4.vs_initial_fmp = tD.vs_initial_fmp /\
   t4.vs_data_section = tD.vs_data_section /\ t4.vs_call_ctx = tD.vs_call_ctx /\
   t4.vs_accounts = tD.vs_accounts /\ t4.vs_transient = tD.vs_transient /\
   t4.vs_immutables = tD.vs_immutables` by
    (qpat_assum `t4 with <|vs_vars := _; vs_inst_idx := _|> = tD` mp_tac >>
     simp[NoAsms,venom_state_component_equality]) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esD t4 /\
    immutable_frame_mods func cenv cx esD t4 /\
    storage_well_formed_on cx esD (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx esD G4 tn4 t4` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ tD /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (qpat_assum `t4 = t with vs_inst_idx := _` (SUBST1_TAC) >>
         simp[stmt_state_rel_inst_idx] >>
         irule hash_readonly_state_rel >> qexistsl_tac [`tD`,`s2`] >> simp[]) >>
     conj_tac
     >- (irule immutable_frame_mods_exterior_frame >>
         qexistsl_tac [`esD`,`tD`,`s2`] >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ tD`
       (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          ghost_inv_at_mods_exterior_frame) th)) >>
     rpt (conj_tac >- (REFL_TAC ORELSE first_assum ACCEPT_TAC)) >>
     qexists_tac `s2` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand data t4 = SOME (n2w b) /\
    expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data t4` by
    (qpat_x_assum `data = Var x` SUBST_ALL_TAC >>
     `not_fresh_at s2 x` by simp[] >>
     `!z. not_fresh_at s2 z ==> lookup_var z t4 = lookup_var z tD` by simp[] >>
     irule raw_bytes_header_value_at >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexists_tac `tD` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!fn inst s. frag_reachable ctx func t4 fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ [] _`
       (qspec_then `DF (storage_trace_horizon esD.storage_trace)`
         (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           gas_origin_ptr_path_dalloca_fmp_headroom) th))) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `b + 32 + LENGTH bs <= t4.vs_alloca_next` by
    (qpat_assum `t4.vs_alloca_next = tD.vs_alloca_next` (once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t4)` by
    (pure_rewrite_tac[allocas_below_fmp_def] >>
     qpat_assum `t4.vs_allocas = tD.vs_allocas` (once_rewrite_tac o single) >>
     qpat_assum `t4.vs_initial_fmp = tD.vs_initial_fmp` (pure_rewrite_tac o single) >>
     qpat_assum `t4.vs_fmp = tD.vs_fmp` (once_rewrite_tac o single) >>
     simp[GSYM allocas_below_fmp_def]) >>
  qexistsl_tac [`b`,`t4`,`G4`,`tn4`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qmatch_asmsub_rename_tac `G4 = (_ : (string,num # num) fmap) |+ (ptr_v,cov_base,cov_size)` >>
      qexistsl_tac [`ptr_v`,`cov_base`,`cov_size`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `ptr = Var ptr_v` (once_rewrite_tac o single) >>
          pure_rewrite_tac[op_prov_def,operand_case_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
      conj_tac >- decide_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      fs[listTheory.LENGTH_NIL]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_bytes_header_entry_mods
