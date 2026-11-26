(* Choose a linked Len load endpoint before specializing its horizon. *)
Theory bodyLenLoadSuffixMods
Ancestors
  bodyLenQualifiedHeaderMods bodyLenPathPostMods bodyLenMemoryRunCoreMods
  bodyLenCtorCodeRunMods bodyLenRuntimeCodeRunMods bodyLenStorageRunMods
  bodyFullShadowBodyInv exprSimHypsDefs exprSimLen builtinProps loweringPosts
  vyperStorageFootprint valueEncodingDefs context bodyPtrDefs

Theorem len_load_suffix_mods:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op pvt tvt.
    expr_body_pre_mods mods cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre_mods mods cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
           eval_operand (vv_operand vv) t = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
             val_in_memory rt val (w2n w) mem) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?n z G2 tn2.
      result_array_length cx tv ee = (INL n,ee) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all len_qualified_header_mods >> simp[LET_THM] >> strip_tac >>
  qabbrev_tac `loc = case vv_location vv of NONE => LocMemory | SOME l => l` >>
  `?z G2 tn2.
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2)) /\
     eval_operand op z = SOME (n2w n) /\ op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
     ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
     z.vs_inst_idx = LENGTH sb.cs_current_insts /\
     (alloca_history func t ==> alloca_history func z) /\
     z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
     (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
       FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
     tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm` by
    suspend "run" >>
  qexistsl_tac [`n`,`z`,`G2`,`tn2`] >> conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  irule len_path_post_mods >> simp[] >>
  qexistsl_tac [`sm`,`tv`,`vv`] >> simp[]
QED

Resume len_load_suffix_mods[run]:
  Cases_on `loc = LocMemory` >- suspend "memory" >>
  `vv_location vv = SOME loc` by (Cases_on `vv_location vv` >> fs[Abbr `loc`]) >>
  Cases_on `loc = LocCode` >- suspend "code" >>
  suspend "slot"
QED

Resume len_load_suffix_mods[memory]:
  `mload (w2n w) t = n2w n` by fs[ptr_load_val_def] >>
  irule len_memory_run_core_mods >> simp[] >>
  qexistsl_tac [`G0`,`cenv`,`d`,`e`,`env`,`es`,`pvt`,`s0`,`sa`,`tn0`,`tv`,`tvt`,`vv`,`w`] >>
  fs[]
QED

Resume len_load_suffix_mods[code]:
  qpat_x_assum `Abbrev (loc = _)` kall_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
     (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb)` by
    simp[] >>
  Cases_on `cenv.ce_is_ctor`
  >- (`mload (w2n w) t = n2w n` by fs[ptr_load_val_def] >>
      `w2n w + 32 <= lo` by fs[] >>
      `!m. mem_agree_outside tn.t_mem t.vs_memory m ==> mem_word_at (w2n w) m = n2w n` by fs[] >>
      drule_all len_ctor_code_run_alias_safe_mods >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`z`,`G2`,`tn2`] >> simp[]) >>
  `w2n w <= LENGTH t.vs_data_section /\ mem_word_at (w2n w) t.vs_data_section = n2w n` by
    fs[ptr_load_val_def, mem_word_at_def] >>
  `op_taint tn (vv_operand vv) = {}` by
    (Cases_on `vv` >> gvs[vv_location_def,vv_operand_def,ptr_vv_ok_def]) >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  drule_all len_runtime_code_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`z`,`G2`,`tn2`] >> simp[]
QED

Resume len_load_suffix_mods[slot]:
  qpat_x_assum `Abbrev (loc = _)` kall_tac >>
  `?tr. loc = slot_loc tr` by
    (Cases_on `loc` >> fs[] >- (qexists_tac `F` >> simp[slot_loc_def]) >>
     qexists_tac `T` >> simp[slot_loc_def]) >>
  qpat_x_assum `loc = slot_loc tr` SUBST_ALL_TAC >>
  `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
     (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb)` by simp[] >>
  `(if tr then tload w t else sload w t) = n2w n` by
    (Cases_on `tr` >> fs[slot_loc_def,ptr_load_val_def]) >>
  drule_all_then assume_tac sized_type_widens_source >>
  drule_all len_storage_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`z`,`G2`,`tn2`] >> simp[]
QED

Finalise len_load_suffix_mods
