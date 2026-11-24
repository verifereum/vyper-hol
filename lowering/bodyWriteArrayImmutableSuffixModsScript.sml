(* The constructor array suffix uses one qualified current header and one run. *)
Theory bodyWriteArrayImmutableSuffixMods
Ancestors
  bodyWriteArrayPacketMods bodyWriteArrayOperandsMods bodyWriteArraySelectMods
  bodyWriteArrayImmutableLengthMods bodyWriteArrayImmutableExtendMods
  bodyWriteArrayFinishMods bodyWriteTargetStageMods bodyFullTargetArrayLoad
  bodyPtrBopInRepresentation bodyFullShadowBodyInv bodyFullPostsMods
  exprLowering exprLoweringProps vyperStorageFootprint vyperValueOperation vyperTyping
  loweringPosts loweringStateRelDefs context compileEnv emitHelper emitHelperProps
  ptrDiscipline memLocDefs venomInst venomState finite_map words

Theorem ctor_iload_clean[local]:
  eval_operand addr s = SOME a /\ mem_word_taint tn.t_mem (w2n a) = {} ==>
  op_prov (step_prov PG G (mk_inst id ILOAD [addr] [out]) u) (Var out) = NONE /\
  op_taint (step_taint (mk_inst id ILOAD [addr] [out]) s u tn) (Var out) = {}
Proof
  simp[op_taint_def, op_prov_def, step_taint_def, step_prov_def,
       mk_inst_def, set_prov_def, set_var_taint_def, out_taint_def, out_prov_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem ctor_length_loader_clean[local]:
  array_length_loader_ok T imm LocCode addr nw sn len sl lo ctx func PG s G tn u Gu tu /\
  compile_ptr_load T imm LocCode addr sn = (len,sl) /\
  eval_operand addr s = SOME a /\ mem_word_taint tn.t_mem (w2n a) = {} /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w) ==>
  op_prov Gu len = NONE /\ op_taint tu len = {}
Proof
  Cases_on `imm` >> simp[array_length_loader_ok_def, LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `?opc out. _`
        (qx_choosel_then [`opc`,`out`] (map_every assume_tac o CONJUNCTS)) >>
      `emit_op opc [addr] sn = emit_op ILOAD [addr] sn` by
        (qpat_assum `compile_ptr_load T NONE LocCode _ = emit_op _ _`
           (mp_tac o C AP_THM ``sn:compile_state``) >>
         simp_tac (srw_ss()) [compile_ptr_load_def, compile_imm_load_word_def, EQ_SYM_EQ]) >>
      `opc = ILOAD` by
        (qpat_x_assum `emit_op opc _ _ = emit_op ILOAD _ _` mp_tac >>
         simp[loweringShapeRulesTheory.emit_op_eq, compile_state_component_equality,
              mk_inst_def, instruction_component_equality]) >>
      gvs[] >> irule ctor_iload_clean >> qexists `a` >> simp[])
  >- (ntac 5 (first_x_assum CHOOSE_TAC) >>
      pop_assum (map_every assume_tac o CONJUNCTS) >>
      gvs[] >> irule ctor_iload_clean >>
      rename1 `eval_operand addr s = SOME aw` >> qexists `aw` >>
      reverse conj_tac
      >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      `!w. (step_taint (mk_inst sn.cs_next_id ADD [addr;x] [out1]) s
               (update_var out1 w s) tn).t_mem = tn.t_mem` by
        (gen_tac >> irule bodyPtrEnvBuiltinsEdgesTheory.step_taint_no_memory_effect >>
         simp[update_var_def, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
              written_taint_def]) >> simp[])
QED

Theorem write_array_immutable_suffix_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) ==>
  write_array_suffix_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2))
Proof
  strip_tac >>
  qhdtm_assum `write_array_reached_mods`
    (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon mid2.storage_trace` >>
  `valid_horizon cx st0 H0 mid2.storage_trace` by
    simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `op_prov G1 (FST rb) = NONE` by
    (drule_all write_array_reached_immutable_mods >> strip_tac >> simp[]) >>
  drule_all_then strip_assume_tac write_array_reached_operands_mods >>
  drule_all_then strip_assume_tac write_array_immutable_current_mods >>
  `SND (SND rb) = SOME (ValPT (ArrayT et bd))` by
    (drule write_target_post_view_mods >> simp[value_type_place_def]) >>
  `eval_operand (FST rb) t2 = SOME (n2w (off+k)) /\ op_prov G2 (FST rb) = NONE` by
    fs[] >>
  drule_all write_array_immutable_length_mods >> simp[LET_THM] >> strip_tac >>
  `allocas_from lo t2` by fs[ghost_inv_at_mods_def] >>
  `stmt_state_rel H0 ctx func cenv cx mid2 t2` by fs[expr_post_mods_def, expr_post_def] >>
  qabbrev_tac `nw = n2w (array_length (ArrayTV etv bd) av):bytes32` >>
  `!n. bd = Fixed n ==> nw = n2w n` by
    (rpt strip_tac >> Cases_on `av` >> gvs[Abbr `nw`, value_has_type_def, array_length_def]) >>
  `!cap len sl. bd = Dynamic cap /\
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode (FST rb) sn = (len,sl) ==>
    ?ul Gl tl. array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca LocCode
      (FST rb) nw sn len sl lo ctx func PG t2 G2 tn2 ul Gl tl /\
      op_prov Gl len = NONE /\ op_taint tl len = {}` by
    (rpt strip_tac >>
     qpat_assum `!cap. bd = Dynamic cap ==> _` (drule_then strip_assume_tac) >>
     `compile_ptr_load T cenv.ce_imm_alloca LocCode (FST rb) sn = (len,sl)` by
       (qpat_assum `cenv.ce_is_ctor` (fn th => once_rewrite_tac[GSYM (EQT_INTRO th)]) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!p sl. compile_ptr_load T _ _ _ _ = (p,sl) ==> _`
       (drule_then strip_assume_tac) >>
     `mem_word_taint tn2.t_mem (w2n (n2w (off+k):bytes32)) = {}` by
       fs[w2n_n2w, arithmeticTheory.LESS_MOD, arithmeticTheory.ADD_COMM] >>
     `!base_op. cenv.ce_imm_alloca = SOME base_op ==> eval_operand base_op t2 = SOME 0w` by
       (`lo <> 0` by decide_tac >>
        rpt strip_tac >> drule_all membership_immutable_base_value >> simp[]) >>
     drule_all_then strip_assume_tac ctor_length_loader_clean >>
     qexistsl [`t`,`G'`,`tn'`] >> fs[Abbr `nw`]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  `?t3 G3 tn3. write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (ImmutablePlace owner id path),t1,G1,tn1),
     (index_gas,mid2,IntV i,t2,G2,tn2))
    (LocCode,n2w (off+k),iw,nw) (t3,G3,tn3)` by
    (irule write_array_select_run_mods >> simp[]) >>
  rename1 `write_array_select_frame _ _ (t3,G3,tn3)` >>
  qabbrev_tac `inside = idx_in_range (is_signed_type (expr_type e)) iw nw` >>
  qabbrev_tac `child = PlaceR (ImmutablePlace owner id (path ++ [ValueSubscript (IntV i)]))` >>
  qabbrev_tac `res = if inside then INL child else INR (Error (RuntimeError "evaluate_subscripts array_index"))` >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
      extend_place cx (PlaceR (ImmutablePlace owner id path)) (ValueSubscript (IntV i)) mid2 = (res,mid2) /\
      (inside ==> target_ptr_ok cenv child r G3 tn3 t3 /\
                  write_target_location_mods cenv cx (SubscriptTarget bt e) mid2 child vt r G3 t3)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `valid_horizon cx st0 H0 _` kall_tac >>
     qpat_x_assum `Abbrev (nw = _)`
       (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all write_array_immutable_extend_mods >>
     simp[LET_THM, Abbr `res`, Abbr `child`, Abbr `inside`]) >>
  qpat_x_assum `i = if _ then _ else _` SUBST_ALL_TAC >>
  irule write_array_finish_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G3`,`n2w (off+k)`,`iw`,`LocCode`,`nw`,`res`,`t3`,`tn3`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ (inside ==> _)`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `Abbrev (inside <=> _)`
    (fn th => once_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  Cases_on `inside` >> simp[Abbr `res`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >> fs[]
QED
