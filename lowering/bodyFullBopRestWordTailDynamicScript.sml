Theory bodyFullBopRestWordTailDynamic
Ancestors
  bodyFullBopRestWordTailRep bodyFullBopRestWordFullControl
  bodyFullBopRestWordLoads bodyFullBopRestWordCtor
  bodyFullBopRestWordCtorHeader bodyFullBopRestWordTailFrame
  bodyPtrBopInHeaderCode bodyPtrBopInBaseBoundary exprSimBopRestWordBasics
  bodyPtrEnvBuiltinsLen

Theorem rest_word_membership_tail_dynamic_full:
 !DF lo d explicit ctx fn PG cenv cx e es sa sm s0 G0 tn0 tv vv ee u Gu Tu needleop needle av ety bd pbd et is_in out ct guard.
 (?cap. bd = Dynamic cap) /\
 compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
 fn_has_code sm ct fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
 local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. needleop = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
 is_word_type ety /\ expr_type e = ArrayT ety bd /\ post_value_type cenv e = ArrayT ety pbd /\
 (case bd of Fixed n => pbd = Fixed n | Dynamic cap => ?pcap. pbd = Dynamic pcap) /\
 (case bd of Fixed n => n | Dynamic cap => cap) < dimword (:256) /\
 ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
 (!H. guard H ==>
   read_result cx tv ee = (INL (ArrayV av),ee) /\
   evaluate_type (get_tenv cx) ety = SOME et /\
   evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et pbd) /\
   value_has_type (ArrayTV et bd) (ArrayV av) /\ value_has_type et needle /\
   eval_operand needleop u = SOME (typed_val_to_w256 et needle) /\
   op_prov (Gu H) needleop = NONE /\ op_taint (Tu H) needleop = {} /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
   alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
   ghost_inv_at (DF H) lo d cenv cx ee (Gu H) (Tu H) u /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gu H) (Tu H) u /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gu H) u) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gu H) u) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 (Gu H) (Tu H)) ==>
 ?t Gt Tt. !H. guard H ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
     (u,Gu H,Tu H) [] (OK t,Gt H,Tt H) /\
   membership_loop_frame sm (Gu H) (Tu H) u (Gt H) (Tt H) t /\
   ~t.vs_halted /\ t.vs_current_bb = ct.cs_current_bb /\
   t.vs_inst_idx = LENGTH ct.cs_current_insts /\
   alloca_history fn t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv t /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
   ghost_inv_at (DF H) lo d cenv cx ee (Gt H) (Tt H) t /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gt H) (Tt H) t /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) t = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside (Tt H).t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gt H) t) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gt H) t) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 (Gt H) (Tt H) /\
   eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
   op_prov (Gt H) needleop = NONE /\ op_taint (Tt H) needleop = {} /\
   eval_operand out t = SOME (bool_to_word
     (if is_in then evaluate_in_array (ArrayTV et bd) needle av
      else ~evaluate_in_array (ArrayTV et bd) needle av)) /\
   op_prov (Gt H) out = NONE /\ op_taint (Tt H) out = {}
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?H. guard H`
  >- suspend "dynamic_execution" >>
  qexistsl_tac [`u`, `Gu`, `Tu`] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[dynamic_execution]:
  drule_all rest_word_membership_tail_clean_reads >> strip_tac >>
  gvs[] >>
  qabbrev_tac `ws = GENLIST (\i. typed_val_to_w256 et
    (THE (array_index (ArrayTV et (Dynamic cap)) av (&i))))
    (array_length (ArrayTV et (Dynamic cap)) av)` >>
  suspend "dynamic_header"
QED

Resume rest_word_membership_tail_dynamic_full[dynamic_header]:
  `vv_holds cenv cx (ArrayT ety (Dynamic pcap)) tv vv ee u /\
   vv_at cenv cx (ArrayT ety (Dynamic pcap)) sa sm ee tv vv u /\
   ptr_vv_ok cx (ArrayT ety (Dynamic pcap)) tv vv ee (Gu H) (Tu H) u` by
    (qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
      (drule_then strip_assume_tac) >> gvs[loweringPostsTheory.vv_post_def]) >>
  `?nv loc. vv_operand nv = vv_operand vv /\ vv_location nv = SOME loc /\
    loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
    loc <> LocCalldata /\
    compile_var_array_membership cenv needleop nv
      (ArrayT ety (Dynamic cap)) is_in sm = (out,ct)` by
    (Cases_on `vv`
     >- (rename1 `StackValue ann arr_op` >>
         qexistsl_tac [`LocatedValue (ArrayT ety (Dynamic cap)) (mk_ptr arr_op LocMemory)`, `LocMemory`] >>
         simp[contextTheory.vv_operand_def, contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
         qpat_x_assum `compile_var_array_membership _ _ (StackValue _ _) _ _ _ = _` mp_tac >>
         simp[membership_dynamic_compile_split, contextTheory.vv_operand_def,
           contextTheory.vv_location_def]) >>
     rename1 `LocatedValue ann p` >>
     qexistsl_tac [`LocatedValue ann p`, `p.ptr_location`] >>
     simp[contextTheory.vv_operand_def, contextTheory.vv_location_def] >>
     Cases_on `p.ptr_location` >> fs[loweringPostsTheory.vv_holds_def]) >>
  suspend "normalized_header"
QED

Resume rest_word_membership_tail_dynamic_full[normalized_header]:
  qpat_assum `!H'. guard H' ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `?w. eval_operand (vv_operand vv) u = SOME w` by
    (Cases_on `vv_location vv` >> fs[] >>
     rename1 `vv_location vv = SOME lc` >>
     Cases_on `lc` >> fs[] >>
     metis_tac[]) >>
  suspend "header_endpoint"
QED

Resume rest_word_membership_tail_dynamic_full[header_endpoint]:
  `?len sl sh Gh Th.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (vv_operand nv) sm = (len,sl) /\
    compile_array_membership_loop needleop (vv_operand nv) len
      (elem_size_in_location cenv loc ety) (word_scale loc)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) (SOME cap) is_in sl = (out,ct) /\
    (!h. guard h ==>
      gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (u,Gu h,Tu h) [] (OK sh,Gh h,Th h) /\
      membership_loop_frame sm (Gu h) (Tu h) u (Gh h) (Th h) sh /\
      eval_operand len sh = SOME (n2w (LENGTH ws)) /\
      op_prov (Gh h) len = NONE /\ op_taint (Th h) len = {} /\
      ~sh.vs_halted /\ allocas_from lo sh /\ sh.vs_current_bb = sl.cs_current_bb /\
      sh.vs_inst_idx = LENGTH sl.cs_current_insts)` by
    suspend "header_apply" >>
  suspend "bounded_search"
QED

Resume rest_word_membership_tail_dynamic_full[header_apply]:
  Cases_on `cenv.ce_is_ctor /\ loc = LocCode`
  >- suspend "ctor_header" >>
  irule rest_word_membership_header_joint_indexed >>
  reverse conj_tac
  >- (qpat_x_assum `loc = case _ of _ => _ | _ => _` kall_tac >>
      simp[] >> conj_tac >- metis_tac[] >> Cases_on `loc` >> simp[] >> metis_tac[]) >>
  qexists_tac `w` >> gen_tac >> disch_tac >>
  suspend "runtime_header_inputs"
QED

Resume rest_word_membership_tail_dynamic_full[runtime_header_inputs]:
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!H'. guard H' ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `allocas_from lo u` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  qpat_x_assum `!H. guard H ==> read_result _ _ _ = _ /\ _` kall_tac >>
  qpat_x_assum `!H'. guard H' ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _` kall_tac >>
  `LENGTH ws = array_length (ArrayTV et (Dynamic cap)) av` by
    simp[Abbr `ws`] >>
  simp[] >>
  Cases_on `vv_location vv`
  >- (fs[] >>
      `?p. vv_operand vv = Var p /\ ptr_covers (Gu H') (Tu H') p u 32` by
        (irule sized_ptr_val_header_covers >>
         conj_tac >- metis_tac[] >>
         qexistsl_tac [`cx`, `ArrayTV et (Dynamic pcap)`,
           `ArrayT ety (Dynamic pcap)`, `ArrayV av`] >>
         simp[bodyPtrDefsTheory.ptr_val_ok_def,
           compileEnvTheory.is_word_type_def,
           vyperTypeSystemTheory.is_sized_type_def]) >>
      gvs[valueEncodingTheory.type_memory_size_def]) >>
  rename1 `vv_location vv = SOME lc` >>
  Cases_on `lc` >> fs[]
  >- (`?p. vv_operand vv = Var p /\ ptr_covers (Gu H') (Tu H') p u 32` by
        (irule sized_ptr_val_header_covers >>
         conj_tac >- metis_tac[] >>
         qexistsl_tac [`cx`, `ArrayTV et (Dynamic pcap)`,
           `ArrayT ety (Dynamic pcap)`, `ArrayV av`] >>
         simp[bodyPtrDefsTheory.ptr_val_ok_def,
           compileEnvTheory.is_word_type_def,
           vyperTypeSystemTheory.is_sized_type_def]) >>
      gvs[valueEncodingTheory.type_memory_size_def])
  >- (qpat_x_assum `!tr. _ ==> ?w. _` (qspec_then `F` mp_tac) >>
      simp[] >> strip_tac >> gvs[]) 
  >- (qpat_x_assum `!tr. _ ==> ?w. _` (qspec_then `T` mp_tac) >>
      simp[] >> strip_tac >> gvs[]) >>
  gvs[valueEncodingTheory.type_memory_size_def]
QED

Resume rest_word_membership_tail_dynamic_full[ctor_header]:
  qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode` strip_assume_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  irule rest_word_membership_ctor_header_full_joint >>
  reverse conj_tac
  >- (simp[] >> metis_tac[]) >>
  qexists_tac `w` >> gen_tac >> disch_tac >>
  suspend "ctor_header_inputs"
QED

Resume rest_word_membership_tail_dynamic_full[ctor_header_inputs]:
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!H'. guard H' ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_x_assum `!H. guard H ==> read_result _ _ _ = _ /\ _` kall_tac >>
  qpat_x_assum `!H'. guard H' ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _` kall_tac >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `LENGTH ws = array_length (ArrayTV et (Dynamic cap)) av` by
    simp[Abbr `ws`] >>
  fs[] >>
  `lo <> 0` by decide_tac >>
  gvs[]
QED

Resume rest_word_membership_tail_dynamic_full[bounded_search]:
  `sm.cs_next_var <= sl.cs_next_var` by
    metis_tac[exprSafeOperandBuiltinsTheory.compile_ptr_load_next_var] >>
  `cs_extends sm sl` by
    (mp_tac externalEntryShapeTheory.compile_ptr_load_labels >>
     disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `loc`, `vv_operand nv`, `sm`, `\l. T`] mp_tac) >>
     simp[]) >>
  `cs_extends sl ct` by metis_tac[bodyPtrBopInBoundedLayoutTheory.membership_bounded_loop_extends] >>
  `fn_has_code sl ct fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!x. len = Var x ==> not_fresh_at sl x` by
    metis_tac[fragFuelExprHelpersTheory.compile_ptr_load_var,
      loweringStateRelDefsTheory.not_fresh_at_def, fragFuelTheory.var_below_def] >>
  suspend "bounded_control"
QED

Resume rest_word_membership_tail_dynamic_full[bounded_control]:
  `?t gf tf. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (sh,Gh H,Th H) [] (OK t,gf H,tf H) /\
    membership_loop_frame sl (Gh H) (Th H) sh (gf H) (tf H) t /\
    eval_operand out t = SOME (bool_to_word
      (if is_in then MEM (typed_val_to_w256 et needle) ws
       else ~MEM (typed_val_to_w256 et needle) ws)) /\
    op_prov (gf H) out = NONE /\ op_taint (tf H) out = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts` by
      suspend "bounded_run" >>
  suspend "dynamic_post"
QED

Resume rest_word_membership_tail_dynamic_full[bounded_run]:
  irule rest_word_membership_loop_full_horizon_joint_all >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- ( `LENGTH ws = array_length (ArrayTV et (Dynamic cap)) av` by simp[Abbr `ws`] >> simp[]) >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`vv_operand nv`, `SOME cap`, `cenv.ce_imm_alloca`,
    `cenv.ce_is_ctor`, `len`, `loc`, `needleop`, `word_scale loc`,
    `elem_size_in_location cenv loc ety`] >>
  suspend "bounded_run_premises"
QED

Resume rest_word_membership_tail_dynamic_full[bounded_run_premises]:
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!h. guard h ==> array_length _ _ <= _ /\ _`
        (qspec_then `H'` (drule_then strip_assume_tac)) >>
      qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H'` (drule_then strip_assume_tac)) >>
      qpat_x_assum `!sl t Gt Tt. _`
        (qspecl_then [`sm`, `sh`, `Gh H'`, `Th H'`] mp_tac) >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- suspend "bounded_callback" >>
  `LENGTH ws = array_length (ArrayTV et (Dynamic cap)) av` by simp[Abbr `ws`] >>
  simp[]
QED

Resume rest_word_membership_tail_dynamic_full[bounded_callback]:
  Cases_on `cenv.ce_is_ctor /\ loc = LocCode`
  >- suspend "bounded_ctor_callback" >>
  suspend "bounded_runtime_callback"
QED

Resume rest_word_membership_tail_dynamic_full[bounded_ctor_callback]:
  qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode` strip_assume_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `LocCode = case vv_location vv of NONE => LocMemory | SOME l => l` kall_tac >>
  Cases_on `IS_SOME cenv.ce_imm_alloca`
  >- (qpat_assum `cenv.ce_is_ctor` (fn th =>
        qpat_assum `IS_SOME cenv.ce_imm_alloca` (fn wh =>
          simp[NoAsms, compileEnvTheory.word_scale_def, th, wh])) >>
      rpt gen_tac >> strip_tac >>
      irule (SRULE [] (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
        (Q.INST [`q` |-> `2`, `delta` |-> `1`, `width` |-> `2`]
          rest_word_membership_ctor_load_joint_indexed))) >>
      suspend "bounded_ctor_inputs_some") >>
  qpat_assum `cenv.ce_is_ctor` (fn th =>
    qpat_assum `~IS_SOME cenv.ce_imm_alloca` (fn wh =>
      simp[NoAsms, compileEnvTheory.word_scale_def, th, wh])) >>
  rpt gen_tac >> strip_tac >>
  irule (SRULE [] (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`q` |-> `2`, `delta` |-> `1`, `width` |-> `1`]
      rest_word_membership_ctor_load_joint_indexed))) >>
  suspend "bounded_ctor_inputs_none"
QED

Resume rest_word_membership_tail_dynamic_full[bounded_ctor_inputs_some]:
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  qexistsl_tac [`\i. w + n2w (32 + elem_size_in_location cenv LocCode ety * i)`,
    `vv_operand nv`, `SOME cap`, `w`, `cenv.ce_imm_alloca`, `is_in`,
    `len`, `needleop`, `out`, `ct`, `32`, `elem_size_in_location cenv LocCode ety`] >>
  conj_tac >- suspend "ctor_some_read_inputs" >>
  simp[compileEnvTheory.word_scale_def] >>
  conj_tac >- (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def, compileEnvTheory.word_scale_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[ctor_some_read_inputs]:
  gen_tac >> disch_tac >>
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `LENGTH ws = array_length (ArrayTV et (Dynamic cap)) av` by simp[Abbr `ws`] >>
  fs[] >>
  suspend "ctor_some_frame_reads"
QED

Resume rest_word_membership_tail_dynamic_full[ctor_some_frame_reads]:
  qpat_x_assum `!sl t Gt Tt. _`
    (qspecl_then [`sm`, `sh`, `Gh H'`, `Th H'`] mp_tac) >>
  simp[] >> strip_tac >>
  `lo <= u.vs_alloca_next` by
    (qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
      (qspec_then `H'` (drule_then strip_assume_tac)) >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `lo <= sh.vs_alloca_next` by
    (qpat_assum `membership_loop_frame sm (Gu H') _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> strip_tac >>
     qpat_x_assum `sh = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      drule bodyPtrBopInLoopContractTheory.membership_loop_frame_operand >>
      disch_then (qspec_then `ib` mp_tac) >>
      impl_tac >- metis_tac[] >>
      strip_tac >> fs[] >> metis_tac[]) >>
  suspend "ctor_some_elements"
QED

Resume rest_word_membership_tail_dynamic_full[ctor_some_elements]:
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `sh.vs_memory = u.vs_memory /\ (Th H').t_mem = (Tu H').t_mem` by
    (qpat_assum `membership_loop_frame sm (Gu H') _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> strip_tac >>
     qpat_x_assum `sh = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[] >>
  suspend "ctor_some_element_address"
QED

Resume rest_word_membership_tail_dynamic_full[ctor_some_element_address]:
  gen_tac >> disch_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?w. _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_assum `!j. j < array_length _ _ ==> 32 * j + _ <= lo /\ _`
    (qspec_then `i'` (drule_then strip_assume_tac)) >>
  `w2n w + (32 * i' + 32) < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then SUBST1_TAC >>
  `w2n w + (32 * i' + 32) = 32 * i' + (w2n w + 32)` by decide_tac >>
  simp[Abbr `ws`, listTheory.EL_GENLIST] >>
  fs[venomStateTheory.mload_def]
QED

Resume rest_word_membership_tail_dynamic_full[bounded_ctor_inputs_none]:
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  qexistsl_tac [`\i. w + n2w (32 + elem_size_in_location cenv LocCode ety * i)`,
    `vv_operand nv`, `SOME cap`, `w`, `cenv.ce_imm_alloca`, `is_in`,
    `len`, `needleop`, `out`, `ct`, `32`, `elem_size_in_location cenv LocCode ety`] >>
  conj_tac >- suspend "ctor_none_read_inputs" >>
  simp[compileEnvTheory.word_scale_def] >>
  conj_tac >- (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def, compileEnvTheory.word_scale_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[ctor_none_read_inputs]:
  gen_tac >> disch_tac >>
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `LENGTH ws = array_length (ArrayTV et (Dynamic cap)) av` by simp[Abbr `ws`] >>
  fs[] >>
  suspend "ctor_none_frame_reads"
QED

Resume rest_word_membership_tail_dynamic_full[ctor_none_frame_reads]:
  qpat_x_assum `!sl t Gt Tt. _`
    (qspecl_then [`sm`, `sh`, `Gh H'`, `Th H'`] mp_tac) >>
  simp[] >> strip_tac >>
  `lo <= u.vs_alloca_next` by
    (qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
      (qspec_then `H'` (drule_then strip_assume_tac)) >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `lo <= sh.vs_alloca_next` by
    (qpat_assum `membership_loop_frame sm (Gu H') _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> strip_tac >>
     qpat_x_assum `sh = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- simp[] >>
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `sh.vs_memory = u.vs_memory /\ (Th H').t_mem = (Tu H').t_mem` by
    (qpat_assum `membership_loop_frame sm (Gu H') _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> strip_tac >>
     qpat_x_assum `sh = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[] >>
  suspend "ctor_none_element_address"
QED

Resume rest_word_membership_tail_dynamic_full[ctor_none_element_address]:
  gen_tac >> disch_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?w. _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_assum `!j. j < array_length _ _ ==> 32 * j + _ <= lo /\ _`
    (qspec_then `i'` (drule_then strip_assume_tac)) >>
  `w2n w + (32 * i' + 32) < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then SUBST1_TAC >>
  `w2n w + (32 * i' + 32) = 32 * i' + (w2n w + 32)` by decide_tac >>
  simp[Abbr `ws`, listTheory.EL_GENLIST] >>
  fs[venomStateTheory.mload_def]
QED

Resume rest_word_membership_tail_dynamic_full[bounded_runtime_callback]:
  rpt gen_tac >> strip_tac >>
  suspend "runtime_prefix_and_read"
QED

Resume rest_word_membership_tail_dynamic_full[runtime_prefix_and_read]:
  `compile_array_membership_loop needleop (vv_operand nv) len
     (elem_size_in_location cenv loc ety) (word_scale loc)
     (compile_ptr_load F cenv.ce_imm_alloca loc) (SOME cap) is_in sl = (out,ct)` by
    (`compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc =
       compile_ptr_load F cenv.ce_imm_alloca loc` by
       (simp[FUN_EQ_THM] >> Cases_on `loc` >> fs[contextTheory.compile_ptr_load_def]) >>
     metis_tac[]) >>
  `?sp gp tp. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG)
      (s,Gs h,Ts h) [] (OK sp,gp h,tp h) /\
    membership_loop_frame sl (Gh h) (Th h) sh (gp h) (tp h) sp /\
    membership_loop_registers sl i 0w (gp h) (tp h) sp /\
    ~sp.vs_halted /\ allocas_from lo sp /\
    sp.vs_current_bb = s.vs_current_bb /\
    sp.vs_inst_idx = 2 + (if 0 < word_scale loc then 1 else 0) /\
    lookup_var ("%" ++ toString (sl.cs_next_var+6+(if 0 < word_scale loc then 1 else 0))) sp =
      SOME (w+n2w (word_scale loc+elem_size_in_location cenv loc ety*i)) /\
    FLOOKUP (gp h) ("%" ++ toString (sl.cs_next_var+6+(if 0 < word_scale loc then 1 else 0))) =
      op_prov (Gh h) (vv_operand nv) /\
    op_taint (tp h) (Var ("%" ++ toString (sl.cs_next_var+6+(if 0 < word_scale loc then 1 else 0)))) = {}` by
      suspend "runtime_prefix" >>
  suspend "runtime_read"
QED

Resume rest_word_membership_tail_dynamic_full[runtime_prefix]:
  irule rest_word_membership_runtime_address_operand_joint_bounded_indexed >>
  conj_tac >- suspend "runtime_prefix_guard" >>
  conj_tac >- (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  simp[] >>
  metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_prefix_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  simp[] >>
  suspend "runtime_prefix_operand"
QED

Resume rest_word_membership_tail_dynamic_full[dynamic_post]:
  `!H. guard H ==> membership_loop_frame sm (Gu H) (Tu H) u (gf H) (tf H) t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
       (qspec_then `H'` (drule_then strip_assume_tac)) >>
     qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sh,_,_) _ _ /\ _`
       (qspec_then `H'` (drule_then strip_assume_tac)) >>
     irule bodyPtrBopInLoopContractTheory.membership_loop_frame_source >>
     qexistsl_tac [`Gh H'`, `sl`, `sh`, `Th H'`] >>
     simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qexistsl_tac [`t`, `gf`, `tf`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sh,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  conj_tac >- metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  conj_tac >- metis_tac[] >>
  simp[] >>
  suspend "dynamic_restore"
QED

Resume rest_word_membership_tail_dynamic_full[dynamic_restore]:
  `!h. guard h ==>
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\
    membership_loop_frame sm (Gu h) (Tu h) u (gf h) (tf h) t /\
    alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    vv_post h ctx fn cenv cx e es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
    ghost_inv_at (DF h) lo d cenv cx ee (Gu h) (Tu h) u /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gu h) (Tu h) u /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside (Tu h).t_mem u.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
    (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gu h) u) /\
    (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gu h) u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 (Gu h) (Tu h)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sh,_,_) _ _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     simp[] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?val. _`
       (drule_then strip_assume_tac) >>
     gvs[] ) >>
  drule_all rest_word_membership_tail_full_frame >>
  strip_tac >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_prefix_operand]:
  qpat_assum `!sl t Gt Tt. sm.cs_next_var <= sl.cs_next_var /\ _ ==> _`
    (qspecl_then [`sm`, `sh`, `Gh H'`, `Th H'`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `vv_location vv`
  >- (qpat_x_assum `_ \/ _ ==> ?w. eval_operand _ u = _ /\ op_taint (Tu H') _ = _ /\ _` mp_tac >>
      simp[] >> metis_tac[]) >>
  rename1 `vv_location vv = SOME vl` >>
  Cases_on `vl`
  >- (qpat_x_assum `_ \/ _ ==> ?w. eval_operand _ u = _ /\ op_taint (Tu H') _ = _ /\ _` mp_tac >>
      simp[] >> metis_tac[])
  >- (qpat_x_assum `!tr. _ = SOME (if tr then _ else _) ==> ?w. eval_operand _ u = _ /\ op_taint (Tu H') _ = _ /\ _`
        (qspec_then `F` mp_tac) >> simp[] >> metis_tac[])
  >- (qpat_x_assum `!tr. _ = SOME (if tr then _ else _) ==> ?w. eval_operand _ u = _ /\ op_taint (Tu H') _ = _ /\ _`
        (qspec_then `T` mp_tac) >> simp[] >> metis_tac[])
  >- (qpat_x_assum `~cenv.ce_is_ctor /\ _ ==> ?w. eval_operand _ u = _ /\ op_taint (Tu H') _ = _ /\ _` mp_tac >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `loc = case _ of NONE => _ | SOME l => l` mp_tac >> simp[]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_read]:
  simp[] >> Cases_on `loc`
  >- suspend "runtime_memory_read"
  >- suspend "runtime_storage_read"
  >- suspend "runtime_transient_read"
  >- suspend "runtime_code_read"
  >> fs[]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_storage_read]:
  `?t gt tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (sp,gp h,tp h) [] (OK t,gt h,tt h) /\
    membership_loop_frame sl (Gh h) (Th h) sh (gt h) (tt h) t /\
    membership_loop_registers sl i 0w (gt h) (tt h) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sp.vs_current_bb /\
    t.vs_inst_idx = 4 /\
    lookup_var ("%" ++ toString (sl.cs_next_var+8)) t = SOME (sload (w+n2w (i+1)) sp) /\
    FLOOKUP (gt h) ("%" ++ toString (sl.cs_next_var+8)) = NONE /\
    op_taint (tt h) (Var ("%" ++ toString (sl.cs_next_var+8))) = {}` by
    suspend "storage_load" >>
  suspend "storage_finish"
QED

Resume rest_word_membership_tail_dynamic_full[storage_load]:
  simp[NoAsms, stringTheory.STRCAT] >>
  irule (rest_word_membership_slot_read_joint_bounded_indexed
    |> Q.INST [`tr` |-> `F`, `delta` |-> `1`]
    |> PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    |> SRULE []) >>
  simp[] >>
  conj_tac >- suspend "storage_guard" >>
  qexistsl_tac [`vv_operand nv`, `cap`, `cenv.ce_imm_alloca`, `is_in`, `len`, `needleop`, `out`, `ct`, `word_scale LocStorage`, `elem_size_in_location cenv LocStorage ety`] >>
  fs[compileEnvTheory.word_scale_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[storage_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame sl _ _ sh _ _ s /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[compileEnvTheory.word_scale_def,
     exprSimBopRestWordTailTheory.rest_word_word_stride,
     stringTheory.STRCAT] >>
  qpat_assum `!h. guard h ==> (!ib. cenv.ce_imm_alloca = SOME ib ==> _) /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocStorage` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then _ else _) ==> _`
    (qspec_then `F` mp_tac) >> simp[] >> strip_tac >>
  fs[Abbr `ws`, bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[storage_finish]:
  qexistsl_tac [`t`, `gt`, `tt`] >> gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sp,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocStorage` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `LocStorage = case vv_location vv of NONE => LocMemory | SOME l => l` kall_tac >>
  simp[compileEnvTheory.word_scale_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> metis_tac[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= cap /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocStorage` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then _ else _) ==> _`
    (qspec_then `F` mp_tac) >> simp[] >> strip_tac >>
  fs[Abbr `ws`, listTheory.EL_GENLIST,
     bodyPtrBopInLoopContractTheory.membership_loop_frame_def, venomStateTheory.sload_def] >>> NTH_GOAL (metis_tac[]) 1 >>
  qpat_x_assum `!tr. (if tr then LocTransient else LocStorage) = LocStorage ==> _`
    (qspec_then `F` mp_tac) >> simp[] >> strip_tac >>
  fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
     venomStateTheory.contract_storage_def] >>
  qpat_x_assum `sp = _` (fn th => simp[Once th] >> simp[Once th]) >>
  qpat_x_assum `sh = _` (fn th => simp[Once th] >> simp[Once th]) >>
  simp[]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_transient_read]:
  `?t gt tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (sp,gp h,tp h) [] (OK t,gt h,tt h) /\
    membership_loop_frame sl (Gh h) (Th h) sh (gt h) (tt h) t /\
    membership_loop_registers sl i 0w (gt h) (tt h) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sp.vs_current_bb /\
    t.vs_inst_idx = 4 /\
    lookup_var ("%" ++ toString (sl.cs_next_var+8)) t = SOME (tload (w+n2w (i+1)) sp) /\
    FLOOKUP (gt h) ("%" ++ toString (sl.cs_next_var+8)) = NONE /\
    op_taint (tt h) (Var ("%" ++ toString (sl.cs_next_var+8))) = {}` by
    suspend "transient_load" >>
  suspend "transient_finish"
QED

Resume rest_word_membership_tail_dynamic_full[transient_load]:
  simp[NoAsms, stringTheory.STRCAT] >>
  irule (rest_word_membership_slot_read_joint_bounded_indexed
    |> Q.INST [`tr` |-> `T`, `delta` |-> `1`]
    |> PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    |> SRULE []) >>
  simp[] >>
  conj_tac >- suspend "transient_guard" >>
  qexistsl_tac [`vv_operand nv`, `cap`, `cenv.ce_imm_alloca`, `is_in`, `len`, `needleop`, `out`, `ct`, `word_scale LocTransient`, `elem_size_in_location cenv LocTransient ety`] >>
  fs[compileEnvTheory.word_scale_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[transient_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame sl _ _ sh _ _ s /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[compileEnvTheory.word_scale_def,
     exprSimBopRestWordTailTheory.rest_word_word_stride,
     stringTheory.STRCAT] >>
  qpat_assum `!h. guard h ==> (!ib. cenv.ce_imm_alloca = SOME ib ==> _) /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocTransient` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then _ else _) ==> _`
    (qspec_then `T` mp_tac) >> simp[] >> strip_tac >>
  fs[Abbr `ws`, bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[transient_finish]:
  qexistsl_tac [`t`, `gt`, `tt`] >> gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sp,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocTransient` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `LocTransient = case vv_location vv of NONE => LocMemory | SOME l => l` kall_tac >>
  simp[compileEnvTheory.word_scale_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> metis_tac[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= cap /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then _ else _) ==> _`
    (qspec_then `T` mp_tac) >> simp[] >> strip_tac >>
  fs[Abbr `ws`, listTheory.EL_GENLIST,
     bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
     venomStateTheory.tload_def, venomStateTheory.contract_transient_def] >>
  qpat_x_assum `sp = _` (fn th => simp[Once th] >> simp[Once th]) >>
  qpat_x_assum `sh = _` (fn th => simp[Once th] >> simp[Once th]) >>
  metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_code_read]:
  `?t gt tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (sp,gp h,tp h) [] (OK t,gt h,tt h) /\
    membership_loop_frame sl (Gh h) (Th h) sh (gt h) (tt h) t /\
    membership_loop_registers sl i 0w (gt h) (tt h) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sp.vs_current_bb /\
    t.vs_inst_idx = 4 /\
    lookup_var ("%" ++ toString (sl.cs_next_var+8)) t = SOME
      (word_of_bytes T (0w:bytes32) (TAKE 32 (DROP (w2n (w+n2w (32*i+32))) sp.vs_data_section ++ REPLICATE 32 0w))) /\
    FLOOKUP (gt h) ("%" ++ toString (sl.cs_next_var+8)) = NONE /\
    op_taint (tt h) (Var ("%" ++ toString (sl.cs_next_var+8))) = {}` by
    suspend "code_load" >>
  suspend "code_finish"
QED

Resume rest_word_membership_tail_dynamic_full[code_load]:
  simp[NoAsms, stringTheory.STRCAT] >>
  irule (rest_word_membership_code_read_joint_bounded_indexed
    |> Q.INST [`delta` |-> `1`]
    |> PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    |> SRULE []) >>
  simp[] >>
  conj_tac >- suspend "code_bound" >>
  conj_tac >- suspend "code_guard" >>
  qexistsl_tac [`vv_operand nv`, `cap`, `cenv.ce_imm_alloca`, `is_in`, `len`, `needleop`, `out`, `ct`, `word_scale LocCode`, `elem_size_in_location cenv LocCode ety`] >>
  fs[compileEnvTheory.word_scale_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[code_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame sl _ _ sh _ _ s /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[compileEnvTheory.word_scale_def,
     exprSimBopRestWordTailTheory.rest_word_word_stride,
     stringTheory.STRCAT] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[code_bound]:
  `vv_location vv = SOME LocCode` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= cap /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `~cenv.ce_is_ctor` by fs[] >>
  qpat_x_assum `~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> ?w. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `LocCode = case vv_location vv of NONE => LocMemory | SOME l => l` kall_tac >>
  fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Dynamic pcap)) av` by
    (fs[Abbr `ws`, vyperValueOperationTheory.array_length_def]) >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >>
  simp[] >> strip_tac >>
  `w2n (w+n2w (32*i+32)) <= w2n w + (32*i+32)` by
    (CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV
       (REWR_CONV (GSYM wordsTheory.n2w_w2n))))) >>
     simp[NoAsms, wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_LESS_EQ]) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  qpat_x_assum `sp = _` (fn th => simp[Once th]) >>
  qpat_x_assum `sh = _` (fn th => simp[Once th]) >>
  gvs[] >> decide_tac
QED

Resume rest_word_membership_tail_dynamic_full[code_finish]:
  qexistsl_tac [`t`, `gt`, `tt`] >> gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sp,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocCode` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `LocCode = case vv_location vv of NONE => LocMemory | SOME l => l` kall_tac >>
  simp[compileEnvTheory.word_scale_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> metis_tac[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ <= cap /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame sl _ _ sh _ _ s /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[Abbr `ws`, listTheory.EL_GENLIST,
     bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  `sp.vs_data_section = u.vs_data_section` by
    (qpat_x_assum `sp = _` (fn th => simp[Once th]) >>
     qpat_x_assum `sh = _` (fn th => simp[Once th])) >>
  fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def]
QED

Resume rest_word_membership_tail_dynamic_full[runtime_memory_read]:
  `?t gt tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (sp,gp h,tp h) [] (OK t,gt h,tt h) /\
    membership_loop_frame sl (Gh h) (Th h) sh (gt h) (tt h) t /\
    membership_loop_registers sl i 0w (gt h) (tt h) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sp.vs_current_bb /\
    t.vs_inst_idx = 4 /\
    lookup_var ("%" ++ toString (sl.cs_next_var+8)) t = SOME (mload (w2n (w+n2w (32*i+32))) sp) /\
    FLOOKUP (gt h) ("%" ++ toString (sl.cs_next_var+8)) = NONE /\
    op_taint (tt h) (Var ("%" ++ toString (sl.cs_next_var+8))) = {}` by
    suspend "memory_load" >>
  suspend "memory_finish"
QED

Resume rest_word_membership_tail_dynamic_full[memory_load]:
  simp[NoAsms, stringTheory.STRCAT] >>
  irule (rest_word_membership_memory_read_joint_bounded_indexed
    |> Q.INST [`delta` |-> `1`]
    |> PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    |> SRULE []) >>
  simp[] >>
  conj_tac >- suspend "memory_bound" >>
  conj_tac >- suspend "memory_guard" >>
  qexistsl_tac [`vv_operand nv`, `cap`, `cenv.ce_imm_alloca`, `is_in`, `len`, `needleop`, `out`, `ct`, `word_scale LocMemory`, `elem_size_in_location cenv LocMemory ety`] >>
  fs[compileEnvTheory.word_scale_def] >> metis_tac[]
QED

Resume rest_word_membership_tail_dynamic_full[memory_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame sl _ _ sh _ _ s /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[compileEnvTheory.word_scale_def,
     exprSimBopRestWordTailTheory.rest_word_word_stride,
     stringTheory.STRCAT] >>
  suspend "memory_guard_coverage"
QED

Resume rest_word_membership_tail_dynamic_full[memory_guard_coverage]:
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!h. guard h ==> (!ib. cenv.ce_imm_alloca = SOME ib ==> _) /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[] >>
  `?p. vv_operand vv = Var p /\ ptr_covers (Gu H') (Tu H') p u 32` by
    (irule sized_ptr_val_header_covers >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`cx`, `ArrayTV et (Dynamic pcap)`,
       `ArrayT ety (Dynamic pcap)`, `ArrayV av`] >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def,
       compileEnvTheory.is_word_type_def,
       vyperTypeSystemTheory.is_sized_type_def]) >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Dynamic pcap)) av` by
    fs[Abbr `ws`, vyperValueOperationTheory.array_length_def] >>
  `val_wf (ArrayTV et (Dynamic pcap)) (ArrayV av)` by
    (fs[loweringPostsTheory.expr_val_at_def, compileEnvTheory.is_word_type_def]) >>
  `32 + i * 32 + 32 <= type_memory_size (ArrayTV et (Dynamic pcap))` by
    (qpat_x_assum `val_wf _ _` mp_tac >>
     qpat_x_assum `i < array_length (ArrayTV et (Dynamic pcap)) av` mp_tac >>
     Cases_on `av` >>
     simp[NoAsms, valueEncodingDefsTheory.val_wf_def,
         vyperValueOperationTheory.array_length_def,
         valueEncodingTheory.type_memory_size_def] >>
     simp[Once (GSYM arithmeticTheory.MULT_COMM)] >> decide_tac) >>
  suspend "memory_coverage_arith"
QED

Resume rest_word_membership_tail_dynamic_full[memory_coverage_arith]:
  markerLib.RESUME_TAC >>
  fs[] >>
  `type_memory_size (ArrayTV et (Dynamic pcap)) + w2n w <= u.vs_alloca_next` by
    (qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `w2n w + (32*i+32) < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then SUBST1_TAC >>
  suspend "memory_coverage_transport"
QED

Resume rest_word_membership_tail_dynamic_full[memory_coverage_transport]:
  markerLib.RESUME_TAC >>
  (conj_tac >- suspend "memory_pointer_transport") >>
  `(tp H').t_mem = (Tu H').t_mem` by
    (qpat_x_assum `membership_loop_frame sl _ _ sh _ _ sp` mp_tac >>
     qpat_x_assum `membership_loop_frame sm _ _ u _ _ sh` mp_tac >>
     simp[NoAsms, bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     metis_tac[]) >>
  simp[] >>
  `i < array_length (ArrayTV et (Dynamic cap)) av` by fs[Abbr `ws`] >>
  `32 * i + (w2n w + 32) = w2n w + (32*i+32)` by decide_tac >>
  qpat_x_assum `!i'. i' < array_length _ _ ==> mem_word_taint _ _ = {}`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_dynamic_full[memory_pointer_transport]:
  markerLib.RESUME_TAC >>
  `not_fresh_at sm p` by metis_tac[] >>
  `FLOOKUP (Gh H') p = FLOOKUP (Gu H') p` by
    (qpat_assum `membership_loop_frame sm _ _ u _ _ sh` mp_tac >>
     simp[NoAsms, bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> metis_tac[]) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _`
    (mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!off n dst t G' T'. _`
    (qspec_then `32*i+32` mp_tac) >>
  disch_then irule >>
  simp[exprSimBopRestWordTailTheory.rest_word_word_stride,
       compileEnvTheory.word_scale_def,
       ptrDisciplineTheory.op_prov_def] >>
  `i * 32 = 32 * i` by decide_tac >> simp[] >> decide_tac
QED

Resume rest_word_membership_tail_dynamic_full[memory_bound]:
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by
    (Cases_on `vv_location vv` >> fs[]) >>
  fs[] >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Dynamic pcap)) av` by
    fs[Abbr `ws`, vyperValueOperationTheory.array_length_def] >>
  `val_wf (ArrayTV et (Dynamic pcap)) (ArrayV av)` by
    fs[loweringPostsTheory.expr_val_at_def, compileEnvTheory.is_word_type_def] >>
  `32 + i * 32 + 32 <= type_memory_size (ArrayTV et (Dynamic pcap))` by
    (qpat_x_assum `val_wf _ _` mp_tac >>
     qpat_x_assum `i < array_length (ArrayTV et (Dynamic pcap)) av` mp_tac >>
     Cases_on `av` >>
     simp[NoAsms, valueEncodingDefsTheory.val_wf_def,
         vyperValueOperationTheory.array_length_def,
         valueEncodingTheory.type_memory_size_def] >>
     simp[Once (GSYM arithmeticTheory.MULT_COMM)] >> decide_tac) >>
  `type_memory_size (ArrayTV et (Dynamic pcap)) + w2n w <= u.vs_alloca_next` by
    (qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  `sp.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_x_assum `membership_loop_frame sl _ _ sh _ _ sp` mp_tac >>
     qpat_x_assum `membership_loop_frame sm _ _ u _ _ sh` mp_tac >>
     simp[NoAsms, bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `sp = _` (fn th => simp[Once th]) >>
     qpat_x_assum `sh = _` (fn th => simp[Once th])) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `w2n w + (32*i+32) < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
  disch_then SUBST1_TAC >> decide_tac
QED

Resume rest_word_membership_tail_dynamic_full[memory_finish]:
  qexistsl_tac [`t`, `gt`, `tt`] >> gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sp,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  simp[compileEnvTheory.word_scale_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> metis_tac[]) >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `LocMemory = case vv_location vv of NONE => LocMemory | SOME l => l` kall_tac >>
  qpat_assum `!h. guard h ==> array_length _ _ <= cap /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[Abbr `ws`, listTheory.EL_GENLIST,
     compileEnvTheory.word_scale_def] >>
  `sp.vs_memory = u.vs_memory` by
    (qpat_x_assum `membership_loop_frame sl _ _ sh _ _ sp` mp_tac >>
     qpat_x_assum `membership_loop_frame sm _ _ u _ _ sh` mp_tac >>
     simp[NoAsms, bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `sp = _` (fn th => simp[Once th]) >>
     qpat_x_assum `sh = _` (fn th => simp[Once th])) >>
  `mload (w2n (w+n2w (32*i+32))) sp =
    mload (w2n (w+n2w (32*i+32))) u` by
    simp[venomStateTheory.mload_def] >>
  qpat_assum `vv_location vv = _` (fn th => rewrite_tac[th]) >>
  simp[NoAsms, compileEnvTheory.word_scale_def] >>
  qpat_assum `!H. guard H ==> membership_loop_frame sl _ _ sh _ _ s /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  simp[ptrDisciplineTheory.op_prov_def, venomStateTheory.eval_operand_def] >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `val_wf (ArrayTV et (Dynamic pcap)) (ArrayV av)` by
    fs[loweringPostsTheory.expr_val_at_def, compileEnvTheory.is_word_type_def] >>
  `32 + i * 32 + 32 <= type_memory_size (ArrayTV et (Dynamic pcap))` by
    (qpat_x_assum `val_wf _ _` mp_tac >>
     qpat_x_assum `i < array_length (ArrayTV et (Dynamic cap)) av` mp_tac >>
     Cases_on `av` >>
     simp[NoAsms, valueEncodingDefsTheory.val_wf_def,
         vyperValueOperationTheory.array_length_def,
         valueEncodingTheory.type_memory_size_def] >>
     simp[Once (GSYM arithmeticTheory.MULT_COMM)] >> decide_tac) >>
  `type_memory_size (ArrayTV et (Dynamic pcap)) + w2n w <= u.vs_alloca_next` by
    (qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `w2n w + (32*i+32) < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> strip_tac >>
  `w2n w + (32*i+32) = 32*i+(w2n w+32)` by decide_tac >>
  fs[]
QED

Finalise rest_word_membership_tail_dynamic_full
