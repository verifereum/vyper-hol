Theory bodyFullBopRestWordTailFixed
Ancestors
  bodyFullBopRestWordTailRep bodyFullBopRestWordFullControl
  bodyFullBopRestWordLoads bodyFullBopRestWordCtor
  bodyFullBopRestWordTailFrame bodyPtrBopInHeaderCode
  exprSimBopRestWordBasics exprPtrUnwrapMarked fragGasOriginPtrLoop

Theorem rest_word_membership_tail_fixed_full:
 !DF lo d explicit ctx fn PG cenv cx e es sa sm s0 G0 tn0 tv vv ee u Gu Tu needleop needle av ety bd pbd et is_in out ct guard.
 (?n. bd = Fixed n) /\
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
  >- suspend "fixed_execution" >>
  qexistsl_tac [`u`, `Gu`, `Tu`] >> metis_tac[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_execution]:
  drule_all rest_word_membership_tail_clean_reads >> strip_tac >>
  gvs[] >>
  `compile_array_membership_loop needleop (vv_operand vv) (Lit (n2w n))
    (elem_size_in_location cenv (case vv_location vv of SOME l => l | NONE => LocMemory) ety)
    0 (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case vv_location vv of SOME l => l | NONE => LocMemory)) NONE is_in sm = (out,ct)` by
    gvs[membership_fixed_compile_split] >>
  suspend "fixed_search"
QED

Resume rest_word_membership_tail_fixed_full[fixed_search]:
  qabbrev_tac `ws = GENLIST (\i. typed_val_to_w256 et
    (THE (array_index (ArrayTV et (Fixed n)) av (&i))))
    (array_length (ArrayTV et (Fixed n)) av)` >>
  `LENGTH ws = n` by (simp[Abbr `ws`] >> metis_tac[]) >>
  suspend "fixed_control"
QED

Resume rest_word_membership_tail_fixed_full[fixed_control]:
  `?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gu H,Tu H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sm (Gu H) (Tu H) u (Gt H) (Tt H) t /\
    ~t.vs_halted /\ t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\
    eval_operand out t = SOME (bool_to_word
      (if is_in then MEM (typed_val_to_w256 et needle) ws
       else ~MEM (typed_val_to_w256 et needle) ws)) /\
    op_prov (Gt H) out = NONE /\ op_taint (Tt H) out = {}` by
      suspend "fixed_run" >>
  `!H. guard H ==>
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\
    membership_loop_frame sm (Gu H) (Tu H) u (Gt' H) (Tt H) t /\
    alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
    ghost_inv_at (DF H) lo d cenv cx ee (Gu H) (Tu H) u /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gu H) (Tu H) u /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
    (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gu H) u) /\
    (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gu H) u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 (Gu H) (Tu H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
       (drule_then strip_assume_tac) >> simp[] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `guard H` kall_tac >>
  qexistsl_tac [`t`, `Gt'`, `Tt`] >>
  gen_tac >> disch_tac >>
  drule_all rest_word_membership_tail_full_frame >> strip_tac >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  `evaluate_in_array (ArrayTV et (Fixed n)) needle av <=>
    MEM (typed_val_to_w256 et needle) ws` by
      (simp[Abbr `ws`] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >> rpt strip_tac >> gvs[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_run]:
  `?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gu H,Tu H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sm (Gu H) (Tu H) u (Gt H) (Tt H) t /\
    eval_operand out t = SOME (bool_to_word
      (if is_in then MEM (typed_val_to_w256 et needle) ws
       else ~MEM (typed_val_to_w256 et needle) ws)) /\
    op_prov (Gt H) out = NONE /\ op_taint (Tt H) out = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts` by
    (irule rest_word_membership_loop_full_horizon_joint_all >>
     conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
           (drule_then strip_assume_tac) >>
         gvs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
     simp[] >>
     goal_assum (drule_at Any) >>
     simp[] >> conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
           (drule_then strip_assume_tac) >>
         simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
     suspend "fixed_callback") >>
  qpat_x_assum `!H. guard H ==> read_result _ _ _ = _ /\ _` kall_tac >>
  qpat_x_assum `!H. guard H ==> array_length _ _ = _ /\ _` kall_tac >>
  metis_tac[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_callback]:
  qabbrev_tac `loc = case vv_location vv of NONE => LocMemory | SOME l => l` >>
  Cases_on `cenv.ce_is_ctor /\ loc = LocCode`
  >- suspend "fixed_ctor_callback" >>
  rpt gen_tac >> strip_tac >> suspend "fixed_runtime_callback"
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_callback]:
  qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode` strip_assume_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!H. guard H ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `?bw. eval_operand (vv_operand vv) u = SOME bw` by
    metis_tac[] >>
  Cases_on `IS_SOME cenv.ce_imm_alloca`
  >- (qpat_assum `cenv.ce_is_ctor` (fn th =>
        qpat_assum `IS_SOME cenv.ce_imm_alloca` (fn wh =>
          simp[NoAsms, th, wh])) >>
      rpt gen_tac >> strip_tac >>
      irule (SRULE [] (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
        (Q.INST [`q` |-> `0`, `delta` |-> `0`, `width` |-> `2`]
          rest_word_membership_ctor_load_joint_indexed))) >>
      suspend "fixed_ctor_some_inputs") >>
  qpat_assum `cenv.ce_is_ctor` (fn th =>
    qpat_assum `~IS_SOME cenv.ce_imm_alloca` (fn wh =>
      simp[NoAsms, th, wh])) >>
  rpt gen_tac >> strip_tac >>
  irule (SRULE [] (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`q` |-> `0`, `delta` |-> `0`, `width` |-> `1`]
      rest_word_membership_ctor_load_joint_indexed))) >>
  suspend "fixed_ctor_none_inputs"
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_some_inputs]:
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  qexistsl_tac [`\i. bw + n2w (elem_size_in_location cenv LocCode ety * i)`,
    `vv_operand vv`, `NONE`, `bw`, `cenv.ce_imm_alloca`, `is_in`,
    `Lit (n2w n)`, `needleop`, `out`, `ct`, `0`, `elem_size_in_location cenv LocCode ety`] >>
  conj_tac >- suspend "fixed_ctor_some_reads" >>
  simp[] >> (gvs[])
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_none_inputs]:
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  qexistsl_tac [`\i. bw + n2w (elem_size_in_location cenv LocCode ety * i)`,
    `vv_operand vv`, `NONE`, `bw`, `cenv.ce_imm_alloca`, `is_in`,
    `Lit (n2w n)`, `needleop`, `out`, `ct`, `0`, `elem_size_in_location cenv LocCode ety`] >>
  conj_tac >- suspend "fixed_ctor_none_reads" >>
  gvs[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_callback]:
  suspend "fixed_runtime_prefix_and_read"
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_some_reads]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. guard H ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  qpat_x_assum `LENGTH ws = n` kall_tac >>
  gvs[] >>
  `lo <> 0` by
    (qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
       (qspec_then `i` (drule_then strip_assume_tac)) >> decide_tac) >>
  simp[] >>
  suspend "fixed_ctor_some_elements"
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_none_reads]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. guard H ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  qpat_x_assum `LENGTH ws = n` kall_tac >>
  gvs[] >>
  `lo <> 0` by
    (qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
       (qspec_then `i` (drule_then strip_assume_tac)) >> decide_tac) >>
  simp[] >>
  suspend "fixed_ctor_none_elements"
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_some_elements]:
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  gen_tac >> disch_tac >>
  `i' < n` by fs[Abbr `ws`] >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
    (qspec_then `i'` (drule_then strip_assume_tac)) >>
  `w2n bw + 32 * i' < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then assume_tac >>
  `w2n (bw + n2w (i' * elem_size_in_location cenv LocCode ety)) = 32 * i' + w2n bw` by
    (qpat_assum `elem_size_in_location _ _ _ = 32` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[Once arithmeticTheory.MULT_COMM] >>
     qpat_assum `w2n (bw + n2w (32 * i')) = _` (fn th => pure_rewrite_tac[th]) >> decide_tac) >>
  simp[Abbr `ws`, listTheory.EL_GENLIST]
QED

Resume rest_word_membership_tail_fixed_full[fixed_ctor_none_elements]:
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  gen_tac >> disch_tac >>
  `i' < n` by fs[Abbr `ws`] >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
    (qspec_then `i'` (drule_then strip_assume_tac)) >>
  `w2n bw + 32 * i' < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then assume_tac >>
  `w2n (bw + n2w (i' * elem_size_in_location cenv LocCode ety)) = 32 * i' + w2n bw` by
    (qpat_assum `elem_size_in_location _ _ _ = 32` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[Once arithmeticTheory.MULT_COMM] >>
     qpat_assum `w2n (bw + n2w (32 * i')) = _` (fn th => pure_rewrite_tac[th]) >> decide_tac) >>
  simp[Abbr `ws`, listTheory.EL_GENLIST]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_prefix_and_read]:
  `compile_array_membership_loop needleop (vv_operand vv) (Lit (n2w n))
     (elem_size_in_location cenv loc ety) 0
     (compile_ptr_load F cenv.ce_imm_alloca loc) NONE is_in sm = (out,ct)` by
    (`compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc =
       compile_ptr_load F cenv.ce_imm_alloca loc` by
       (simp[FUN_EQ_THM] >> Cases_on `loc` >> fs[contextTheory.compile_ptr_load_def]) >>
     metis_tac[]) >>
  `?bw. eval_operand (vv_operand vv) u = SOME bw` by
    (qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     Cases_on `vv_location vv`
     >- (qpat_x_assum `_ \/ _ ==> ?w. _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
     rename1 `vv_location vv = SOME vl` >> Cases_on `vl`
     >- (qpat_x_assum `_ \/ _ ==> ?w. _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >> simp[])
     >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
           (qspec_then `F` mp_tac) >>
         simp[NoAsms] >> strip_tac >> simp[])
     >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
           (qspec_then `T` mp_tac) >>
         simp[NoAsms] >> strip_tac >> simp[])
     >- (Cases_on `cenv.ce_is_ctor`
         >- (qpat_x_assum `cenv.ce_is_ctor /\ _ ==> ?w. _` mp_tac >>
             (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
         qpat_x_assum `~cenv.ce_is_ctor /\ _ ==> ?w. _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
     qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     Cases_on `vv` >> fs[contextTheory.vv_location_def] >>
     drule vv_post_not_calldata >> simp[]) >>
  `?sp gp tp. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG)
      (s,Gs h,Ts h) [] (OK sp,gp h,tp h) /\
    membership_loop_frame sm (Gu h) (Tu h) u (gp h) (tp h) sp /\
    membership_loop_registers sm i 0w (gp h) (tp h) sp /\
    ~sp.vs_halted /\ allocas_from lo sp /\
    sp.vs_current_bb = s.vs_current_bb /\ sp.vs_inst_idx = 2 /\
    lookup_var ("%" ++ toString (sm.cs_next_var+4)) sp =
      SOME (bw+n2w (elem_size_in_location cenv loc ety*i)) /\
    FLOOKUP (gp h) ("%" ++ toString (sm.cs_next_var+4)) =
      op_prov (Gu h) (vv_operand vv) /\
    op_taint (tp h) (Var ("%" ++ toString (sm.cs_next_var+4))) = {}` by
      suspend "fixed_runtime_prefix" >>
  suspend "fixed_runtime_read"
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_prefix]:
  simp[NoAsms] >>
  irule (SRULE [Once arithmeticTheory.MULT_COMM]
    (Q.INST [`skip` |-> `0`, `delta` |-> `0`]
      rest_word_membership_runtime_address_operand_joint_indexed)) >>
  conj_tac >- suspend "fixed_runtime_prefix_guard" >>
  conj_tac >- (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_prefix_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  simp[] >>
  qpat_assum `!sl t Gt Tt. sm.cs_next_var <= sl.cs_next_var /\ _ ==> _`
    (qspecl_then [`sm`, `s`, `Gs H'`, `Ts H'`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `vv_location vv`
  >- (fs[] >> metis_tac[]) >>
  rename1 `vv_location vv = SOME vl` >>
  Cases_on `vl`
  >- (fs[] >> metis_tac[])
  >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
        (qspec_then `F` mp_tac) >> simp[NoAsms] >> strip_tac >> simp[])
  >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
        (qspec_then `T` mp_tac) >> simp[NoAsms] >> strip_tac >> simp[])
  >- (fs[Abbr `loc`] >> metis_tac[]) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  Cases_on `vv` >> fs[contextTheory.vv_location_def] >>
  drule vv_post_not_calldata >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_read]:
  `?t Gt Tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG)
      (sp,gp h,tp h) [] (OK t,Gt h,Tt h) /\
    membership_loop_frame sm (Gu h) (Tu h) u (Gt h) (Tt h) t /\
    membership_loop_registers sm i 0w (Gt h) (Tt h) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sp.vs_current_bb /\ t.vs_inst_idx = 3 /\
    lookup_var ("%" ++ toString (sm.cs_next_var+5)) t = SOME (EL i ws) /\
    FLOOKUP (Gt h) ("%" ++ toString (sm.cs_next_var+5)) = NONE /\
    op_taint (Tt h) (Var ("%" ++ toString (sm.cs_next_var+5))) = {}` by
      suspend "fixed_runtime_load" >>
  qexistsl_tac [`t`, `Gt'`, `Tt`] >> gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sp,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~(cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca)` by metis_tac[] >>
  simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def] >>
  conj_tac >- (irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >> simp[]) >>
  fs[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_load]:
  `?t Gt Tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG)
      (sp,gp h,tp h) [] (OK t,Gt h,Tt h) /\
    membership_loop_frame sm (Gu h) (Tu h) u (Gt h) (Tt h) t /\
    membership_loop_registers sm i 0w (Gt h) (Tt h) t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sp.vs_current_bb /\ t.vs_inst_idx = 3 /\
    lookup_var ("%" ++ toString (sm.cs_next_var+5)) t =
      SOME (ptr_load_val F loc (bw+n2w (elem_size_in_location cenv loc ety*i)) sp) /\
    FLOOKUP (Gt h) ("%" ++ toString (sm.cs_next_var+5)) = NONE /\
    op_taint (Tt h) (Var ("%" ++ toString (sm.cs_next_var+5))) = {}` by
      suspend "fixed_runtime_raw_load" >>
  `ptr_load_val F loc (bw+n2w (elem_size_in_location cenv loc ety*i)) sp = EL i ws` by
      suspend "fixed_runtime_load_value" >>
  qexistsl_tac [`t`, `Gt'`, `Tt`] >> metis_tac[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_raw_load]:
  Cases_on `loc`
  >- suspend "fixed_runtime_memory_load"
  >- suspend "fixed_runtime_storage_load"
  >- suspend "fixed_runtime_transient_load"
  >- suspend "fixed_runtime_code_load" >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  Cases_on `vv` >> fs[contextTheory.vv_location_def] >>
  drule vv_post_not_calldata >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_storage_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`tr` |-> `F`, `skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_slot_read_joint_indexed)) >>
  simp[] >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  suspend "fixed_runtime_storage_inputs"
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_storage_inputs]:
  `vv_location vv = SOME LocStorage` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `F` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocStorage ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  simp[] >>
  ` (tp H').t_stor = (Tu H').t_stor` by
    fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  gvs[] >>
  qpat_x_assum `!j. j < n ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_transient_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`tr` |-> `T`, `skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_slot_read_joint_indexed)) >>
  simp[] >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocTransient` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `T` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocTransient ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  simp[] >>
  `(tp H').t_trans = (Tu H').t_trans` by
    fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  gvs[] >>
  qpat_x_assum `!j. j < _ ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_load_value]:
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `LENGTH ws = n` kall_tac >>
  `EL i ws = typed_val_to_w256 et
    (THE (array_index (ArrayTV et (Fixed n)) av (&i)))` by
    simp[Abbr `ws`, listTheory.EL_GENLIST] >>
  Cases_on `loc`
  >- suspend "fixed_memory_value"
  >- suspend "fixed_storage_value"
  >- suspend "fixed_transient_value"
  >- suspend "fixed_code_value" >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  Cases_on `vv` >> fs[contextTheory.vv_location_def] >>
  drule vv_post_not_calldata >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_storage_value]:
  `vv_location vv = SOME LocStorage` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `F` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocStorage ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `!w. sload w sp = sload w u` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >>
     simp[venomStateTheory.sload_def, venomStateTheory.contract_storage_def]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[venomStateTheory.sload_def]
QED

Resume rest_word_membership_tail_fixed_full[fixed_transient_value]:
  `vv_location vv = SOME LocTransient` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `T` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocTransient ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `!w. tload w sp = tload w u` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >>
     simp[venomStateTheory.tload_def, venomStateTheory.contract_transient_def]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[venomStateTheory.tload_def]
QED

Resume rest_word_membership_tail_fixed_full[fixed_code_value]:
  `vv_location vv = SOME LocCode /\ ~cenv.ce_is_ctor` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
  simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `sp.vs_data_section = u.vs_data_section` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> word_of_bytes _ _ _ = _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_code_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_code_read_joint_indexed)) >>
  simp[] >>
  conj_tac >- suspend "fixed_code_bound" >>
  conj_tac >- suspend "fixed_code_guard" >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_code_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  fs[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_code_bound]:
  `vv_location vv = SOME LocCode /\ ~cenv.ce_is_ctor` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >>
  simp[] >> strip_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `sp.vs_data_section = u.vs_data_section` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => simp[Once th])) >>
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n (bw+n2w (32*i)) <= w2n bw + 32*i` by
    (CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV
       (REWR_CONV (GSYM wordsTheory.n2w_w2n))))) >>
     simp[NoAsms, wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_LESS_EQ]) >>
  gvs[] >> decide_tac
QED

Resume rest_word_membership_tail_fixed_full[fixed_runtime_memory_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_memory_read_joint_indexed)) >>
  simp[] >>
  conj_tac >- suspend "fixed_memory_bound" >>
  conj_tac >- suspend "fixed_memory_guard" >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_memory_bound]:
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >>
  (impl_tac >- (Cases_on `vv_location vv` >> fs[])) >>
  disch_then strip_assume_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >>
  simp[] >> strip_tac >>
  `type_memory_size (ArrayTV et (Fixed n)) + w2n bw <= u.vs_alloca_next` by
    (gvs[] >> qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `sp.vs_alloca_next = u.vs_alloca_next` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => simp[Once th])) >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n (bw+n2w (32*i)) <= w2n bw + 32*i` by
    (CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV
       (REWR_CONV (GSYM wordsTheory.n2w_w2n))))) >>
     simp[NoAsms, wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_LESS_EQ]) >>
  gvs[] >> decide_tac
QED

Resume rest_word_membership_tail_fixed_full[fixed_memory_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >>
  (impl_tac >- (Cases_on `vv_location vv` >> fs[])) >>
  disch_then strip_assume_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >>
  simp[] >> strip_tac >>
  suspend "fixed_memory_guard_inputs"
QED

Resume rest_word_membership_tail_fixed_full[fixed_memory_guard_inputs]:
  qpat_x_assum `LENGTH ws = n` kall_tac >>
  `type_memory_size (ArrayTV et (Fixed n)) + w2n bw <= u.vs_alloca_next` by
    (gvs[] >> qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n bw + 32*i < dimword (:256)` by decide_tac >>
  `w2n (bw+n2w (32*i)) = w2n bw + 32*i` by
    metis_tac[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  simp[] >>
  `i * 32 = 32*i` by decide_tac >>
  simp[] >>
  `(tp H').t_mem = (Tu H').t_mem` by
    fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  gvs[] >>
  `?p. vv_operand vv = Var p` by
    (`val_footprint (ArrayTV et (Fixed n)) (ArrayV av) <> 0` by
       (simp[loweringPostsTheory.val_footprint_def] >> decide_tac) >>
     drule_all bodyPtrBopHashFootprintTheory.ptr_mem_ok_bounds >> metis_tac[]) >>
  qpat_x_assum `!off n' src dst t G' T'. _` (qspec_then `32*i` mp_tac) >>
  disch_then irule >>
  simp[ptrDisciplineTheory.op_prov_def] >> fs[]
QED

Resume rest_word_membership_tail_fixed_full[fixed_memory_value]:
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >>
  (impl_tac >- (Cases_on `vv_location vv` >> fs[])) >>
  disch_then strip_assume_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >>
  simp[] >> strip_tac >>
  `type_memory_size (ArrayTV et (Fixed n)) + w2n bw <= u.vs_alloca_next` by
    (gvs[] >> qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n bw + 32*i < dimword (:256)` by decide_tac >>
  `w2n (bw+n2w (32*i)) = w2n bw + 32*i` by
    metis_tac[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  `!a. mload a sp = mload a u` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >>
     simp[venomStateTheory.mload_def]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> mem_word_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Finalise rest_word_membership_tail_fixed_full

Theorem rest_word_membership_tail_fixed_const_full:
 !DF lo d explicit ctx fn PG cenv cx e es sa sm s0 G0 tn0 tv vv ee u Gu Tu needleop needle av ety bd pbd et is_in out ct guard.
 (?n. bd = Fixed n) /\
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
   op_prov Gu needleop = NONE /\ op_taint Tu needleop = {} /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
   alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
   ghost_inv_at (DF H) lo d cenv cx ee Gu Tu u /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu Tu u /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside Tu.t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op Gu u) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand Gu u) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gu Tu) ==>
 ?t Gt Tt. !H. guard H ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
     (u,Gu,Tu) [] (OK t,Gt,Tt) /\
   membership_loop_frame sm Gu Tu u Gt Tt t /\
   ~t.vs_halted /\ t.vs_current_bb = ct.cs_current_bb /\
   t.vs_inst_idx = LENGTH ct.cs_current_insts /\
   alloca_history fn t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv t /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
   ghost_inv_at (DF H) lo d cenv cx ee Gt Tt t /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gt Tt t /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) t = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside Tt.t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op Gt t) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand Gt t) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gt Tt /\
   eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
   op_prov Gt needleop = NONE /\ op_taint Tt needleop = {} /\
   eval_operand out t = SOME (bool_to_word
     (if is_in then evaluate_in_array (ArrayTV et bd) needle av
      else ~evaluate_in_array (ArrayTV et bd) needle av)) /\
   op_prov Gt out = NONE /\ op_taint Tt out = {}
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?H. guard H`
  >- suspend "execution" >>
  qexistsl_tac [`u`, `Gu`, `Tu`] >> metis_tac[]
QED

Resume rest_word_membership_tail_fixed_const_full[execution]:
  drule_all (BETA_RULE (Q.SPECL [`\h. Gu`, `\h. Tu`]
    (Q.GENL [`Gu`, `Tu`] (SPEC_ALL rest_word_membership_tail_clean_reads)))) >> strip_tac >>
  gvs[] >>
  `compile_array_membership_loop needleop (vv_operand vv) (Lit (n2w n))
    (elem_size_in_location cenv (case vv_location vv of SOME l => l | NONE => LocMemory) ety)
    0 (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case vv_location vv of SOME l => l | NONE => LocMemory)) NONE is_in sm = (out,ct)` by
    gvs[membership_fixed_compile_split] >>
  qabbrev_tac `ws = GENLIST (\i. typed_val_to_w256 et
    (THE (array_index (ArrayTV et (Fixed n)) av (&i))))
    (array_length (ArrayTV et (Fixed n)) av)` >>
  `LENGTH ws = n` by (simp[Abbr `ws`] >> metis_tac[]) >>
  suspend "control"
QED

Resume rest_word_membership_tail_fixed_const_full[control]:
  `?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gu,Tu) [] (OK t,Gt,Tt) /\
    membership_loop_frame sm Gu Tu u Gt Tt t /\
    ~t.vs_halted /\ t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\
    eval_operand out t = SOME (bool_to_word
      (if is_in then MEM (typed_val_to_w256 et needle) ws
       else ~MEM (typed_val_to_w256 et needle) ws)) /\
    op_prov Gt out = NONE /\ op_taint Tt out = {}` by
      suspend "run" >>
  `!H. guard H ==>
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\
    membership_loop_frame sm Gu Tu u Gt' Tt t /\
    alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
    ghost_inv_at (DF H) lo d cenv cx ee Gu Tu u /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu Tu u /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside Tu.t_mem u.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
    (!vt op. vv = StackValue vt op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op Gu u) /\
    (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand Gu u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gu Tu` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
       (drule_then strip_assume_tac) >> simp[] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `guard H` kall_tac >>
  qexistsl_tac [`t`, `Gt'`, `Tt`] >>
  gen_tac >> disch_tac >>
  drule_all (BETA_RULE (Q.SPECL [`\h. Gu`, `\h. Tu`, `\h. Gt'`, `\h. Tt`]
    (Q.GENL [`gu`, `tu`, `gt`, `tt`]
      (SPEC_ALL rest_word_membership_tail_full_frame)))) >> strip_tac >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  `evaluate_in_array (ArrayTV et (Fixed n)) needle av <=>
    MEM (typed_val_to_w256 et needle) ws` by
      (simp[Abbr `ws`] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >> rpt strip_tac >> gvs[]
QED

Resume rest_word_membership_tail_fixed_const_full[run]:
  `?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gu,Tu) [] (OK t,Gt,Tt) /\
    membership_loop_frame sm Gu Tu u Gt Tt t /\
    eval_operand out t = SOME (bool_to_word
      (if is_in then MEM (typed_val_to_w256 et needle) ws
       else ~MEM (typed_val_to_w256 et needle) ws)) /\
    op_prov Gt out = NONE /\ op_taint Tt out = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts` by
    (irule rest_word_membership_loop_const_full_horizon_joint_all >>
     conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
           (drule_then strip_assume_tac) >>
         gvs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
     simp[] >> goal_assum (drule_at Any) >>
     simp[] >> conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
           (drule_then strip_assume_tac) >>
         simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
     suspend "callback") >>
  qpat_x_assum `!H. guard H ==> read_result _ _ _ = _ /\ _` kall_tac >>
  qpat_x_assum `!H. guard H ==> array_length _ _ = _ /\ _` kall_tac >>
  metis_tac[]
QED

Resume rest_word_membership_tail_fixed_const_full[callback]:
  qabbrev_tac `loc = case vv_location vv of NONE => LocMemory | SOME l => l` >>
  Cases_on `cenv.ce_is_ctor /\ loc = LocCode`
  >- suspend "ctor_callback" >>
  rpt gen_tac >> strip_tac >> suspend "runtime_prefix_and_read"
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_callback]:
  qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode` strip_assume_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!H. guard H ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `?bw. eval_operand (vv_operand vv) u = SOME bw` by metis_tac[] >>
  Cases_on `IS_SOME cenv.ce_imm_alloca`
  >- (qpat_assum `cenv.ce_is_ctor` (fn th =>
        qpat_assum `IS_SOME cenv.ce_imm_alloca` (fn wh => simp[NoAsms, th, wh])) >>
      rpt gen_tac >> strip_tac >>
      irule (SRULE [] (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
        (Q.INST [`q` |-> `0`, `delta` |-> `0`, `width` |-> `2`]
          rest_word_membership_ctor_load_joint_const))) >>
      suspend "ctor_some_inputs") >>
  qpat_assum `cenv.ce_is_ctor` (fn th =>
    qpat_assum `~IS_SOME cenv.ce_imm_alloca` (fn wh => simp[NoAsms, th, wh])) >>
  rpt gen_tac >> strip_tac >>
  irule (SRULE [] (PURE_REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`q` |-> `0`, `delta` |-> `0`, `width` |-> `1`]
      rest_word_membership_ctor_load_joint_const))) >>
  suspend "ctor_none_inputs"
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_some_inputs]:
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`\i. bw + n2w (elem_size_in_location cenv LocCode ety * i)`,
    `vv_operand vv`, `NONE`, `bw`, `cenv.ce_imm_alloca`, `is_in`,
    `Lit (n2w n)`, `needleop`, `out`, `ct`, `0`, `elem_size_in_location cenv LocCode ety`] >>
  conj_tac >- suspend "ctor_some_reads" >> simp[] >> gvs[]
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_none_inputs]:
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`\i. bw + n2w (elem_size_in_location cenv LocCode ety * i)`,
    `vv_operand vv`, `NONE`, `bw`, `cenv.ce_imm_alloca`, `is_in`,
    `Lit (n2w n)`, `needleop`, `out`, `ct`, `0`, `elem_size_in_location cenv LocCode ety`] >>
  conj_tac >- suspend "ctor_none_reads" >> gvs[]
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_some_reads]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. guard H ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  qpat_x_assum `LENGTH ws = n` kall_tac >> gvs[] >>
  `lo <> 0` by
    (qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
       (qspec_then `i` (drule_then strip_assume_tac)) >> decide_tac) >>
  simp[] >> suspend "ctor_some_elements"
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_none_reads]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. guard H ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  qpat_x_assum `LENGTH ws = n` kall_tac >> gvs[] >>
  `lo <> 0` by
    (qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
       (qspec_then `i` (drule_then strip_assume_tac)) >> decide_tac) >>
  simp[] >> suspend "ctor_none_elements"
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_some_elements]:
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  gen_tac >> disch_tac >> `i' < n` by fs[Abbr `ws`] >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
    (qspec_then `i'` (drule_then strip_assume_tac)) >>
  `w2n bw + 32 * i' < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then assume_tac >>
  `w2n (bw + n2w (i' * elem_size_in_location cenv LocCode ety)) = 32 * i' + w2n bw` by
    (qpat_assum `elem_size_in_location _ _ _ = 32` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[Once arithmeticTheory.MULT_COMM] >>
     qpat_assum `w2n (bw + n2w (32 * i')) = _` (fn th => pure_rewrite_tac[th]) >> decide_tac) >>
  simp[Abbr `ws`, listTheory.EL_GENLIST]
QED

Resume rest_word_membership_tail_fixed_const_full[ctor_none_elements]:
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  gen_tac >> disch_tac >> `i' < n` by fs[Abbr `ws`] >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  qpat_assum `!j. j < n ==> 32 * j + _ <= lo /\ _`
    (qspec_then `i'` (drule_then strip_assume_tac)) >>
  `w2n bw + 32 * i' < dimword (:256)` by decide_tac >>
  drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> disch_then assume_tac >>
  `w2n (bw + n2w (i' * elem_size_in_location cenv LocCode ety)) = 32 * i' + w2n bw` by
    (qpat_assum `elem_size_in_location _ _ _ = 32` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[Once arithmeticTheory.MULT_COMM] >>
     qpat_assum `w2n (bw + n2w (32 * i')) = _` (fn th => pure_rewrite_tac[th]) >> decide_tac) >>
  simp[Abbr `ws`, listTheory.EL_GENLIST]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_prefix_and_read]:
  `compile_array_membership_loop needleop (vv_operand vv) (Lit (n2w n))
     (elem_size_in_location cenv loc ety) 0
     (compile_ptr_load F cenv.ce_imm_alloca loc) NONE is_in sm = (out,ct)` by
    (`compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc =
       compile_ptr_load F cenv.ce_imm_alloca loc` by
       (simp[FUN_EQ_THM] >> Cases_on `loc` >> fs[contextTheory.compile_ptr_load_def]) >> metis_tac[]) >>
  `?bw. eval_operand (vv_operand vv) u = SOME bw` by
    (qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     Cases_on `vv_location vv`
     >- (qpat_x_assum `_ \/ _ ==> ?w. _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
     rename1 `vv_location vv = SOME vl` >> Cases_on `vl`
     >- (qpat_x_assum `_ \/ _ ==> ?w. _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >> simp[])
     >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
           (qspec_then `F` mp_tac) >> simp[NoAsms] >> strip_tac >> simp[])
     >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
           (qspec_then `T` mp_tac) >> simp[NoAsms] >> strip_tac >> simp[])
     >- (Cases_on `cenv.ce_is_ctor`
         >- (qpat_x_assum `cenv.ce_is_ctor /\ _ ==> ?w. _` mp_tac >>
             (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
         qpat_x_assum `~cenv.ce_is_ctor /\ _ ==> ?w. _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
     qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     Cases_on `vv` >> fs[contextTheory.vv_location_def] >> drule vv_post_not_calldata >> simp[]) >>
  `?sp gp tp. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG)
      (s,Gs,Ts) [] (OK sp,gp,tp) /\
    membership_loop_frame sm Gu Tu u gp tp sp /\
    membership_loop_registers sm i 0w gp tp sp /\
    ~sp.vs_halted /\ allocas_from lo sp /\
    sp.vs_current_bb = s.vs_current_bb /\ sp.vs_inst_idx = 2 /\
    lookup_var ("%" ++ toString (sm.cs_next_var+4)) sp =
      SOME (bw+n2w (elem_size_in_location cenv loc ety*i)) /\
    FLOOKUP gp ("%" ++ toString (sm.cs_next_var+4)) = op_prov Gu (vv_operand vv) /\
    op_taint tp (Var ("%" ++ toString (sm.cs_next_var+4))) = {}` by
      suspend "runtime_prefix" >>
  suspend "runtime_read"
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_prefix]:
  simp[NoAsms] >>
  irule (SRULE [Once arithmeticTheory.MULT_COMM]
    (Q.INST [`skip` |-> `0`, `delta` |-> `0`]
      rest_word_membership_runtime_address_operand_joint_const)) >>
  conj_tac >- suspend "runtime_prefix_guard" >>
  conj_tac >- (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_prefix_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >> simp[] >>
  qpat_assum `!sl t Gt Tt. sm.cs_next_var <= sl.cs_next_var /\ _ ==> _`
    (qspecl_then [`sm`, `s`, `Gs`, `Ts`] mp_tac) >>
  simp[] >> strip_tac >> Cases_on `vv_location vv`
  >- (fs[] >> metis_tac[]) >> rename1 `vv_location vv = SOME vl` >>
  Cases_on `vl`
  >- (fs[] >> metis_tac[])
  >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
        (qspec_then `F` mp_tac) >> simp[NoAsms] >> strip_tac >> simp[])
  >- (qpat_x_assum `!tr. _ = SOME (if tr then LocTransient else LocStorage) ==> _`
        (qspec_then `T` mp_tac) >> simp[NoAsms] >> strip_tac >> simp[])
  >- (fs[Abbr `loc`] >> metis_tac[]) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  Cases_on `vv` >> fs[contextTheory.vv_location_def] >> drule vv_post_not_calldata >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_read]:
  `?t Gt Tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (sp,gp,tp) [] (OK t,Gt,Tt) /\
    membership_loop_frame sm Gu Tu u Gt Tt t /\
    membership_loop_registers sm i 0w Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sp.vs_current_bb /\ t.vs_inst_idx = 3 /\
    lookup_var ("%" ++ toString (sm.cs_next_var+5)) t = SOME (EL i ws) /\
    FLOOKUP Gt ("%" ++ toString (sm.cs_next_var+5)) = NONE /\
    op_taint Tt (Var ("%" ++ toString (sm.cs_next_var+5))) = {}` by suspend "runtime_load" >>
  qexistsl_tac [`t`, `Gt'`, `Tt`] >> gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (sp,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~(cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca)` by metis_tac[] >>
  simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def] >>
  conj_tac >- (irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >> simp[]) >> fs[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_load]:
  `?t Gt Tt. !h. guard h ==>
    gas_origin_ptr_path (DF h,lo,explicit,ctx,fn,PG) (sp,gp,tp) [] (OK t,Gt,Tt) /\
    membership_loop_frame sm Gu Tu u Gt Tt t /\
    membership_loop_registers sm i 0w Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sp.vs_current_bb /\ t.vs_inst_idx = 3 /\
    lookup_var ("%" ++ toString (sm.cs_next_var+5)) t =
      SOME (ptr_load_val F loc (bw+n2w (elem_size_in_location cenv loc ety*i)) sp) /\
    FLOOKUP Gt ("%" ++ toString (sm.cs_next_var+5)) = NONE /\
    op_taint Tt (Var ("%" ++ toString (sm.cs_next_var+5))) = {}` by suspend "runtime_raw_load" >>
  `ptr_load_val F loc (bw+n2w (elem_size_in_location cenv loc ety*i)) sp = EL i ws` by
    suspend "runtime_load_value" >>
  qexistsl_tac [`t`, `Gt'`, `Tt`] >> metis_tac[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_raw_load]:
  Cases_on `loc`
  >- suspend "runtime_memory_load"
  >- suspend "runtime_storage_load"
  >- suspend "runtime_transient_load"
  >- suspend "runtime_code_load" >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  Cases_on `vv` >> fs[contextTheory.vv_location_def] >> drule vv_post_not_calldata >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_storage_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`tr` |-> `F`, `skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_slot_read_joint_const)) >>
  simp[] >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocStorage` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `F` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocStorage ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  simp[] >>
  `tp.t_stor = Tu.t_stor` by fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  gvs[] >> qpat_x_assum `!j. j < n ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_transient_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`tr` |-> `T`, `skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_slot_read_joint_const)) >>
  simp[] >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  `vv_location vv = SOME LocTransient` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `T` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocTransient ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  simp[] >>
  `tp.t_trans = Tu.t_trans` by fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
  gvs[] >> qpat_x_assum `!j. j < _ ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_load_value]:
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `LENGTH ws = n` kall_tac >>
  `EL i ws = typed_val_to_w256 et
    (THE (array_index (ArrayTV et (Fixed n)) av (&i)))` by
    simp[Abbr `ws`, listTheory.EL_GENLIST] >>
  Cases_on `loc`
  >- suspend "memory_value"
  >- suspend "storage_value"
  >- suspend "transient_value"
  >- suspend "code_value" >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  Cases_on `vv` >> fs[contextTheory.vv_location_def] >> drule vv_post_not_calldata >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[storage_value]:
  `vv_location vv = SOME LocStorage` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `F` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocStorage ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `!w. sload w sp = sload w u` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >>
     simp[venomStateTheory.sload_def, venomStateTheory.contract_storage_def]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[venomStateTheory.sload_def]
QED

Resume rest_word_membership_tail_fixed_const_full[transient_value]:
  `vv_location vv = SOME LocTransient` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==> _`
    (qspec_then `T` mp_tac) >> simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocTransient ety = 1` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `!w. tload w sp = tload w u` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >>
     simp[venomStateTheory.tload_def, venomStateTheory.contract_transient_def]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> key_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[venomStateTheory.tload_def]
QED

Resume rest_word_membership_tail_fixed_const_full[code_value]:
  `vv_location vv = SOME LocCode /\ ~cenv.ce_is_ctor` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_x_assum `~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
  simp[NoAsms] >> disch_then strip_assume_tac >>
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `sp.vs_data_section = u.vs_data_section` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> word_of_bytes _ _ _ = _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_code_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_code_read_joint_const)) >>
  simp[] >> conj_tac >- suspend "code_bound" >>
  conj_tac >- suspend "code_guard" >> goal_assum (drule_at Any) >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[code_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >> fs[]
QED

Resume rest_word_membership_tail_fixed_const_full[code_bound]:
  `vv_location vv = SOME LocCode /\ ~cenv.ce_is_ctor` by (Cases_on `vv_location vv` >> fs[]) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >> simp[] >> strip_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `sp.vs_data_section = u.vs_data_section` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => simp[Once th])) >>
  `elem_size_in_location cenv LocCode ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n (bw+n2w (32*i)) <= w2n bw + 32*i` by
    (CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV (GSYM wordsTheory.n2w_w2n))))) >>
     simp[NoAsms, wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, arithmeticTheory.MOD_LESS_EQ]) >>
  gvs[] >> decide_tac
QED

Resume rest_word_membership_tail_fixed_const_full[runtime_memory_load]:
  simp[NoAsms, builtinPropsTheory.ptr_load_val_def] >>
  irule (SRULE [] (Q.INST [`skip` |-> `0`, `delta` |-> `0`]
    rest_word_membership_memory_read_joint_const)) >> simp[] >>
  conj_tac >- suspend "memory_bound" >>
  conj_tac >- suspend "memory_guard" >> goal_assum (drule_at Any) >> simp[]
QED

Resume rest_word_membership_tail_fixed_const_full[memory_bound]:
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >>
  (impl_tac >- (Cases_on `vv_location vv` >> fs[])) >> disch_then strip_assume_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >> simp[] >> strip_tac >>
  `type_memory_size (ArrayTV et (Fixed n)) + w2n bw <= u.vs_alloca_next` by
    (gvs[] >> qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `sp.vs_alloca_next = u.vs_alloca_next` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => simp[Once th])) >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n (bw+n2w (32*i)) <= w2n bw + 32*i` by
    (CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV (GSYM wordsTheory.n2w_w2n))))) >>
     simp[NoAsms, wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, arithmeticTheory.MOD_LESS_EQ]) >>
  gvs[] >> decide_tac
QED

Resume rest_word_membership_tail_fixed_const_full[memory_guard]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> array_length _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H'` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >>
  (impl_tac >- (Cases_on `vv_location vv` >> fs[])) >> disch_then strip_assume_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >> simp[] >> strip_tac >>
  suspend "memory_guard_inputs"
QED

Resume rest_word_membership_tail_fixed_const_full[memory_guard_inputs]:
  qpat_x_assum `LENGTH ws = n` kall_tac >>
  `type_memory_size (ArrayTV et (Fixed n)) + w2n bw <= u.vs_alloca_next` by
    (gvs[] >> qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n bw + 32*i < dimword (:256)` by decide_tac >>
  `w2n (bw+n2w (32*i)) = w2n bw + 32*i` by metis_tac[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  simp[] >> `i * 32 = 32*i` by decide_tac >> simp[] >>
  `tp.t_mem = Tu.t_mem` by fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> gvs[] >>
  `?p. vv_operand vv = Var p` by
    (`val_footprint (ArrayTV et (Fixed n)) (ArrayV av) <> 0` by
       (simp[loweringPostsTheory.val_footprint_def] >> decide_tac) >>
     drule_all bodyPtrBopHashFootprintTheory.ptr_mem_ok_bounds >> metis_tac[]) >>
  qpat_x_assum `!off n' src dst t G' T'. _` (qspec_then `32*i` mp_tac) >>
  disch_then irule >> simp[ptrDisciplineTheory.op_prov_def] >> fs[]
QED

Resume rest_word_membership_tail_fixed_const_full[memory_value]:
  qpat_assum `!h. guard h ==> read_result _ _ _ = _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==> _` mp_tac >>
  (impl_tac >- (Cases_on `vv_location vv` >> fs[])) >> disch_then strip_assume_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `i < array_length (ArrayTV et (Fixed n)) av` by fs[] >>
  drule_all bodyPtrBopInCodeContentsTheory.membership_array_element_extent >> simp[] >> strip_tac >>
  `type_memory_size (ArrayTV et (Fixed n)) + w2n bw <= u.vs_alloca_next` by
    (gvs[] >> qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    metis_tac[loweringPostsTheory.vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              exprLoweringPropsTheory.alloca_room_next_lt] >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    simp[exprSimBopRestWordTailTheory.rest_word_word_stride, compileEnvTheory.word_scale_def] >>
  `w2n bw + 32*i < dimword (:256)` by decide_tac >>
  `w2n (bw+n2w (32*i)) = w2n bw + 32*i` by metis_tac[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  `!a. mload a sp = mload a u` by
    (fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qpat_x_assum `sp = _` (fn th => once_rewrite_tac[th]) >> simp[venomStateTheory.mload_def]) >>
  gvs[builtinPropsTheory.ptr_load_val_def] >>
  qpat_x_assum `!j. j < n ==> mem_word_taint _ _ = {} /\ _`
    (qspec_then `i` mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Finalise rest_word_membership_tail_fixed_const_full
