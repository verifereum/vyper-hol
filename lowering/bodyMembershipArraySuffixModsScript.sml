(* Assemble the reached array read and the corresponding physical membership run. *)
Theory bodyMembershipArraySuffixMods
Ancestors
  bodyMembershipArrayReadMods bodyMembershipArrayMemoryMods
  bodyMembershipArraySlotsMods bodyMembershipArrayCodeMods bodyMembershipArrayCtorMods
  bodyMembershipArrayIndexLoadMods bodyMembershipArrayHeaderMods
  bodyMembershipFixedPhysicalMods bodyMembershipDynamicPhysicalMods
  bodyMembershipMemoryReadInputsMods bodyMembershipSlotReadInputsMods
  bodyMembershipCodeReadInputsMods bodyMembershipCtorReadInputsMods
  bodyMembershipNeedleAtRhsMods bodyPtrBopInRepresentation
  bodyPtrBopInHeaderCode exprSimBopRestWordTail stateRelProj allocationPtr
  bodyMembershipArrayPostMods bodyForcedStorageFrameMods
  bodyFullPostsMods gasOutcomeFullPostMods exprOperandVar exprWordOperand
  exprBodyPreProps exprBopSimDefs exprBopSimProps exprSimBopRestWordBasics abiEncodeArgsSim
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperArray vyperState
  bodyFullShadowBodyInv bodyPtrDefs exprLowering exprLoweringProps context compileEnv loweringPosts
  venomState venomExecSemantics ptrDiscipline freshWrites list
Libs monadsyntax

Theorem membership_horizon_at_cut[local]:
  storage_trace_frame f /\
  f (ee with gas_obs := xs) = (res, ee2 with gas_obs := ys) /\
  valid_horizon cx st0 H ee2.storage_trace ==>
  valid_horizon cx st0 H ee.storage_trace
Proof
  rpt strip_tac >> drule_all storage_trace_frame_prefix >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]
QED

val result_post = ``\(H : (bool # 256 word # type_value) list # num list) (res : value + vyperState$exception) ee G tn q. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa ct s0 ee v out q /\
  expr_store_bound cx (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2])) v out q /\
  q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
  alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
  s0.vs_alloca_next <= q.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn q /\
  ptr_val_ok cx (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2])) v out G tn q /\
  (~is_word_type (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2])) ==>
    ptr_buf_ok cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) out G q) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem membership_array_suffix_mods:
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  expr_body_pre_mods mods cenv cx env e1 es /\
  expr_body_pre_mods mods cenv cx env e2 mid /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  compile_var_array_membership cenv x vv (ArrayT (expr_type e1) bd) (bop = In) sm = (out,ct) /\
  fn_has_code sm ct func /\
  (!z. x = Var z \/ vv_operand vv = Var z ==> not_fresh_at sm z) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := obs1 ++ tail) =
    (INL needle,mid with gas_obs := tail)) /\
  (!tail. eval_expr cx e2 (mid with gas_obs := obs2 ++ tail) =
    (INL tv,fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid needle x t /\
    ptr_val_ok cx (post_value_type cenv e1) needle x G1 tn1 t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    vv_post_mods H ctx func cenv cx e2 mid s1 sm t fin tv vv u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
    ptr_vv_ok cx (post_value_type cenv e2) tv vv fin G2 tn2 u /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv fin = (INL v,fin) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e2) = SOME rt /\
                 eval_operand (vv_operand vv) u = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
                    val_in_memory rt v (w2n w) mem)) /\
    ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ ~u.vs_halted /\ fin.gas_obs = []) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (read_result cx tv)
       (\arr ee. (bop_result cx (BaseT BoolT) bop [expr_type e1;expr_type e2] needle arr ee,ee)))
    (fin,u,G2,tn2) (^result_post) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (gen_tac >> disch_tac >>
     irule (INST_TYPE [``:'a`` |-> ``:eval_result``] membership_horizon_at_cut) >>
     qexistsl_tac [`fin`,`eval_expr cx e2`,`INL tv`,`obs2 ++ []`,`[]`] >>
     conj_tac >- simp[evaluate_storage_trace_frame] >>
     conj_tac >- qpat_assum `!tail. eval_expr cx e2 _ = _` (qspec_then `[]` ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     irule (INST_TYPE [``:'a`` |-> ``:value``] membership_horizon_at_cut) >>
     qexistsl_tac [`mid`,`bind (eval_expr cx e1) (read_result cx)`,`INL needle`,`obs1 ++ []`,`[]`] >>
     conj_tac >- simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
     conj_tac >- qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `vv_holds_mods cenv cx (post_value_type cenv e2) tv vv (fin with gas_obs := []) u` by
    (`fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
     fs[vv_post_mods_def]) >>
  drule_all_then strip_assume_tac membership_array_read_mods >>
  qabbrev_tac `b = if bop = In then MEM (typed_val_to_w256 et needle) ws
                      else ~MEM (typed_val_to_w256 et needle) ws` >>
  `?q G tn. !H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G2,tn2) [] (OK q,G,tn) /\
    membership_loop_frame sm G2 tn2 u G tn q /\
    eval_operand out q = SOME (bool_to_word b) /\ op_prov G out = NONE /\ op_taint tn out = {} /\
    q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts` by
    suspend "run" >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`fin`,`INL (BoolV b)`,`q`,`tn`] >> conj_tac
  >- suspend "source" >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[] >> suspend "post"
QED

Resume membership_array_suffix_mods[run]:
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) mid.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac membership_needle_at_rhs_mods >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `stmt_state_rel (storage_trace_horizon fin.storage_trace) ctx func cenv cx fin u` by
    (qhdtm_assum `vv_post_mods` (mp_tac o REWRITE_RULE [vv_post_mods_def]) >> simp[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    (drule_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL alloca_room_next_lt)) stmt_state_rel_alloca_room) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!ib z. cenv.ce_imm_alloca = SOME ib /\ ib = Var z ==> not_fresh_at sm z` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at s1 z` by
       (irule local_ptrs_reserved_imm_base >> qexists_tac `cenv` >> simp[]) >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >> simp[]) >>
  `read_result cx tv fin = (INL (ArrayV av),fin)` by
    (`fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
     pop_assum (fn th => qpat_assum `!tail. read_result _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [th])))) >>
  qabbrev_tac `loc = case vv_location vv of NONE => LocMemory | SOME l => l` >>
  `loc <> LocCalldata` by
    (Cases_on `vv` >> fs[Abbr `loc`, vv_location_def] >>
     strip_tac >> fs[vv_holds_mods_def] >> drule membership_located_not_calldata >> simp[]) >>
  `elem_size_in_location cenv loc (expr_type e1) = word_scale loc` by
    simp[rest_word_word_stride] >>
  `evaluate_type (get_tenv cx) (ArrayT (expr_type e1) pbd) = SOME (ArrayTV et pbd)` by
    metis_tac[] >>
  `?w. eval_operand (vv_operand vv) u = SOME w /\ op_taint tn2 (vv_operand vv) = {} /\
    (!i. i < LENGTH ws ==>
      let skip = case bd of Fixed _ => 0 | Dynamic _ => word_scale loc in
      let addr = w + n2w (skip + elem_size_in_location cenv loc (expr_type e1) * i) in
      ptr_load_val cenv.ce_is_ctor loc addr u = EL i ws /\
      (loc = LocMemory ==>
        w2n addr + 32 <= u.vs_alloca_next /\ mem_word_taint tn2.t_mem (w2n addr) = {} /\
        !z p Gp Tp. lookup_var z p = SOME addr /\ FLOOKUP Gp z = op_prov G2 (vv_operand vv) /\
          op_taint Tp (Var z) = {} ==> ptr_covers Gp Tp z p 32) /\
      (loc = LocStorage ==> key_taint tn2.t_stor addr = {}) /\
      (loc = LocTransient ==> key_taint tn2.t_trans addr = {}) /\
      (loc = LocCode /\ ~cenv.ce_is_ctor ==> w2n addr <= LENGTH u.vs_data_section) /\
      (loc = LocCode /\ cenv.ce_is_ctor ==>
        w2n addr + 32 <= lo /\ mem_word_taint tn2.t_mem (w2n addr) = {})) /\
    (!cap. bd = Dynamic cap ==>
      if cenv.ce_is_ctor /\ loc = LocCode then
        w2n w + 32 <= lo /\ mem_word_taint tn2.t_mem (w2n w) = {} /\
        mload (w2n w) u = n2w (LENGTH ws)
      else case loc of
        LocMemory => (?z. vv_operand vv = Var z /\ ptr_covers G2 tn2 z u 32) /\
          w2n w + 32 <= u.vs_alloca_next /\ mem_word_taint tn2.t_mem (w2n w) = {} /\
          mload (w2n w) u = n2w (LENGTH ws)
      | LocStorage => key_taint tn2.t_stor w = {} /\ sload w u = n2w (LENGTH ws)
      | LocTransient => key_taint tn2.t_trans w = {} /\ tload w u = n2w (LENGTH ws)
      | LocCode => w2n w <= LENGTH u.vs_data_section /\
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) = n2w (LENGTH ws)
      | _ => F) /\
    (cenv.ce_is_ctor /\ loc = LocCode /\ (0 < LENGTH ws \/ (?cap. bd = Dynamic cap)) ==>
      op_prov G2 (vv_operand vv) = NONE /\
      !ib. cenv.ce_imm_alloca = SOME ib ==>
        eval_operand ib u = SOME 0w /\ op_prov G2 ib = NONE /\ op_taint tn2 ib = {})` by
    suspend "representation" >>
  `?q G tn. !H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G2,tn2) [] (OK q,G,tn) /\
    membership_loop_frame sm G2 tn2 u G tn q /\
    eval_operand out q = SOME (bool_to_word b) /\ op_prov G out = NONE /\ op_taint tn out = {} /\
    ~q.vs_halted /\ allocas_from lo q /\
    q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts` suffices_by
    (disch_then strip_assume_tac >> qexistsl_tac [`q`,`G`,`tn`] >>
     gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ws = GENLIST _ _` kall_tac >>
  simp_tac bool_ss [Abbr `b`] >>
  Cases_on `bd` >>
  rule_assum_tac (SIMP_RULE bool_ss [vyperASTTheory.bound_case_def,
    vyperASTTheory.bound_distinct, LET_THM])
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume membership_array_suffix_mods[representation]:
  Cases_on `loc = LocMemory` >- suspend "memory" >>
  Cases_on `loc = LocCode`
  >- (Cases_on `cenv.ce_is_ctor` >- suspend "ctor" >> suspend "code") >>
  suspend "slot"
QED

Resume membership_array_suffix_mods[memory]:
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` suffices_by
    (disch_tac >> drule_all_then strip_assume_tac membership_array_memory_mods >>
     `elem_size_in_location cenv LocMemory (expr_type e1) = 32` by
       simp[rest_word_word_stride, word_scale_def] >>
     drule_all_then mp_tac membership_memory_read_inputs_mods >>
     qpat_x_assum `ws = GENLIST _ _` kall_tac >>
     qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
     qpat_assum `elem_size_in_location cenv LocMemory (expr_type e1) = 32` (fn th =>
       simp_tac bool_ss [th, LET_THM, FORALL_AND_THM, IMP_CONJ_THM, word_scale_def,
         compileEnvTheory.data_location_distinct, compileEnvTheory.data_location_case_def]) >>
     disch_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
     qexists_tac `w` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `vv_location vv` >> fs[Abbr `loc`]
QED

Resume membership_array_suffix_mods[slot]:
  `?tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) /\
        loc = (if tr then LocTransient else LocStorage)` by
    (Cases_on `vv_location vv` >> fs[Abbr `loc`] >>
     rename1 `vv_location vv = SOME l` >> Cases_on `l` >> fs[] >>
     ((qexists_tac `F` >> simp[] >> NO_TAC) ORELSE (qexists_tac `T` >> simp[]))) >>
  rename1 `vv_location vv = SOME (if tr then LocTransient else LocStorage)` >>
  `elem_size_in_location cenv loc (expr_type e1) = 1` by
    (qpat_assum `elem_size_in_location _ loc _ = word_scale loc`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `loc = if tr then _ else _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `tr` >> simp[word_scale_def]) >>
  drule_all_then strip_assume_tac membership_array_slots_mods >>
  mp_tac (Q.INST [`ety` |-> `expr_type e1`, `Tu` |-> `tn2`]
            membership_slot_read_inputs_mods) >>
  simp_tac bool_ss [LET_THM] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ws = GENLIST _ _` kall_tac >>
  qpat_x_assum `loc = if tr then _ else _` SUBST_ALL_TAC >>
  Cases_on `tr` >>
  simp_tac bool_ss [LET_THM, FORALL_AND_THM, IMP_CONJ_THM,
    compileEnvTheory.data_location_distinct, compileEnvTheory.data_location_case_def] >>
  disch_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `w` >>
  FULL_SIMP_TAC bool_ss [LET_THM, FORALL_AND_THM, IMP_CONJ_THM, word_scale_def,
    compileEnvTheory.data_location_distinct, compileEnvTheory.data_location_case_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume membership_array_suffix_mods[ctor]:
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[Abbr `loc`]) >>
  `sa.cs_next_var <= sm.cs_next_var` by decide_tac >>
  qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`
    (mp_tac) >> impl_tac >- simp[] >> disch_tac >>
  drule_all_then strip_assume_tac membership_array_ctor_mods >>
  `elem_size_in_location cenv LocCode (expr_type e1) = 32` by
    simp[rest_word_word_stride, word_scale_def] >>
  drule_all_then mp_tac membership_ctor_read_inputs_mods >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  simp_tac bool_ss [LET_THM, FORALL_AND_THM, IMP_CONJ_THM,
    compileEnvTheory.data_location_distinct] >>
  disch_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `w` >>
  qpat_x_assum `ws = GENLIST _ _` kall_tac >>
  ASM_SIMP_TAC bool_ss [LET_THM, FORALL_AND_THM, IMP_CONJ_THM,
    compileEnvTheory.data_location_distinct] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume membership_array_suffix_mods[code]:
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> fs[Abbr `loc`]) >>
  drule_all (REWRITE_RULE [LET_THM] (SPEC_ALL membership_array_code_mods)) >>
  qpat_assum `ws = GENLIST _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  BETA_TAC >> strip_tac >>
  `elem_size_in_location cenv loc (expr_type e1) = 32` by
    simp[word_scale_def] >>
  mp_tac (Q.INST [`ety` |-> `expr_type e1`] membership_code_read_inputs_mods) >>
  simp_tac bool_ss [LET_THM] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  simp_tac bool_ss [LET_THM, FORALL_AND_THM, IMP_CONJ_THM] >>
  disch_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `w` >>
  qpat_x_assum `ws = GENLIST _ _` kall_tac >>
  ASM_SIMP_TAC bool_ss [LET_THM, FORALL_AND_THM, IMP_CONJ_THM,
    compileEnvTheory.data_location_distinct, compileEnvTheory.data_location_case_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume membership_array_suffix_mods[fixed]:
  `loc = case vv_location vv of SOME l => l | NONE => LocMemory` by
    (Cases_on `vv_location vv` >> simp[Abbr `loc`]) >>
  irule (membership_fixed_physical_mods |> SIMP_RULE bool_ss [LET_THM]
         |> Q.GEN `guard` |> Q.ISPEC `\H. valid_horizon cx st0 H fin.storage_trace`
         |> BETA_RULE) >>
  conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_var_array_membership _ _ _ _ _ _ = _` (irule_at Any) >>
  simp_tac bool_ss [vyperASTTheory.bound_11] >>
  reverse conj_tac >-
    (conj_tac >-
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!z. x = Var z \/ _ ==> _` irule >> ASM_SIMP_TAC bool_ss []) >>
     conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
     ASM_SIMP_TAC bool_ss []) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `loc = case _ of _ => _ | _ => _` (fn loc_eq =>
    qpat_assum `compile_var_array_membership _ _ _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [membership_fixed_compile_split, GSYM loc_eq])) >>
  irule (membership_array_index_load_mods
         |> Q.GEN `guard` |> Q.ISPEC `\H. valid_horizon cx st0 H fin.storage_trace`
         |> Q.INST [`skip` |-> `0`, `bound` |-> `NONE`]
         |> SIMP_RULE std_ss [BETA_THM, optionTheory.IS_SOME_DEF, arithmeticTheory.ADD_0,
                              prim_recTheory.NOT_LESS_0]) >>
  conj_tac >-
    (gen_tac >> disch_tac >> qpat_assum `!z. x = Var z \/ _ ==> _` irule >>
     ASM_SIMP_TAC bool_ss []) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexists_tac `w` >>
  conj_tac >-
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!j. j < LENGTH ws ==> ptr_load_val _ _ _ _ = _ /\ _`
       (drule_then mp_tac) >>
     simp_tac bool_ss [LET_THM, arithmeticTheory.ADD_CLAUSES] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     disch_tac >> qpat_assum `loc = LocMemory ==> _` (drule_then strip_assume_tac) >>
     ASM_SIMP_TAC bool_ss [] >> rpt strip_tac >> first_x_assum irule >>
     ASM_SIMP_TAC bool_ss []) >>
  conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < LENGTH ws` by decide_tac >>
  qpat_assum `cenv.ce_is_ctor /\ loc = LocCode /\ 0 < LENGTH ws ==> _` mp_tac >>
  ASM_SIMP_TAC bool_ss [FORALL_AND_THM, IMP_CONJ_THM] >>
  rpt strip_tac >> first_assum ACCEPT_TAC
QED

Resume membership_array_suffix_mods[dynamic]:
  irule (membership_dynamic_physical_mods |> Q.GEN `guard`
         |> Q.ISPEC `\H. valid_horizon cx st0 H fin.storage_trace` |> BETA_RULE) >>
  conj_tac >-
    (qexists_tac `storage_trace_horizon fin.storage_trace` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `compile_var_array_membership _ _ _ _ _ _ = _` (irule_at Any) >>
  simp_tac bool_ss [vyperASTTheory.bound_11] >>
  qexists_tac `w` >>
  qpat_assum `Abbrev (loc = case _ of _ => _ | _ => _)`
    (fn th => simp_tac bool_ss [LET_THM, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (disch_tac >> qpat_assum `cenv.ce_is_ctor /\ loc = LocCode /\ _ ==> _` mp_tac >>
     ASM_SIMP_TAC bool_ss [vyperASTTheory.bound_11, EXISTS_REFL]) >>
  qpat_assum `!cap. Dynamic n = Dynamic cap ==> _`
    (qspec_then `n` (mp_tac o REWRITE_RULE [])) >>
  DISCH_THEN ACCEPT_TAC
QED

Resume membership_array_suffix_mods[source]:
  qpat_x_assum `ws = GENLIST _ _` kall_tac >>
  `bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := obs2) =
     (INL (ArrayV av),fin with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
     simp[bind_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT (expr_type e1) bd) = SOME (ArrayTV et bd)` by
    (`expr_body_pre_mods mods cenv cx env e2 (mid with gas_obs := obs2)` by
       simp[bodyWriteSubscriptSourceModsTheory.write_subscript_source_gas_obs_mods] >>
     drule_all (REWRITE_RULE [ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval_mods) >>
     strip_tac >>
     qpat_assum `expr_body_pre_mods _ _ _ _ e2 mid`
       (assume_tac o MATCH_MP expr_sim_inv_mods_env o MATCH_MP expr_body_pre_mods_inv) >>
     drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
     qpat_assum `!v. INL _ = INL v ==> _` (qspec_then `ArrayV av` mp_tac) >>
     simp_tac bool_ss [vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> strip_tac >>
     qpat_assum `env.type_defs = _` (fn a =>
       qpat_assum `expr_type e2 = _` (fn b =>
         qpat_assum `evaluate_type env.type_defs (expr_type e2) = SOME _`
           (assume_tac o REWRITE_RULE [a,b]))) >>
     drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
     qpat_assum `evaluate_type _ (expr_type e1) = SOME et` (fn th =>
       simp_tac (srw_ss()) [th]) >>
     strip_tac >>
     qpat_assum `expr_type e2 = _` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `tv' = _` (fn th =>
       qpat_assum `evaluate_type (get_tenv cx) (ArrayT _ _) = SOME tv'`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  gen_tac >> simp[bind_def] >>
  qpat_assum `bop = In \/ bop = NotIn` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
  simp[Abbr `b`,bop_result_def,vyperContextTheory.evaluate_builtin_def,
       vyperValueOperationTheory.evaluate_binop_def,vyperValueOperationTheory.binop_negate_def]
QED

Resume membership_array_suffix_mods[post]:
  `valid_horizon cx st0 H mid.storage_trace` by simp[] >>
  `valid_horizon cx st0 H es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  mp_tac (membership_array_post_mods |> Q.GEN `H` |>
          Q.ISPEC `H : (bool # 256 word # type_value) list # num list` |>
          Q.INST [`ety` |-> `expr_type e1`]) >>
  simp_tac bool_ss [LET_THM] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  BETA_TAC >> simp[]
QED

Finalise membership_array_suffix_mods
