(* Compiler and execution cuts for the non-word MakeArray slot suffix. *)
Theory bodyMakeSlotNonwordMods
Ancestors
  bodyMakeElementsContractMods bodyMakeElementStoreMods bodyStructFieldsSourceMods
  bodyIfExpArmUnwrapMods bodyAttributeAddFrameMods bodyFullMakeArrayInputs
  bodyIfExpTypedImmFrameMods gasOutcomeFullPostMods bodyFullIfExpReach
  externalEntryShape exprSimUnwrap exprLoweringProps fragExec compileEnv
  bodyPtrMakeArrayEmission bodyFullAttributeAdd fragGasSeqPtr ptrDiscipline
  venomState finite_map words bodyPtrDefs bodyFullPostsMods bodyFullShadowBodyInv
  fragGasOriginPtr gasContext vyperStorageFootprint exprOperandVar freshWrites
  bodyMakeSlotVvFrameMods loweringStateRelDefs bodyForRangeScalarFrameMods
  bodyFullUnwrapRun context exprSimMemDefs vyperState logValueFramePtr
  bodyMakeSlotReadWindowMods bodyMakeSlotNonwordStoreMods bodyMakeSlotStoreCutMods
  bodyMakeSlotStoreWindowMods bodyStructFieldCutsMods vyperInterpreter
  exprBodyPreProps exprSimMemorySource

val _ = Parse.hide "base";

Theorem make_slot_nonword_code_cuts[local]:
  make_elements_once_mods ce e q off dty sa = ((),sb) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  fn_has_code sa sb func ==>
  ?dst sn src sc.
    emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (src,sc) /\
    compile_store_memory ce src dst dty (lowered_value_type ce e) sc = ((),sb) /\
    fn_has_code sm sn func /\ fn_has_code sn sc func /\ fn_has_code sc sb func /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    ci_mono sm sn /\ ci_mono sn sc /\ ci_mono sc sb
Proof
  strip_tac >>
  Cases_on `emit_op ADD [Var q; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (src,sc)` >>
  fs[make_elements_once_mods_def,comp_bind_def] >>
  drule_then strip_assume_tac compile_expr_extends >>
  drule_then assume_tac unwrap_value_extends >>
  `cs_extends sm sn` by
    (mp_tac (CONJUNCT1 (CONJUNCT2 cs_appends_emit_helpers)) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends sc sb` by
    (qspecl_then [`ce`,`src`,`dst`,`dty`,`lowered_value_type ce e`,`sc`] mp_tac
       compile_store_memory_labels >> simp[]) >>
  `cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sn sc func /\ fn_has_code sc sb func` by metis_tac[fn_has_code_split] >>
  `ci_mono sm sn` by (qspecl_then [`ADD`,`[Var q; Lit (n2w off)]`,`sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sn sc` by (qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sc sb` by
    (qspecl_then [`ce`,`src`,`dst`,`dty`,`lowered_value_type ce e`,`sc`] mp_tac
       ci_mono_compile_store_memory >> simp[]) >>
  simp[]
QED

(* The address calculation is independent of the operand returned by the
   expression.  Keep the pre-unwrap operand and the new address separate. *)
Theorem make_slot_nonword_add[local]:
  emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var q s = SOME (n2w base) /\ ptr_covers G tn q s cap /\
  base + cap < dimword (:256) /\ off + n <= cap ==>
  ?out z Gf tf.
    dst = Var out /\ not_fresh_at sn out /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    z = s with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    z.vs_current_bb = sn.cs_current_bb /\ alloca_history func z /\
    lookup_var out z = SOME (n2w (base+off)) /\ ptr_covers Gf tf out z n /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s /\
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [Var q; Lit (n2w off)] [tmp]` >>
  qabbrev_tac `u = update_var tmp (n2w (base+off)) s` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  `op_taint tn (Var q) = {}` by fs[ptr_covers_def] >>
  `(!D lo explicit. allocas_from lo s ==>
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
   FLOOKUP Gf tmp = op_prov G (Var q) /\ op_taint tf (Var tmp) = {} /\
   tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!p. p <> tmp ==> FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tf (Var p) = op_taint tn (Var p))` by
    (`eval_operand (Var q) s = SOME (n2w base)` by simp[eval_operand_def] >>
     `u = update_var tmp (n2w base + n2w off) s` by simp[Abbr `u`,word_add_n2w] >>
     map_every (fn pat => qpat_assum pat
       (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (i = _)`,`Abbrev (z = _)`,`Abbrev (Gf = _)`,`Abbrev (tf = _)`] >>
     drule_all attribute_add_full_frame >>
     qpat_assum `dst = Var tmp` (fn th => pure_once_rewrite_tac[th]) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var tmp z = SOME (n2w (base+off))` by
    simp[Abbr `z`,Abbr `u`,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  `ptr_covers Gf tf tmp z n` by
    (qpat_x_assum `ptr_covers G tn q s cap` (mp_tac o REWRITE_RULE[ptr_covers_def]) >>
     `base < dimword (:256) /\ base+off < dimword (:256)` by decide_tac >>
     simp[ptr_covers_def,op_prov_def] >>
     disch_then (qx_choosel_then [`b`,`sz`] strip_assume_tac) >>
     qexistsl [`b`,`sz`] >> simp[] >> decide_tac) >>
  `alloca_history func z` by
    (qpat_x_assum `alloca_history func s`
       (strip_assume_tac o REWRITE_RULE[allocaHistoryTheory.alloca_history_def]) >>
     simp[allocaHistoryTheory.alloca_history_def,Abbr `z`,Abbr `u`,update_var_def] >>
     rpt strip_tac >>
     `k < s.vs_inst_idx \/ k = s.vs_inst_idx` by decide_tac
     >- (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl [`bb'`,`k`] >> metis_tac[]) >>
     gvs[Abbr `i`,venomInstTheory.mk_inst_def]) >>
  qexistsl [`tmp`,`z`,`Gf`,`tf`] >>
  simp[Abbr `z`,Abbr `u`,update_var_def] >>
  conj_tac
  >- (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  rpt strip_tac >>
  `p <> STRING #"%" (toString sm.cs_next_var)` by metis_tac[] >>
  simp[lookup_var_def,FLOOKUP_UPDATE,EQ_SYM_EQ]
QED

Theorem make_slot_nonword_read_mods:
  ~is_word_type dty /\
  make_slot_entry_mods mods exps src tops cenv cx env
    (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
    h xs dty dtv ps off sa sb sha shb (es,s,G,tn) /\
  compile_expr cenv (expr_type h) h sa = (vv,sm) /\
  (!tail. eval_expr cx h (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL raw,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK u,g1,tt1) /\
    make_slot_child_post_mods DF lo d ctx func cenv cx h es sa sm s G tn vv
      H (INL raw) mid g1 tt1 u) ==>
  ?out op sc v z gz tz.
    read_result cx raw mid = (INL v,mid) /\
    compile_store_memory cenv op (Var out) dty (lowered_value_type cenv h) sc = ((),sb) /\
    fn_has_code sc sb func /\ ci_mono sc sb /\
    sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,g1,tt1) [] (OK z,gz,tz) /\
      expr_post_mods H ctx func cenv cx h es sa sc s mid v op z /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid gz tz z) /\
    ghost_kept_at lo cenv es sa G tn s gz tz /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s.vs_alloca_next <= z.vs_alloca_next /\
    not_fresh_at sc out /\ lookup_var out z = SOME (n2w (base+off)) /\
    ptr_covers gz tz out z (type_memory_size dtv) /\
    ptr_val_ok cx (post_value_type cenv h) v op gz tz z /\
    ptr_buf_ok cenv h op gz z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt /\
      eval_operand op z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    (!x. op = Var x ==> not_fresh_at sc x)
Proof
  strip_tac >>
  fs[make_slot_entry_mods_def,make_elements_entry_mods_def,make_elements_cut_mods_def,
     make_elements_static_mods_def,make_elements_code_mods_def] >>
  drule_all_then strip_assume_tac make_slot_nonword_code_cuts >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (assume_tac o SIMP_RULE (srw_ss()) [make_slot_child_post_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~u.vs_halted` by
    (drule_then strip_assume_tac gas_origin_ptr_path_projections >>
     drule gas_path_ptr_ok_not_halted >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env h es` by metis_tac[listTheory.MEM] >>
  `~is_word_type (expr_type h)` by metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `?v. read_result cx raw mid = (INL v,mid)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
     pure_rewrite_tac[vv_post_mods_def] >> strip_tac >> Cases_on `vv`
     >- fs[vv_holds_mods_def,loweringPostsTheory.vv_holds_def] >>
     rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
     >- fs[vv_holds_mods_def,immutable_holds_mods_def,loweringPostsTheory.immutable_holds_def] >>
     fs[vv_holds_mods_def] >>
     drule_then strip_assume_tac bodyPtrAttributeSourceTheory.attribute_vv_holds_read_operand >> simp[]) >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE[listTheory.APPEND_NIL])) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx h) (read_result cx) (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,mid)` by simp[bind_def] >>
  drule_all bodyCopyReadPhysicalTypeModsTheory.copy_read_physical_type_gas_obs_mods >>
  disch_then (assume_tac o CONJUNCT1) >>
  `lookup_var q u = SOME (n2w base)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ u`
       (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
     first_x_assum irule >> simp[]) >>
  `ptr_covers g1 tt1 q u cap` by
    (qpat_assum `ghost_kept_at lo cenv es sa G tn s g1 tt1`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     `FLOOKUP g1 q = FLOOKUP G q /\ op_taint tt1 (Var q) = op_taint tn (Var q)` by
       (first_x_assum (qspec_then `q` mp_tac) >> simp[]) >>
     qpat_x_assum `ptr_covers G tn q s cap` (mp_tac o REWRITE_RULE[ptr_covers_def]) >>
     simp[ptr_covers_def]) >>
  drule_all (Q.INST [`s` |-> `u`, `ctx` |-> `ctx`, `G` |-> `g1`, `tn` |-> `tt1`,
    `n` |-> `type_memory_size dtv`] make_slot_nonword_add) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`out`,`a`,`Ga`,`ta`] strip_assume_tac)) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (CONJUNCT1 compiler_compile_var) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x u /\
      FLOOKUP Ga x = FLOOKUP g1 x /\ op_taint ta (Var x) = op_taint tt1 (Var x)` by
    (gen_tac >> strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!p. not_fresh_at sm p ==> lookup_var p a = _ /\ _`
       (drule_then ACCEPT_TAC)) >>
  `a.vs_memory = u.vs_memory /\ a.vs_alloca_next = u.vs_alloca_next /\
   a.vs_allocas = u.vs_allocas /\ a.vs_accounts = u.vs_accounts /\
   a.vs_call_ctx = u.vs_call_ctx /\ a.vs_transient = u.vs_transient /\
   a.vs_immutables = u.vs_immutables /\ a.vs_labels = u.vs_labels /\ ~a.vs_halted` by
    (qpat_assum `a = u with <|vs_vars := _; vs_inst_idx := _|>` (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) u /\
   op_prov Ga (vv_operand vv) = op_prov g1 (vv_operand vv) /\
   op_taint ta (vv_operand vv) = op_taint tt1 (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def,op_prov_def]
     >- simp[op_taint_def] >>
     TRY (rename1 `op_taint ta (Label _) = _` >> simp[op_taint_def] >> NO_TAC) >>
     qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at sm x` (drule_then assume_tac) >>
     qpat_assum `!p. not_fresh_at sm p ==> lookup_var p a = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `csbase` >> simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post_mods H ctx func cenv cx h es sa sn s mid raw vv a /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid Ga ta a` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (irule make_slot_vv_readonly_post_mods >> simp[] >> qexistsl [`u`,`sm`] >> fs[ci_mono_def]) >>
     drule (Q.SPECL [`DF H`,`lo`,`d`,`cenv`,`cx`] ghost_inv_at_mods_exterior_frame) >>
     disch_then irule >> simp[] >> qexists `sa` >> simp[]) >>
  `ptr_vv_ok cx (post_value_type cenv h) raw vv mid Ga ta a` by
    (qpat_assum `ptr_vv_ok _ _ _ _ _ g1 tt1 u` (mp_then Any mp_tac make_slot_vv_readonly_ptr_mods) >>
     disch_then irule >> simp[]) >>
  `vv_store_bound cx (post_value_type cenv h) (lowered_value_type cenv h) mid raw vv a` by
    (qpat_assum `vv_store_bound _ _ _ _ _ _ u` mp_tac >>
     Cases_on `vv` >> fs[vv_store_bound_def,vv_operand_def]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv h) = SOME rt /\
        eval_operand (vv_operand vv) a = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        !mem. mem_agree_outside ta.t_mem a.vs_memory mem ==> val_in_memory rt v (w2n w) mem` by
    (qpat_x_assum `_ /\ vv_location vv = SOME LocCode ==> ?v. _ /\ _` mp_tac >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s Ga ta` by
    (qpat_assum `ghost_kept_at lo cenv es sa G tn s g1 tt1`
       (mp_then Any mp_tac ghost_kept_at_clean_suffix) >>
     disch_then irule >> simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `ptr_buf_ok cenv h (vv_operand vv) g1 u ==> ptr_buf_ok cenv h (vv_operand vv) Ga a` by
    (strip_tac >> drule ptr_buf_ok_frame >> disch_then irule >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at sm x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x a = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `!tag x. vv = StackValue tag x ==> ptr_buf_ok cenv h x Ga a` by
    (rpt strip_tac >> qpat_x_assum `ptr_buf_ok _ _ (vv_operand vv) g1 u ==> _` mp_tac >>
     gvs[vv_operand_def]) >>
  `!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv h p.ptr_operand Ga a` by
    (rpt strip_tac >> qpat_x_assum `ptr_buf_ok _ _ (vv_operand vv) g1 u ==> _` mp_tac >>
     gvs[vv_operand_def]) >>
  qpat_assum `ci_mono sm sn` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
  `eval_expr cx h (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL raw,mid)` by simp[] >>
  drule_all (Q.INST [`k` |-> `sn`, `s` |-> `a`, `G` |-> `Ga`, `tn` |-> `ta`,
                     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
                ifexp_arm_nonword_unwrap_mods) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`v'`,`z`,`gz`,`tz`,`pt`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  `v' = v` by (qpat_x_assum `read_result cx raw mid = (INL v',mid)` mp_tac >> simp[]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  rename1 `unwrap_value cenv vv sn = (op,sc)` >>
  `case vv of StackValue ty rawop => (!x. rawop = Var x ==> not_fresh_at sn x)
            | LocatedValue ty p => (!x. p.ptr_operand = Var x ==> not_fresh_at sn x)` by
    (Cases_on `vv` >> fs[vv_operand_def] >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (qpat_assum `unwrap_value cenv vv sn = (op,sc)`
       (mp_then Any mp_tac compiler_unwrap_value_var) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,g1,tt1) [] (OK z,gz,tz)` by
    (gen_tac >> strip_tac >>
     `allocas_from lo u` by
       (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_x_assum `ghost_inv_at_mods (DF H) lo d cenv cx mid g1 tt1 u`
          (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def])) >>
     qpat_assum `!D lo' explicit. allocas_from lo' u ==> _`
       (qspecl_then [`DF H`,`lo`,`gas_explicit_sites ctx shadow_ctx`] (assume_tac o UNDISCH)) >>
     qpat_assum `gas_origin_ptr_path _ (u,g1,tt1) [] (OK a,Ga,ta)`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (irule o SIMP_RULE (srw_ss()) []) >> simp[]) >>
  `lookup_var out z = SOME (n2w (base + off))` by
    (qpat_assum `!x. not_fresh_at sn x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ptr_covers gz tz out z (type_memory_size dtv)` by
    (qpat_assum `!x cap. not_fresh_at sn x /\ ptr_covers Ga ta x a cap ==> _`
       (irule o GEN_ALL) >> simp[]) >>
  `not_fresh_at sc out` by
    (irule not_fresh_at_mono >> qexists `sn` >> fs[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    (qpat_assum `ci_mono sn sc` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >> decide_tac) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  map_every qexists_tac [`out`,`op`,`sc`,`v`,`z`,`gz`,`tz`] >>
  simp[arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `compile_store_memory cenv op dst dty _ sc = _` mp_tac >> simp[]
QED

(* The child path supplies the read cut.  Only the read and store paths
   belong to the continuation returned here. *)
Theorem make_slot_nonword_from_transfer_mods:
  ^(boolSyntax.list_mk_forall (free_vars (concl make_element_transfer_mods), concl make_element_transfer_mods)) ==>
  make_slot_landing_mods (\ty. ~is_word_type ty)
Proof
  disch_tac >> simp_tac bool_ss [make_slot_landing_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then (qx_choosel_then [`dst`,`op`,`sc`,`v`,`z`,`gz`,`tz`] strip_assume_tac)
    make_slot_nonword_read_mods >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx h es sa sc s mid v op z /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid gz tz z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK z,gz,tz)` by suspend "read_path" >>
  drule_all_then strip_assume_tac make_slot_read_window_mods >>
  qhdtm_assum `make_slot_entry_mods`
    (strip_assume_tac o PURE_REWRITE_RULE[make_slot_entry_mods_def,make_elements_entry_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env h es` by simp[] >>
  `body_exprs_full_ok_mods mods exps cx xs /\
   expr_sim_inv_mods mods cenv cx env mid /\
   body_const_cells_agree_mods mods cx env mid /\
   value_runtime_typed env (expr_type h) v /\
   make_elements_admissible_mods cx xs mid` by suspend "source" >>
  `bind (eval_expr cx h) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,mid)` by suspend "bind" >>
  `aid < sa.cs_next_id /\
   (!name b n. local_region cenv es.scopes s name b n ==>
      loweringStateRelDefs$regions_disjoint base cap b n)` by suspend "entry" >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx h es sa sc s mid v op z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `~is_word_type (post_value_type cenv h) ==> ptr_buf_ok cenv h op gz z` by simp[] >>
  `~is_word_type (post_value_type cenv h) ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv h) = SOME rt /\
      eval_operand op z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next` by simp[] >>
  `?t gf tf.
    (!D. gas_origin_ptr_path
      (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (z,gz,tz) [] (OK t,gf,tf)) /\
    struct_store_effects func (sc,gz,tz,z) (sb,gf,tf,t) (base+off,dtv,v) /\
    value_has_type dtv v /\ val_wf dtv v` by suspend "store" >>
  `make_elements_cut_mods DF lo d ctx func cenv cx st0
     (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sb mid t gf tf` by suspend "cut" >>
  drule_all_then strip_assume_tac make_slot_store_window_mods >>
  suspend "finish"
QED

Resume make_slot_nonword_from_transfer_mods[read_path]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (s,_,_) _ _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`u`,`g1`,`tt1`,`[]`] mp_tac) >> simp[]
QED

Resume make_slot_nonword_from_transfer_mods[source]:
  qhdtm_assum `make_elements_admissible_mods`
    (assume_tac o PURE_REWRITE_RULE[make_elements_admissible_mods_def]) >>
  drule_all struct_fields_source_cuts_mods >>
  simp[make_elements_admissible_mods_def]
QED

Resume make_slot_nonword_from_transfer_mods[bind]:
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [])) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  simp[bind_def]
QED

Resume make_slot_nonword_from_transfer_mods[entry]:
  qpat_assum `make_elements_cut_mods _ _ _ _ _ _ _ _ _ _ sa es s _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[make_elements_cut_mods_def]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume make_slot_nonword_from_transfer_mods[store]:
  drule_all make_slot_nonword_store_mods >> simp[]
QED

Resume make_slot_nonword_from_transfer_mods[cut]:
  `make_elements_static_mods mods exps src tops cenv cx env
    (DF,lo,ctx,shadow_ctx,func,shadow_func) st0 csbase ebase sbase aid sc` by
    (qhdtm_assum `make_elements_static_mods`
       (strip_assume_tac o PURE_REWRITE_RULE[make_elements_static_mods_def]) >>
     `local_ptrs_reserved cenv sc` by
       (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
     simp[make_elements_static_mods_def] >> decide_tac) >>
  `env_consistent env cx mid` by (drule expr_sim_inv_mods_env >> simp[]) >>
  drule_all make_slot_store_cut_mods >> simp[]
QED

Resume make_slot_nonword_from_transfer_mods[finish]:
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `~u.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,_,_) _ (OK u,_,_) /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s,_,_) _ (OK u,_,_)`
       (mp_then Any strip_assume_tac gas_origin_ptr_path_projections) >>
     drule gas_path_ptr_ok_not_halted >> simp[]) >>
  rewrite_tac[make_elements_run_mods_def] >> irule gas_outcome_full_mods_pure >>
  simp[] >> qexistsl [`gf`,`mid`,`INL v`,`t`,`tf`] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  conj_tac >- (drule read_result_gas_obs >> simp[]) >>
  gen_tac >> disch_tac >> conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (u,_,_) _ _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `gas_origin_ptr_path _ (u,_,_) _ _`
        (mp_then Any mp_tac gas_origin_ptr_path_append) >>
      disch_then (irule o SIMP_RULE (srw_ss()) []) >> simp[]) >>
  simp[make_slot_post_mods_def]
QED

Finalise make_slot_nonword_from_transfer_mods
