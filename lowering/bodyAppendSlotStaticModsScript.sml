(* The static storage/transient Append suffix, after the address is placed. *)
Theory bodyAppendSlotStaticMods
Ancestors
  bodyFullStoreSlotsStatic bodyFullStoreSlotsAddresses augAssignFullStore
  fragGasOriginPtrLoop fragExec ptrDiscipline venomState venomInst
  stmtLoweringMono exprOperandVar exprLoweringProps stmtLowering
  valueEncodingDefs vyperTypeValues vyperStorage vyperValue
  compileEnv loweringStateRelDefs finite_map pred_set words

Theorem append_slot_static_operand[local]:
  (!x. op = Var x ==> not_fresh_at a x) /\
  (!x. not_fresh_at a x ==>
    lookup_var x t = lookup_var x s /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  t.vs_labels = s.vs_labels /\ eval_operand op s = SOME w /\ op_taint tn op = {} ==>
  eval_operand op t = SOME w /\ op_taint tf op = {}
Proof
  Cases_on `op` >> simp[eval_operand_def, op_taint_def] >> metis_tac[]
QED

Theorem append_slot_static_halt_fmp[local]:
  allocas_below_fmp (halt_state (set_returndata [] u)) <=> allocas_below_fmp u
Proof
  simp[allocas_below_fmp_def, halt_state_def, set_returndata_def]
QED

(* This tail still executes when the payload copy contains no stores. *)
Theorem append_slot_static_header[local]:
  emit_op ADD [lop;Lit 1w] sb = (nop,sc) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] sc = ((),sd) /\
  fn_has_code sb sc func /\ fn_has_code sc sd func /\
  (!x. bop = Var x ==> not_fresh_at sb x) /\
  eval_operand lop t = SOME len /\ op_taint tf lop = {} /\
  eval_operand bop t = SOME slot /\ op_taint tf bop = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  t.vs_call_ctx.cc_static /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gf,tf) []
      (Abort ExHalt_abort (halt_state (set_returndata [] u)),Gu,tu)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (halt_state (set_returndata [] u)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `eval_operand (Lit 1w) t = SOME 1w /\ op_taint tf (Lit 1w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`,`w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gf`]
    (qx_choose_then `out` (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK u,_,_)` >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK u,Gu,_)` >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK u,Gu,tu)` >>
  `eval_operand bop u = SOME slot /\ op_taint tu bop = {}` by
    (irule append_slot_static_operand >> qexistsl_tac [`sb`,`t`,`tf`] >>
     simp[Abbr `u`,update_var_def]) >>
  `eval_operand nop u = SOME (len+1w) /\ allocas_from lo u /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ u.vs_call_ctx.cc_static /\
   ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
   u.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (qpat_assum `allocas_from lo t` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
     simp[Abbr `u`,eval_operand_def,lookup_var_def,allocas_from_def,
          allocas_below_fmp_def,update_var_def,FLOOKUP_UPDATE]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) []
    (Abort ExHalt_abort (halt_state (set_returndata [] u)),Gu,tu)` by
    (gen_tac >> irule storage_emit_static_origin_ptr >>
     simp[] >> goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> reverse conj_tac
  >- simp[append_slot_static_halt_fmp] >>
  gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED

Theorem append_slot_static_tail_mods:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
    ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  emit_op ADD [lop;Lit 1w] sb = (nop,sc) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] sc = ((),sd) /\
  fn_has_code sb sc func /\ fn_has_code sc sd func /\
  (type_slot_size tv = 0 ==>
    (!x. bop = Var x \/ lop = Var x ==> not_fresh_at sa x) /\
    eval_operand lop s = SOME len /\ op_taint tn lop = {} /\
    eval_operand bop s = SOME slot /\ op_taint tn bop = {}) ==>
  ?blocked Gb tb.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort (halt_state (set_returndata [] blocked)),Gb,tb)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (halt_state (set_returndata [] blocked)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_store_slots_static_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[bodyFullStoreSlotsFrameTheory.store_slots_normalize_allocas_below_fmp] >>
  Cases_on `type_slot_size tv = 0`
  >- suspend "header" >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  simp[append_slot_static_halt_fmp] >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` mp_tac >> simp[]
QED

Resume append_slot_static_tail_mods[header]:
  qpat_x_assum `type_slot_size tv = 0 ==> (!x. _ ==> _) /\ _`
    (drule_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `eval_operand lop t = SOME len /\ op_taint tf lop = {}` by
    (irule append_slot_static_operand >> qexistsl_tac [`sa`,`s`,`tn`] >>
     simp[] >> rpt strip_tac >> res_tac) >>
  `eval_operand bop t = SOME slot /\ op_taint tf bop = {}` by
    (irule append_slot_static_operand >> qexistsl_tac [`sa`,`s`,`tn`] >>
     simp[] >> rpt strip_tac >> res_tac) >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_store_slots, pairTheory.SND] >>
  `!x. bop = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `sa` >> simp[]) >>
  `allocas_from lo t` by (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  `t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    fs[] >>
  `t.vs_call_ctx.cc_static` by simp[] >>
  drule_all append_slot_static_header >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gf`]
    (qx_choosel_then [`blocked`,`Gb`,`tb`] strip_assume_tac)) >>
  qexistsl_tac [`blocked`,`Gb`,`tb`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gf`,`t`,`tf`] >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` mp_tac >> simp[]
QED

Finalise append_slot_static_tail_mods
