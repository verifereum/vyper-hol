Theory bodyExtRequestPackedOperandsMods
Ancestors
  bodyExtLinkedPackingHandoffMods bodyExtRequestAbiInputsMods exprSimWordArgs
  exprSafeOperand decoderGhostFramePtr exprSimProps abiEncoderWindowContract
  venomState ptrDiscipline bodyPtrDefs loweringPosts bodyPtrBopRepresentationFrame
  exprSimExtCallCase

Theorem packed_operand_word[local]:
  wb_frame ce ee ee s5 zg t /\
  ghost_kept_at lo ce ee s5 Gg tng zg Gf tf /\
  safe_operand s5 op /\ eval_operand op zg = SOME w ==>
  eval_operand op t = SOME w /\ op_taint tf op = op_taint tng op /\
  (!x. op = Var x ==> lookup_var x t = lookup_var x zg /\
                        FLOOKUP Gf x = FLOOKUP Gg x)
Proof
  Cases_on `op` >> simp[safe_operand_def,eval_operand_def] >>
  TRY (rename1 `op_taint tf (Lit _) = _` >> simp[op_taint_def] >> NO_TAC) >>
  strip_tac >> rename1 `lookup_var x zg = SOME w` >>
  `lookup_var x t = SOME w` by (drule_all wb_frame_vars >> simp[]) >>
  fs[ghost_kept_at_def]
QED

(* The common packed_frame field, restricted to a saved allocation. *)
val saved_window = ``
  !a k. (?id b sz. id < s5.cs_next_id /\
         FLOOKUP zg.vs_allocas id = SOME (b,sz) /\ b <= a /\ a+k <= b+sz) ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k zg.vs_memory /\
       (!i. a <= i /\ i < a+k /\ i IN tf.t_mem ==> i IN tng.t_mem)``;

Theorem packed_default_window[local]:
  ^saved_window /\
  val_wf tv dv /\ FLOOKUP zg.vs_allocas aid = SOME (b,type_memory_size tv) /\
  aid < s5.cs_next_id ==>
  mem_bytes_at b (val_footprint tv dv) t.vs_memory =
    mem_bytes_at b (val_footprint tv dv) zg.vs_memory /\
  (!i. b <= i /\ i < b + val_footprint tv dv /\ i IN tf.t_mem ==> i IN tng.t_mem)
Proof
  strip_tac >> drule val_footprint_le >> strip_tac >>
  qpat_assum `!a k. _ ==> _` (qspecl_then [`b`,`val_footprint tv dv`] irule) >>
  qexistsl [`aid`,`b`,`type_memory_size tv`] >> simp[]
QED

Theorem packed_memory_default[local]:
  wb_frame ce ee ee s5 zg t /\
  ghost_kept_at lo ce ee s5 Gg tng zg Gf tf /\
  s5.cs_next_id < sp.cs_next_id /\ window_alloca_growth zg t /\ ^saved_window /\
  safe_operand s5 def_op /\ ~is_word_type def_ty /\
  expr_val_rel cx def_ty dv def_op zg /\ ptr_mem_ok cx def_ty dv def_op Gg tng zg /\
  evaluate_type (get_tenv cx) def_ty = SOME tv /\ val_wf tv dv /\
  eval_operand def_op zg = SOME w /\
  FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < s5.cs_next_id /\
  (type_memory_bytes ce def_ty <> 0 ==>
    (?p. def_op = Var p /\ ptr_covers Gg tng p zg (type_memory_bytes ce def_ty)) /\
    w2n w + type_memory_bytes ce def_ty <= zg.vs_alloca_next) ==>
  expr_val_rel cx def_ty dv def_op t /\ ptr_mem_ok cx def_ty dv def_op Gf tf t /\
  eval_operand def_op t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sp.cs_next_id /\
  (type_memory_bytes ce def_ty <> 0 ==>
    (?p. def_op = Var p /\ ptr_covers Gf tf p t (type_memory_bytes ce def_ty)) /\
    w2n w + type_memory_bytes ce def_ty <= t.vs_alloca_next)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all packed_operand_word >> strip_tac >>
  drule_all packed_default_window >> strip_tac >>
  conj_tac
  >- (irule expr_val_rel_footprint_agree >> simp[] >>
      qexists `zg` >> simp[]) >>
  conj_tac
  >- (drule bop_ptr_mem_ok_frame >>
      disch_then (qspecl_then [`tv`,`tf`,`t`,`Gf`] irule) >> simp[]) >>
  asm_rewrite_tac[] >> conj_tac >- fs[wb_frame_def] >>
  conj_tac >- decide_tac >>
  strip_tac >> fs[] >> conj_tac
  >- (gvs[] >> drule_all ptr_covers_frame >> simp[]) >>
  fs[window_alloca_growth_def] >> decide_tac
QED

(* This is the default part of the post-GAS ABI-input packet.  The row is
   passed as data, not obtained by re-running the ABI-input producer. *)
val default_input = ``
  !dv. dopt = SOME dv /\ ~is_word_type def_ty ==>
    ptr_mem_ok cx def_ty dv def_op Gg tng zg /\
    (type_memory_bytes ce def_ty <> 0 ==>
      (?p. def_op = Var p /\ ptr_covers Gg tng p zg (type_memory_bytes ce def_ty)) /\
      (!w. eval_operand def_op zg = SOME w ==>
        w2n w + type_memory_bytes ce def_ty <= zg.vs_alloca_next)) /\
    (?w aid tv. eval_operand def_op zg = SOME w /\
      evaluate_type (get_tenv cx) def_ty = SOME tv /\ val_wf tv dv /\
      FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < s5.cs_next_id)``;

val default_output = ``
  !dv. dopt = SOME dv /\ ~is_word_type def_ty ==>
    ptr_mem_ok cx def_ty dv def_op Gf tf t /\
    (type_memory_bytes ce def_ty <> 0 ==>
      (?p. def_op = Var p /\ ptr_covers Gf tf p t (type_memory_bytes ce def_ty)) /\
      (!w. eval_operand def_op t = SOME w ==>
        w2n w + type_memory_bytes ce def_ty <= t.vs_alloca_next)) /\
    (?w aid tv. eval_operand def_op zg = SOME w /\ eval_operand def_op t = SOME w /\
      evaluate_type (get_tenv cx) def_ty = SOME tv /\ val_wf tv dv /\
      FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sp.cs_next_id)``;

Theorem packed_default_ready[local]:
  wb_frame ce ee ee s5 zg t /\
  ghost_kept_at lo ce ee s5 Gg tng zg Gf tf /\
  s5.cs_next_id < sp.cs_next_id /\ window_alloca_growth zg t /\ ^saved_window /\
  safe_operand s5 def_op /\ extcall_default_ready cx rt has_def def_op def_ty dopt zg /\
  ^default_input ==>
  extcall_default_ready cx rt has_def def_op def_ty dopt t /\ ^default_output
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `dopt` >- fs[extcall_default_ready_def] >>
  rename1 `SOME dv` >>
  qhdtm_x_assum `extcall_default_ready`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [extcall_default_ready_def]) >>
  drule_all packed_operand_word >> strip_tac >>
  Cases_on `is_word_type def_ty`
  >- gvs[extcall_default_ready_def,expr_val_rel_def] >>
  qpat_x_assum `!dv'. _ ==> ptr_mem_ok _ _ _ _ _ _ zg /\ _`
    (qspec_then `dv` mp_tac) >>
  simp[] >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  `expr_val_rel cx def_ty dv def_op t /\ ptr_mem_ok cx def_ty dv def_op Gf tf t /\
   FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < sp.cs_next_id /\
   (type_memory_bytes ce def_ty <> 0 ==>
     (?p. def_op = Var p /\ ptr_covers Gf tf p t (type_memory_bytes ce def_ty)) /\
     w2n w + type_memory_bytes ce def_ty <= t.vs_alloca_next)` by
    (drule_all packed_memory_default >> simp[]) >>
  `w2n w + val_footprint tv dv <= t.vs_alloca_next` by
    (fs[window_alloca_growth_def] >> decide_tac) >>
  simp[extcall_default_ready_def] >> qexists `aid` >> simp[]
QED

(* Old operands at the physical packing boundary, independently of whether
   the selected packet encoded a payload. *)
Theorem ext_request_packed_operands_mods:
  wb_frame ce ee ee s5 zg t /\
  ghost_kept_at lo ce ee s5 Gg tng zg Gf tf /\
  s5.cs_next_var <= sp.cs_next_var /\ s5.cs_next_id < sp.cs_next_id /\
  window_alloca_growth zg t /\ ^saved_window /\
  EVERY (safe_operand s5) [addr;value;gas;def_op] /\
  EVERY (\p. op_taint tng p = {}) [addr;value;gas;def_op] /\
  eval_operand addr zg = SOME aw /\ w2w aw = target /\
  (stat <=> value_opt = NONE) /\
  (?vw. eval_operand value zg = SOME vw /\
        w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
  eval_operand gas zg = SOME gw /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
  extcall_default_ready cx rt has_def def_op def_ty dopt zg /\ ^default_input ==>
  EVERY (safe_operand sp) [addr;value;gas;def_op] /\
  EVERY (\p. op_taint tf p = {}) [addr;value;gas;def_op] /\
  (!op w. MEM op [addr;value;gas;def_op] /\ eval_operand op zg = SOME w ==>
    eval_operand op t = SOME w /\
    (!x. op = Var x ==> lookup_var x t = lookup_var x zg /\ FLOOKUP Gf x = FLOOKUP Gg x)) /\
  eval_operand addr t = SOME aw /\ w2w aw = target /\
  (stat <=> value_opt = NONE) /\
  (?vw. eval_operand value t = SOME vw /\
        w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
  eval_operand gas t = SOME gw /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
  extcall_default_ready cx rt has_def def_op def_ty dopt t /\ ^default_output
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `safe_operand s5 def_op` by fs[] >>
  drule_all packed_default_ready >> strip_tac >>
  `!op w. MEM op [addr;value;gas;def_op] /\ eval_operand op zg = SOME w ==>
    eval_operand op t = SOME w /\
    (!x. op = Var x ==> lookup_var x t = lookup_var x zg /\ FLOOKUP Gf x = FLOOKUP Gg x)` by
    (rpt strip_tac >> `safe_operand s5 op` by fs[listTheory.EVERY_MEM] >>
     drule_all packed_operand_word >> simp[]) >>
  `EVERY (safe_operand sp) [addr;value;gas;def_op]` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule safe_operand_mono >> qexists `s5` >> fs[listTheory.EVERY_MEM]) >>
  `!p. safe_operand s5 p /\ op_taint tng p = {} ==> op_taint tf p = {}` by
    (Cases >> fs[safe_operand_def,op_taint_def,ghost_kept_at_def]) >>
  `EVERY (\p. op_taint tf p = {}) [addr;value;gas;def_op]` by
    (simp[] >> rpt conj_tac >> first_x_assum irule >> fs[]) >>
  qpat_x_assum `?vw. eval_operand value zg = SOME vw /\ _`
    (qx_choose_then `vw` strip_assume_tac) >>
  asm_rewrite_tac[] >>
  qpat_assum `!op w. MEM op _ /\ _ ==> _` (fn th =>
    map_every (fn args => qspecl_then args mp_tac th)
      [[`addr`,`aw`],[`value`,`vw`],[`gas`,`gw`]]) >>
  simp[] >> rpt strip_tac >> qexists `vw` >> simp[]
QED
