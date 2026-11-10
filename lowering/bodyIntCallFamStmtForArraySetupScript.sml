(* Source preparation for the counted Array producer. *)
Theory bodyIntCallFamStmtForArraySetup
Ancestors
  bodyIntCallFamStmtForArrayProducer stmtSimForArray bodySim
  exprSimHypsDefs vyperTyping vyperTypeSystem vyperTypeInvariants
  vyperInterpreter vyperState vyperValue vyperArray finite_map list
  bodyIntCallFamStmtForArrayResources bodyIntCallJointContract
  stmtSimForArrayLoop venomState venomExecSemantics venomInst exprSimDefs
  exprSimMemDefs exprSimWordArgs stmtSimForArrayFrag stmtSimProps
  compileEnv exprLoweringProps loweringPosts rich_list abiDecoderLoopCode

Theorem intcall_array_source_inputs:
  supported_stmt tops bindings (For id fty (Array arr) bound stmts) /\
  type_stmt env ret_ty (For id fty (Array arr) bound stmts) = SOME env' /\
  expr_sim_inv ce cx env es /\ ce_locals_declared ce env ==>
  ?name env_b snapshot tv ptr sz al vs.
    arr = Name (ArrayT fty (Fixed bound)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT fty (Fixed bound)) name) /\
    assignable_type env.type_defs fty /\ id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT fty (Fixed bound)) name)) stmts /\
    type_stmts (extend_local env id fty F) ret_ty stmts = SOME env_b /\
    supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    lookup_scopes name es.scopes = SOME snapshot /\
    evaluate_type (get_tenv cx) fty = SOME tv /\
    snapshot.type = ArrayTV tv (Fixed bound) /\
    value_has_type snapshot.type snapshot.value /\
    well_formed_type_value snapshot.type /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    ce.ce_var_type name = SOME (ArrayT fty (Fixed bound)) /\
    0 < bound /\ bound < dimword (:256) /\
    snapshot.value = ArrayV (SArrayV al) /\
    vs = array_elements (ArrayTV tv (Fixed bound)) (SArrayV al) /\
    LENGTH vs = bound /\
    (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
    (!gs. eval_iterator cx (Array arr) (es with gas_obs := gs) =
      (INL vs, es with gas_obs := gs)) /\
    FLOOKUP ce.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> drule_all array_for_hypotheses >> strip_tac >> gvs[] >>
  drule_all array_name_local_binding >> strip_tac >>
  `?al. entry.value = ArrayV (SArrayV al)` by
    (qpat_x_assum `value_has_type entry.type entry.value` mp_tac >>
     simp[] >> Cases_on `entry.value` >> simp[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >>
     Cases_on `av` >> simp[value_has_type_def]) >>
  rename1 `entry.value = ArrayV (SArrayV al)` >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var arrptr) arrsz)` >>
  `evaluate_type (get_tenv cx) (ArrayT fty (Fixed bound)) = SOME entry.type` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
        well_typed_expr_def] >> metis_tac[]) >>
  qexistsl [`entry`, `elem_tv`, `arrptr`, `arrsz`, `al`] >> simp[] >>
  simp[fixed_array_elements_length] >>
  conj_tac >-
    (gen_tac >> disch_tac >> fs[] >>
     metis_tac[fixed_array_elements_typed]) >>
  conj_tac >-
    (gen_tac >> irule eval_iterator_fixed_name >>
     simp[] >> metis_tac[]) >>
  conj_tac >-
    (fs[ce_locals_declared_def] >>
     Cases_on `FLOOKUP ce.ce_vars id` >> metis_tac[]) >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
     FLOOKUP_DEF] >>
  Cases_on `lookup_scopes id es.scopes` >> gvs[] >> metis_tac[]
QED

(* Pure iterator preparation emits no source gas events. *)
Theorem intcall_array_eval_for_source:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs = n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) ==>
  !gs. eval_stmt cx (For id et it n stmts) (es with gas_obs := gs) =
    eval_for cx tv id stmts vs (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  simp[Once evaluate_def, lift_option_type_def, bind_def, return_def,
       ignore_bind_def, check_def, compatible_bound_def, assert_def]
QED

Theorem intcall_array_for_admissible:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs = n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) /\
  gas_admissible (eval_stmt cx (For id et it n stmts)) ok es ==>
  gas_admissible (eval_for cx tv id stmts vs) ok es
Proof
  strip_tac >> drule_all intcall_array_eval_for_source >>
  strip_tac >> fs[gasContextTheory.gas_admissible_def] >> metis_tac[]
QED

(* Lift the concrete initial allocation endpoint to invariant zero. *)
Theorem intcall_array_initial_invariant:
  aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [aa; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry fp.jc_func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst i ASSIGN [Lit 0w] [idx]; mk_inst j' JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s0 /\
  local_ptrs_reserved ce sc /\ MEM aa (fn_insts fp.jc_func) /\
  fn_inst_ids_distinct fp.jc_func /\ p <> idx /\
  not_local_ptr ce es.scopes p /\ not_local_ptr ce es.scopes idx /\
  (!x. not_fresh_at sc x ==> x <> p /\ x <> idx) /\
  lookup_scopes id es.scopes = NONE /\ P es /\
  not_fresh_at sc ip /\ lookup_var ip s0 = SOME arrbase ==>
  ?cc dst. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx (Var ip)
      arrbase p dst sz aa cond sc 0 es cc /\
    intcall_joint_res fp ce env es sc cc /\
    (!x z. not_fresh_at sc x /\ lookup_var x s0 = SOME z ==>
       lookup_var x cc = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
       FLOOKUP cc.vs_allocas aid = SOME b) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels
Proof
  strip_tac >> drule_all intcall_array_start_no_history >> strip_tac >>
  qexistsl_tac [`cc`, `w`] >> simp[] >>
  fs[array_loop_inv_def, intcall_joint_res_def, intcall_expr_res_def,
     eval_operand_def, mk_inst_def] >> metis_tac[]
QED

(* Static layout and the actual zero-cost initialization share one endpoint.
   The saved array is a live local, so its snapshot is encoded at every
   invariant state, not only at the initial state. *)
Theorem intcall_array_compiler_entry:
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ip) arrsz) /\
  compile_stmt ce lctx ty
    (For id fty (Array (Name (ArrayT fty (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts)
    sc = ((),sf) /\ ce.ce_alloca_locals /\ fn_has_code sc sf fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes ce fty = type_memory_size tv /\
  32 <= type_memory_bytes ce fty /\
  type_memory_bytes ce fty + 64 < dimword (:256) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts /\
  FLOOKUP ce.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  lookup_scopes name es.scopes = SOME snapshot /\
  snapshot.type = ArrayTV tv (Fixed (LENGTH vs)) /\
  snapshot.value = ArrayV (SArrayV al) /\
  vs = array_elements (ArrayTV tv (Fixed (LENGTH vs))) (SArrayV al) ==>
  ?bc p idx dv ov ep nv cond bod incr exit sa sb0 sb1 sj aa sd bb base dst cc.
    array_for_code fp.jc_func ce bc ty stmts id fty tv (LENGTH vs)
      (type_memory_bytes ce fty) (Var ip) p (type_memory_bytes ce fty)
      aa idx dv ov ep nv cond exit bod incr
      (sc.cs_next_id + 4) (sc.cs_next_id + 5)
      (sc.cs_next_id + 6) (sc.cs_next_id + 7)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    sf.cs_current_bb = exit /\ sf.cs_current_insts = [] /\
    declare_local ce id fty sc = (bc,sd) /\
    (!x. not_fresh_at sc x ==> not_fresh_at sa x /\
      not_fresh_at sb0 x /\ x <> dv /\ x <> ov /\ x <> ep /\ x <> idx /\ x <> nv) /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\ not_fresh_at sb0 ip /\
    sc.cs_next_var <= sb0.cs_next_var /\
    (!op. fp.jc_reserved op ==> op <> Var dv /\ op <> Var idx /\ op <> Var nv) /\
    (!scopes. lookup_scopes id scopes = NONE ==>
      not_local_ptr bc (FEMPTY :: scopes) p) /\
    lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions /\
    (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
      not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
    (!k ee s lbl. k < LENGTH vs /\
      array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
        (\ee. lookup_scopes name ee.scopes = SOME snapshot)
        vs id idx (Var ip) base p dst (type_memory_bytes ce fty) aa lbl sc k ee s ==>
      val_in_memory tv (EL k vs) (w2n base + k * type_memory_bytes ce fty) s.vs_memory /\
      w2n base + k * type_memory_bytes ce fty < dimword (:256) /\
      ret_pc_ok bc sb0 s) /\
    gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
      (\ee. lookup_scopes name ee.scopes = SOME snapshot)
      vs id idx (Var ip) base p dst (type_memory_bytes ce fty) aa cond sc 0 es cc /\
    intcall_joint_res fp ce env es sc cc /\
    (!x z. not_fresh_at sc x /\ lookup_var x s0 = SOME z ==> lookup_var x cc = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP cc.vs_allocas aid = SOME b) /\
    s0.vs_alloca_next <= cc.vs_alloca_next
Proof
  strip_tac >>
  `local_ptrs_reserved ce sc /\ ret_pc_ok ce sc s0 /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by simp[] >>
  drule_all compile_for_array_code_ready_framed >> strip_tac >>
  `bc.ce_return_pc = ce.ce_return_pc` by
    (fs[array_for_code_def] >>
     qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = _`
       (mp_tac o Q.AP_TERM `\c. c.ce_return_pc`) >> simp[]) >>
  `cs_extends sb0 sb1 /\ sb0.cs_next_var <= sb1.cs_next_var` by
    (fs[array_for_code_def] >> metis_tac[]) >>
  `?bb. lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (irule abi_decoder_code_entry_prefix >> qexists_tac `sb1` >>
     fs[array_for_code_def]) >>
  `not_fresh_at sc ip` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `?base. lookup_var ip s0 = SOME base` by
    (drule_all array_snapshot_memory >> simp[eval_operand_def] >> metis_tac[]) >>
  `not_local_ptr ce es.scopes p` by
    (fs[array_for_code_def, not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `not_local_ptr ce es.scopes idx /\ p <> idx /\ MEM ainst (fn_insts fp.jc_func)` by
    (fs[array_for_code_def] >> metis_tac[]) >>
  rename1 `lookup_var ip s0 = SOME arrbase` >>
  `?cc dst. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
      (\ee. lookup_scopes name ee.scopes = SOME snapshot)
      vs id idx (Var ip) arrbase p dst (type_memory_bytes ce fty) ainst cond sc 0 es cc /\
    intcall_joint_res fp ce env es sc cc /\
    (!x z. not_fresh_at sc x /\ lookup_var x s0 = SOME z ==> lookup_var x cc = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP cc.vs_allocas aid = SOME b) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels` by
    (irule intcall_array_initial_invariant >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`bc`, `p`, `idx`, `dv`, `ov`, `ep`, `nv`, `cond`, `bod`,
    `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`, `ainst`, `sd`, `bb`, `arrbase`, `dst`, `cc`] >>
  simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       (fs[intcall_frame_ok_def] >> metis_tac[]) >>
     `not_fresh_at sc x` by
       (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
     gvs[] >>
     first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `not_local_ptr ce (FEMPTY::scopes) p` by
       (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     `bc.ce_imm_alloca = ce.ce_imm_alloca` by
       (fs[array_for_code_def] >>
        qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = _`
          (mp_tac o Q.AP_TERM `\c. c.ce_imm_alloca`) >> simp[]) >>
     irule localPtrsPropsTheory.not_local_ptr_name_update >>
     qexistsl_tac [`ce`, `id`] >> simp[] >> fs[array_for_code_def]) >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at sc x` by (fs[ret_pc_ok_def] >> metis_tac[]) >>
     metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  fs[array_loop_inv_def] >>
  `ret_pc_ok bc sb0 s` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`ce`, `s`, `sc`] >> simp[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ ee s` assume_tac >>
  drule_all array_snapshot_memory >>
  strip_tac >> gvs[eval_operand_def] >> metis_tac[]
QED
