(* Source and compiler preparation for the counted local DynArray producer.
   The loop runs in the outer frame sc; the length register lv, loaded once
   before the loop, is carried by the loop invariant. *)
Theory bodyIntCallFamStmtForDynArraySetup
Ancestors
  whitelistForIterDynFrag whitelistForIterDynLoop bodyDynArraySource
  bodyIntCallFamStmtForArrayResources bodyIntCallJointContract
  bodyIntCallFamStmtForTransport bodyIntCallFamStmtForStart
  bodyIntCallJointStmtJump bodyIntCallJointStmtBoundary
  stmtSimForArrayLoop stmtSimForArray stmtSimProps exprLoweringProps
  compileEnv loweringStateRelDefs loweringPosts abiDecoderLoopCode
  venomState venomExecSemantics venomInst vyperInterpreter vyperState
  vyperValue finite_map list rich_list arithmetic

(* Pure iterator preparation emits no source gas events. *)
Theorem intcall_dynarray_eval_for_source:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs <= n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) ==>
  !gs. eval_stmt cx (For id et it n stmts) (es with gas_obs := gs) =
    eval_for cx tv id stmts vs (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  simp[Once evaluate_def, lift_option_type_def, bind_def, return_def,
       ignore_bind_def, check_def, compatible_bound_def, assert_def]
QED

Theorem intcall_dynarray_for_admissible:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs <= n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) /\
  gas_admissible (eval_stmt cx (For id et it n stmts)) ok es ==>
  gas_admissible (eval_for cx tv id stmts vs) ok es
Proof
  strip_tac >> drule_all intcall_dynarray_eval_for_source >>
  strip_tac >> fs[gasContextTheory.gas_admissible_def] >> metis_tac[]
QED

(* Load the length, allocate the element slot, zero the index and pass the
   capacity check, at the concrete resource endpoint. *)
Theorem intcall_dynarray_initial_invariant:
  ainst = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\ sz < dimword (:256) /\
  MEM ainst (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry fp.jc_func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\
  ALL_DISTINCT [lv; p; idx; g; vld] /\
  not_local_ptr ce es.scopes lv /\ not_local_ptr ce es.scopes p /\
  not_local_ptr ce es.scopes idx /\ not_local_ptr ce es.scopes g /\
  not_local_ptr ce es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv; p; idx; g; vld]) /\
  (!x. not_fresh_at sc x ==> ~MEM x [lv; p; idx; g; vld]) ==>
  ?dst cc. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved_base
      array_base p dst sz ainst cond sc 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    intcall_joint_res fp ce env es sc cc /\
    array_caller_frame sc s0 cc /\ s0.vs_alloca_next <= cc.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\ ret_pc_ok ce sc s0` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
   ainst.inst_operands = [Lit (n2w sz)]` by simp[mk_inst_def] >>
  drule_all dynarray_loop_initialize_explicit >> strip_tac >>
  `~not_fresh_at sc lv /\ ~not_fresh_at sc p /\ ~not_fresh_at sc idx /\
   ~not_fresh_at sc g /\ ~not_fresh_at sc vld` by
    (rpt conj_tac >> strip_tac >>
     qpat_x_assum `!x. not_fresh_at sc x ==> ~MEM _ _` drule >> simp[]) >>
  `!x. fp.jc_reserved (Var x) ==> not_fresh_at sc x` by
    (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `~fp.jc_reserved (Var lv) /\ ~fp.jc_reserved (Var p) /\
   ~fp.jc_reserved (Var idx) /\ ~fp.jc_reserved (Var g) /\
   ~fp.jc_reserved (Var vld)` by
    (rpt conj_tac >> strip_tac >> metis_tac[]) >>
  `intcall_joint_res fp ce env es sc (update_var lv (n2w (LENGTH vs)) s0)` by
    (irule intcall_joint_res_update_var >> simp[]) >>
  `intcall_joint_res fp ce env es sc s1` by
    (irule intcall_joint_res_exec_alloca >> simp[] >>
     qexistsl_tac [`ainst`, `n2w sz`, `p`,
       `update_var lv (n2w (LENGTH vs)) s0`] >> simp[]) >>
  `intcall_joint_res fp ce env es sc cc` by
    (qpat_x_assum `cc = _` SUBST1_TAC >>
     simp[intcall_joint_res_jump_to] >>
     rpt (irule intcall_joint_res_update_var >> simp[]) >>
     simp[intcall_joint_res_jump_to]) >>
  `s0.vs_alloca_next <= cc.vs_alloca_next` by
    (qpat_x_assum `exec_alloca _ _ _ = OK s1` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >>
     simp[update_var_def, jump_to_def]) >>
  qexistsl_tac [`dst`, `cc`] >> simp[]
QED

(* The compiled DynArray loop from the intcall entry state: the code shape,
   the frame st1 that holds the length register, and the loop invariant at
   iteration 0 in the outer frame sc. *)
Theorem intcall_dynarray_compiler_entry:
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ip) arrsz) /\
  compile_stmt ce lctx ty
    (For id fty (Array (Name (ArrayT fty (Dynamic c)) name)) n stmts) sc =
    ((),sf) /\ ce.ce_alloca_locals /\ fn_has_code sc sf fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes ce fty = type_memory_size tv /\
  type_memory_bytes ce fty + 64 < dimword (:256) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts /\
  FLOOKUP ce.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  lookup_scopes name es.scopes = SOME snapshot /\
  snapshot.type = ArrayTV tv (Dynamic c) /\
  snapshot.value = ArrayV (DynArrayV vs) /\
  value_has_type snapshot.type snapshot.value /\
  LENGTH vs <= c /\ c < dimword (:256) ==>
  ?st1 bc lv p idx dv ov tot ep nv cond bod incr exit sa sb0 sb1 sj aa sd
   bb arrbase dst cc.
    dynarray_for_code fp.jc_func ce bc ty stmts id fty tv
      (type_memory_bytes ce fty) (Var ip) p (type_memory_bytes ce fty)
      aa idx dv ov tot ep nv lv cond exit bod incr
      (sc.cs_next_id + 8) (sc.cs_next_id + 9) (sc.cs_next_id + 10)
      (sc.cs_next_id + 11) (sc.cs_next_id + 12)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    sf.cs_current_bb = exit /\ sf.cs_current_insts = [] /\
    declare_local ce id fty st1 = (bc,sd) /\
    sc.cs_next_var <= sb0.cs_next_var /\ not_fresh_at sa lv /\
    (!x. not_fresh_at sc x ==>
      not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
    (!x. not_fresh_at sc x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
    (!x. x = p \/ Var lv = Var x \/ Var ip = Var x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
    not_fresh_at sb0 idx /\
    (!op. fp.jc_reserved op ==> op <> Var dv /\ op <> Var idx /\ op <> Var nv) /\
    (!scopes. lookup_scopes id scopes = NONE ==>
      not_local_ptr bc (FEMPTY :: scopes) p) /\
    lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions /\
    (!k ee s lbl. k < LENGTH vs /\
      array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
        (\ee. lookup_scopes name ee.scopes = SOME snapshot)
        vs id idx (Var ip) arrbase p dst (type_memory_bytes ce fty) aa lbl
        sc k ee s ==>
      val_in_memory tv (EL k vs)
        (w2n arrbase + 32 + k * type_memory_bytes ce fty) s.vs_memory /\
      w2n arrbase + 32 + k * type_memory_bytes ce fty < dimword (:256)) /\
    gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
      (\ee. lookup_scopes name ee.scopes = SOME snapshot)
      vs id idx (Var ip) arrbase p dst (type_memory_bytes ce fty) aa cond
      sc 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    intcall_joint_res fp ce env es sc cc /\
    (!x z. not_fresh_at sc x /\ lookup_var x s0 = SOME z ==>
      lookup_var x cc = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP cc.vs_allocas aid = SOME b) /\
    s0.vs_alloca_next <= cc.vs_alloca_next
Proof
  strip_tac >>
  `local_ptrs_reserved ce sc /\ ret_pc_ok ce sc s0 /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by simp[] >>
  drule_all compile_for_dynarray_code_ready >> strip_tac >>
  `cs_extends sb0 sb1 /\ sb0.cs_next_var <= sb1.cs_next_var` by
    (fs[dynarray_for_code_def] >> metis_tac[]) >>
  `?bb. lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (irule abi_decoder_code_entry_prefix >> qexists_tac `sb1` >>
     fs[dynarray_for_code_def]) >>
  `sc.cs_next_var <= st1.cs_next_var` by
    (spose_not_then assume_tac >>
     `not_fresh_at sc (STRING #"%" (toString st1.cs_next_var))` by
       simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
     qpat_x_assum `!x. not_fresh_at sc x ==> not_fresh_at st1 x` drule >>
     rewrite_tac[not_fresh_at_def] >>
     disch_then (qspec_then `st1.cs_next_var` mp_tac) >> simp[]) >>
  `st1.cs_next_var <= sb0.cs_next_var` by
    (spose_not_then assume_tac >>
     `not_fresh_at st1 (STRING #"%" (toString sb0.cs_next_var))` by
       simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
     qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ _` drule >>
     rewrite_tac[not_fresh_at_def] >> strip_tac >>
     first_x_assum (qspec_then `sb0.cs_next_var` mp_tac) >> simp[]) >>
  `not_fresh_at sc ip` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all dynarray_snapshot_memory >> strip_tac >>
  rename1 `eval_operand (Var ip) s0 = SOME arrbase` >>
  `not_local_ptr ce es.scopes p` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `not_local_ptr ce es.scopes lv /\ not_local_ptr ce es.scopes idx /\
   not_local_ptr ce es.scopes g /\ not_local_ptr ce es.scopes vld` by
    simp[] >>
  `lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
     SOME <|bb_label := sc.cs_current_bb; bb_instructions :=
       sc.cs_current_insts ++
       [mk_inst sc.cs_next_id MLOAD [Var ip] [lv]; ainst;
        mk_inst (sc.cs_next_id + 2) JMP [Label entry] []]|>` by simp[] >>
  `type_memory_bytes ce fty < dimword (:256)` by simp[] >>
  `MEM ainst (fn_insts fp.jc_func)` by
    (qhdtm_x_assum `dynarray_for_code` mp_tac >>
     rewrite_tac[dynarray_for_code_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all (BETA_RULE (Q.INST
    [`P` |-> `\ee. lookup_scopes name ee.scopes = SOME snapshot`]
    intcall_dynarray_initial_invariant)) >>
  strip_tac >>
  `!scopes. lookup_scopes id scopes = NONE ==>
     not_local_ptr bc (FEMPTY :: scopes) p` by
    (rpt strip_tac >>
        `not_local_ptr ce (FEMPTY::scopes) p` by
          (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
        `bc.ce_imm_alloca = ce.ce_imm_alloca` by
          (qhdtm_x_assum `dynarray_for_code`
             (strip_assume_tac o REWRITE_RULE [dynarray_for_code_def]) >>
           qpat_x_assum `_ with <|ce_vars := _; ce_var_type := _;
                                 ce_dynarray_capacity := _|> = _`
             (mp_tac o Q.AP_TERM `\c. c.ce_imm_alloca`) >> simp[]) >>
        irule localPtrsPropsTheory.not_local_ptr_name_update >>
        qexistsl_tac [`ce`, `id`] >> simp[] >> fs[dynarray_for_code_def]) >>
  `!k ee s lbl. k < LENGTH vs /\
     array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
       (\ee. lookup_scopes name ee.scopes = SOME snapshot)
       vs id idx (Var ip) arrbase p dst (type_memory_bytes ce fty) ainst lbl
       sc k ee s ==>
     val_in_memory tv (EL k vs)
       (w2n arrbase + 32 + k * type_memory_bytes ce fty) s.vs_memory /\
     w2n arrbase + 32 + k * type_memory_bytes ce fty < dimword (:256)` by
    (rpt gen_tac >> strip_tac >> fs[array_loop_inv_def] >>
        qpat_x_assum `stmt_state_rel _ _ _ _ ee s` assume_tac >>
        drule_all dynarray_snapshot_memory >> strip_tac >>
        gvs[eval_operand_def] >>
        `w2n arrbase + 32 + k * type_memory_size tv =
         w2n arrbase + (k * type_memory_size tv + 32)` by simp[] >>
        metis_tac[]) >>
  `sc.cs_next_var <= sb0.cs_next_var` by simp[] >>
  `not_fresh_at sa lv` by
    (qpat_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ _`
       (qspec_then `lv` mp_tac) >>
     simp[]) >>
  `(!x. not_fresh_at sc x ==>
      not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
   (!x. not_fresh_at sc x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv)` by
    (qpat_assum `!x. not_fresh_at sc x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `not_fresh_at sb0 ip` by
    (qpat_assum `!x. not_fresh_at sc x ==> not_fresh_at sb0 x /\ _`
       (qspec_then `ip` mp_tac) >> simp[]) >>
  `!x. x = p \/ Var lv = Var x \/ Var ip = Var x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv` by
    (qhdtm_assum `dynarray_for_code` mp_tac >>
     qpat_assum `not_fresh_at sb0 p` mp_tac >>
     qpat_assum `not_fresh_at sb0 ip` mp_tac >>
     qpat_assum `not_fresh_at st1 lv` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[dynarray_for_code_def] >>
     rpt strip_tac >> gvs[]) >>
  `!op. fp.jc_reserved op ==> op <> Var dv /\ op <> Var idx /\ op <> Var nv` by
    (qpat_assum `!x. not_fresh_at sc x ==> not_fresh_at sb0 x /\ _` mp_tac >>
     qpat_assum `intcall_joint_res _ _ _ _ sc s0` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[intcall_joint_res_def, intcall_expr_res_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`st1`, `bc`, `lv`, `p`, `idx`, `dv`, `ov`, `tot`, `ep`, `nv`,
    `cond`, `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`, `ainst`, `sd`,
    `bb`, `arrbase`, `dst`, `cc`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  fs[array_caller_frame_def]
QED
