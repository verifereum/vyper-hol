(* Joint resources from the start of an immutable-array For to its first
   condition test: the optional length load, the element-slot allocation
   and the index initialisation. *)
Theory bodyIntCallFamStmtForImmEntry
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtJump bodyIntCallJointAggCore
  bodyIntCallFamStmtForSetup bodyIntCallFamStmtForSetupGeneral
  bodyIntCallFamStmtForTransport
  exprSimBopRestWordLoads exprSimBopRestWordLayout whitelistForIterImmLoop
  stmtSimForArrayLoop fragGasMode fragGasPathMem loweringPosts
  context compileEnv venomState venomInst venomExecSemantics
  finite_map list

(* The dynamic array's length word, read from its immutable header. *)
Theorem intcall_imm_length_load:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es st s /\
  immutable_holds ce fp.jc_cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
    (n2w off) es s /\
  evaluate_type (get_tenv fp.jc_cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
  compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca (Lit (n2w off)) st =
    (lvo,st1) /\
  fn_has_code st st1 fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_joint_res fp ce env es st u /\
    eval_operand lvo u =
      SOME (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) /\
    ~u.vs_halted /\ u.vs_current_bb = st1.cs_current_bb /\
    u.vs_inst_idx = LENGTH st1.cs_current_insts /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode (Lit (n2w off)) st =
     (lvo,st1)` by simp[compile_ptr_load_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off : bytes32)` by
    simp[eval_operand_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule_all rest_word_array_immutable_header_path >> strip_tac >>
  drule rest_word_ptr_load_fresh >> strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s` by
    (simp[lookup_var_def] >> rpt strip_tac >> first_x_assum irule >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `intcall_joint_res fp ce env es st (s with vs_vars := u.vs_vars)` by
    (irule intcall_joint_res_vars_frame >> fs[lookup_var_def]) >>
  `u = (s with vs_vars := u.vs_vars) with
         vs_inst_idx := LENGTH st1.cs_current_insts` by
    (qpat_x_assum `u = _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u` >> fs[gas_marked_path_def] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >> simp[] >>
  qpat_x_assum `intcall_joint_res _ _ _ _ _ (s with vs_vars := _)` mp_tac >>
  simp[intcall_joint_res_def] >>
  `s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH st1.cs_current_insts|> =
   (s with vs_vars := u.vs_vars) with vs_inst_idx := LENGTH st1.cs_current_insts` by
    simp[venom_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[bodyIntCallJointAggCoreTheory.intcall_joint_res_inst_idx] >>
  rpt strip_tac
QED

(* From the statement start to the first condition test, at the loop
   invariant with the joint resources kept. *)
Theorem intcall_imm_loop_start:
  (if dyn then
     compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) st = (lvo,st1) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es st s /\
  (dyn ==>
    immutable_holds ce fp.jc_cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv fp.jc_cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\
  fn_has_code st st1 fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_ptrs_reserved ce st /\
  ainst = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  MEM ainst (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  lookup_block st1.cs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      st1.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry fp.jc_func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond] []]|> /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ALL_DISTINCT [p; idx; g; vld] /\
  (!scs. not_local_ptr ce scs p /\ not_local_ptr ce scs idx /\
         not_local_ptr ce scs g /\ not_local_ptr ce scs vld) /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [p; idx; g; vld]) ==>
  ?dst cc.
    gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK cc) /\
    intcall_joint_res fp ce env es st cc /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx
      (Lit (n2w off)) (n2w off) p dst sz ainst cond st 0 es cc /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    (!x z. not_fresh_at st x /\ lookup_var x s = SOME z ==>
           lookup_var x cc = SOME z) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP cc.vs_allocas aid = SOME b) /\
    s.vs_alloca_next <= cc.vs_alloca_next
Proof
  strip_tac >>
  `?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
     intcall_joint_res fp ce env es st u /\
     eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
     ~u.vs_halted /\ u.vs_current_bb = st1.cs_current_bb /\
     u.vs_inst_idx = LENGTH st1.cs_current_insts /\
     (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s) /\
     u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `dyn` >> fs[]
     >- (drule_all intcall_imm_length_load >> strip_tac >>
         qexists_tac `u` >> simp[]) >>
     gvs[comp_return_def] >> qexists_tac `s` >>
     simp[eval_operand_def] >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  `!op. fp.jc_reserved op ==>
     op <> Var p /\ op <> Var idx /\ op <> Var g /\ op <> Var vld` by
    (rpt gen_tac >> strip_tac >>
     `!x. op = Var x ==> not_fresh_at st x` by
       (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
     rpt conj_tac >> strip_tac >> gvs[] >> res_tac >> fs[]) >>
  `!x. not_fresh_at st x ==> x <> p` by (rpt strip_tac >> res_tac >> fs[]) >>
  `?ee w. gas_marked_path F fp.jc_ctx fp.jc_func u 0 (OK ee) /\
     ee.vs_current_bb = entry /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
     intcall_joint_res fp ce env es st ee /\
     lookup_var p ee = SOME w /\ FLOOKUP ee.vs_allocas aid = SOME (w2n w,sz) /\
     ee.vs_memory = u.vs_memory /\ ee.vs_labels = u.vs_labels /\
     u.vs_alloca_next <= ee.vs_alloca_next /\
     (!id ent. FLOOKUP u.vs_allocas id = SOME ent ==>
               FLOOKUP ee.vs_allocas id = SOME ent) /\
     (!x. x <> p ==> lookup_var x ee = lookup_var x u)` by
    (irule intcall_for_alloca_start_no_history >> simp[] >>
     conj_tac >- (strip_tac >> res_tac >> fs[]) >>
     qexists_tac `j` >> gvs[]) >>
  suspend "entry"
QED

Resume intcall_imm_loop_start[entry]:
  `eval_operand lvo ee = SOME (n2w (LENGTH vs))` by
    (Cases_on `lvo` >> gvs[eval_operand_def]) >>
  qabbrev_tac `is = [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
    if dyn then
      [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] []] else []` >>
  qabbrev_tac `e4s = if dyn then
    update_var vld 1w (update_var g 0w (update_var idx 0w ee))
    else update_var idx 0w ee` >>
  `run_inst_seq is ee = OK e4s` by
    (qunabbrev_tac `is` >> qunabbrev_tac `e4s` >>
     irule immutable_entry_block_run >> fs[ALL_DISTINCT] >>
     conj_tac >- (strip_tac >> res_tac >> fs[]) >>
     `LENGTH vs < dimword (:256)` by decide_tac >>
     qexists_tac `LENGTH vs` >> simp[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func ee 0 (OK (jump_to cond e4s))` by
    (irule inst_seq_jump_zero_path >> simp[] >>
     qexists_tac `e5` >>
     gvs[Abbr `is`, is_terminator_def] >> Cases_on `dyn` >>
     simp[is_terminator_def]) >>
  `!w t. intcall_joint_res fp ce env es st t ==>
     intcall_joint_res fp ce env es st (update_var idx w t) /\
     intcall_joint_res fp ce env es st (update_var g w t) /\
     intcall_joint_res fp ce env es st (update_var vld w t)` by
    (rpt strip_tac >> irule intcall_joint_res_update_var >> simp[] >>
     metis_tac[]) >>
  `intcall_joint_res fp ce env es st (jump_to cond e4s)` by
    (simp[intcall_joint_res_jump_to] >> Cases_on `dyn` >> fs[Abbr `e4s`]) >>
  `!x. x <> idx /\ x <> g /\ x <> vld ==>
     lookup_var x (jump_to cond e4s) = lookup_var x ee` by
    (Cases_on `dyn` >> simp[Abbr `e4s`, jump_to_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]) >>
  `(jump_to cond e4s).vs_allocas = ee.vs_allocas /\
   (jump_to cond e4s).vs_alloca_next = ee.vs_alloca_next /\
   (jump_to cond e4s).vs_labels = ee.vs_labels /\
   (jump_to cond e4s).vs_current_bb = cond /\
   (jump_to cond e4s).vs_inst_idx = 0 /\ ~(jump_to cond e4s).vs_halted /\
   lookup_var idx (jump_to cond e4s) = SOME 0w` by
    (fs[ALL_DISTINCT] >> Cases_on `dyn` >>
     simp[Abbr `e4s`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es (jump_to cond e4s) /\
   ret_pc_ok ce st (jump_to cond e4s)` by
    (qpat_assum `intcall_joint_res fp ce env es st (jump_to cond e4s)`
       (strip_assume_tac o REWRITE_RULE [intcall_joint_res_def, intcall_expr_res_def]) >>
     asm_rewrite_tac[]) >>
  `lookup_var p (jump_to cond e4s) = SOME w` by fs[ALL_DISTINCT] >>
  qexistsl_tac [`w`, `jump_to cond e4s`] >> rpt conj_tac
  >- (qpat_assum `gas_marked_path _ _ _ s _ (OK u)`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then drule >> simp[] >> strip_tac >>
      drule_then (drule_then mp_tac) gas_marked_path_then >> simp[])
  >- first_assum ACCEPT_TAC
  >- simp[array_loop_inv_def, eval_operand_def, mk_inst_def]
  >- (Cases_on `lvo` >> gvs[eval_operand_def])
  >- (rpt strip_tac >> res_tac >> fs[])
  >- (rpt strip_tac >> gvs[]) >>
  fs[]
QED
Finalise intcall_imm_loop_start
