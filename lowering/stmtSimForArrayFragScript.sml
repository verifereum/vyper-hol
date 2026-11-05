(* Compiler certification and public boundary for fixed-array loops. *)
Theory stmtSimForArrayFrag
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  stmtSimForArrayLoop stmtSimForArrayParts  stmtLowering compileEnv
  exprLoweringProps fragExec loweringSlice localPtrsProps emitHelperProps
  venomInst venomState venomExecSemantics list rich_list finite_map arithmetic
  stmtSimForParts gasOutcome gasContext stmtSimForRounds vyperInterpreter

Theorem array_declared_reserved[local]:
  declare_local cenv id et st =
    (bc, st with cs_next_var := st.cs_next_var + 1) /\
  local_ptrs_reserved cenv st /\
  st.cs_next_var + 1 <= sa.cs_next_var /\
  sa.cs_next_var <= sb.cs_next_var ==>
  local_ptrs_reserved bc sa /\ local_ptrs_reserved bc sb
Proof
  strip_tac >> drule_all declare_local_reserved >> strip_tac >>
  `local_ptrs_reserved bc sa` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `st with cs_next_var := st.cs_next_var + 1` >> simp[]) >>
  simp[] >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Theorem array_generated_vars[local]:
  sa.cs_next_var = st.cs_next_var + 5 /\
  st.cs_next_var + 5 <= sj.cs_next_var ==>
  ALL_DISTINCT
    [STRING #"%" (toString (st.cs_next_var + 1));
     STRING #"%" (toString (st.cs_next_var + 2));
     STRING #"%" (toString (st.cs_next_var + 3));
     STRING #"%" (toString (st.cs_next_var + 4));
     STRING #"%" (toString sj.cs_next_var);
     STRING #"%" (toString st.cs_next_var)] /\
  not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
  not_fresh_at sa (STRING #"%" (toString (st.cs_next_var + 1))) /\
  not_fresh_at sa (STRING #"%" (toString (st.cs_next_var + 4)))
Proof
  simp[ALL_DISTINCT, not_fresh_at_def] >> rpt strip_tac >> simp[]
QED

Theorem array_register_frame[local]:
  local_ptrs_reserved cenv st /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  sa.cs_next_var = st.cs_next_var + 5 /\
  st.cs_next_var + 5 <= sj.cs_next_var /\
  p = STRING #"%" (toString st.cs_next_var) /\
  idx = STRING #"%" (toString (st.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st.cs_next_var + 2)) /\
  ov = STRING #"%" (toString (st.cs_next_var + 3)) /\
  ep = STRING #"%" (toString (st.cs_next_var + 4)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  ALL_DISTINCT [idx;dv;ov;ep;nv;p] /\
  not_fresh_at sa p /\ not_fresh_at sa idx /\ not_fresh_at sa ep /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv) /\
  (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  (!x. arr_op = Var x ==> ~MEM x [idx;dv;ov;ep;nv])
Proof
  strip_tac >> drule_all array_generated_vars >> strip_tac >>
  `!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  `!x. arr_op = Var x ==> not_fresh_at st x` by
    (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem array_start_alloca_member[local]:
  lookup_block lbl func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions := pre ++ [a;j]|> ==>
  MEM a (fn_insts func)
Proof
  strip_tac >> irule lookup_block_fn_insts >>
  goal_assum (drule_at Any) >>
  simp[]
QED

Theorem compile_for_array_code:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) ==>
  ?bc p idx dv ov ep nv entry cond bod incr exit sa sb0 sb1 sj ainst.
    array_for_code func cenv bc ty stmts id et tv n
      (type_memory_bytes cenv et) arr_op p (type_memory_bytes cenv et)
      ainst idx dv ov ep nv cond exit bod incr
      (st.cs_next_id + 4) (st.cs_next_id + 5)
      (st.cs_next_id + 6) (st.cs_next_id + 7)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    ainst = mk_inst st.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv et))] [p] /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb;
             bb_instructions := st.cs_current_insts ++
               [ainst; mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    cs_extends st sa
Proof
  strip_tac >>
  `!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb` by metis_tac[] >>
  drule_all compile_for_array_parts >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `st.cs_next_var + 5 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc sa sb. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all array_register_frame >> strip_tac >>
  `st.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all array_declared_reserved >> strip_tac >>
  drule array_start_alloca_member >> strip_tac >>
  qexistsl_tac [`bc`, `p`, `idx`, `dv`, `ov`, `ep`, `nv`, `entry`, `cond`,
               `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[array_for_code_def, elem_size_in_location_def, is_slot_addressed_def,
     mk_inst_def] >> gvs[]
QED

(* Allocation changes exactly its output register, whether reused or fresh. *)
Theorem array_alloca_fields[local]:
  ainst.inst_outputs = [p] ==>
  ?s1. exec_alloca ainst s0 (sz : bytes32) = OK s1 /\
    s1.vs_current_bb = s0.vs_current_bb /\
    s1.vs_inst_idx = s0.vs_inst_idx /\ s1.vs_halted = s0.vs_halted /\
    s1.vs_labels = s0.vs_labels /\
    (!x. x <> p ==> lookup_var x s1 = lookup_var x s0)
Proof
  strip_tac >> Cases_on `FLOOKUP s0.vs_allocas ainst.inst_id`
  >- simp[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rename1 `FLOOKUP _ _ = SOME pair` >> PairCases_on `pair` >>
  simp[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem array_allocate_ready[local]:
  stmt_state_rel ctx func cenv cx es s0 /\
  fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
  ainst.inst_opcode = ALLOCA /\
  ainst.inst_operands = [Lit (n2w sz)] /\ ainst.inst_outputs = [p] /\
  not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
  eval_operand saved_base s0 = SOME array_base /\
  (!x. saved_base = Var x ==> x <> p) /\ ret_pc_ok cenv st s0 ==>
  ?s1 dst.
    exec_alloca ainst s0 (n2w sz : bytes32) = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\
    s1.vs_current_bb = s0.vs_current_bb /\
    s1.vs_inst_idx = s0.vs_inst_idx /\ s1.vs_halted = s0.vs_halted /\
    eval_operand saved_base s1 = SOME array_base /\ ret_pc_ok cenv st s1 /\
    lookup_var p s1 = SOME dst /\
    FLOOKUP s1.vs_allocas ainst.inst_id = SOME (w2n dst,sz)
Proof
  strip_tac >> drule array_alloca_fields >>
  disch_then (qspecl_then [`n2w sz : bytes32`, `s0`] strip_assume_tac) >>
  rename1 `exec_alloca ainst s0 (n2w sz : bytes32) = OK s1` >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  rename1 `lookup_var p s1 = SOME dst` >>
  `eval_operand saved_base s1 = SOME array_base` by
    (Cases_on `saved_base` >> fs[eval_operand_def] >> metis_tac[]) >>
  `ret_pc_ok cenv st s1` by
    (fs[ret_pc_ok_def] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >>
     Cases_on `x = p` >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`s1`, `dst`] >> simp[]
QED

Theorem array_entry_zero_inv[local]:
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  lookup_var p s = SOME dst /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  eval_operand saved_base s = SOME array_base /\ ret_pc_ok cenv st s /\
  not_local_ptr cenv es.scopes idx /\ p <> idx /\
  (!x. saved_base = Var x ==> x <> idx) ==>
  array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
    ainst cond st 0 es (jump_to cond (update_var idx 0w s))
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (update_var idx 0w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand saved_base (update_var idx 0w s) = SOME array_base` by
    (Cases_on `saved_base` >>
     fs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `ret_pc_ok cenv st (update_var idx 0w s)` by
    (fs[ret_pc_ok_def] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >>
     Cases_on `x = idx` >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to,
       jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       eval_operand_def] >>
  Cases_on `saved_base` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem array_declared_ptr_unique[local]:
  local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) ==>
  !name z. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var p) z) \/ name = id
Proof
  simp[local_ptrs_reserved_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem array_allocation_safe[local]:
  local_ptrs_reserved bc sa /\
  bc.ce_imm_alloca = cenv.ce_imm_alloca /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
  lookup_scopes id scopes = NONE /\ name <> id /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar saved_base arr_sz) ==>
  not_local_ptr cenv scopes p /\ (!x. saved_base = Var x ==> x <> p)
Proof
  strip_tac >> drule_all array_declared_ptr_unique >> strip_tac >>
  `cenv.ce_imm_alloca <> SOME (Var p)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[not_local_ptr_def] >> rpt strip_tac >>
      `name' <> id` by (strip_tac >> gvs[]) >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem array_prefix_continuation[local]:
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit 0w] [idx]; mk_inst i2 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  ainst.inst_opcode = ALLOCA /\ step_inst_base ainst s0 = OK s1 /\
  s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted ==>
  !fuel rr.
    run_from fuel ctx func
      (jump_to cond (update_var idx 0w (jump_to entry s1))) = rr /\
    (!e. rr <> Error e) ==>
    ?fuel'. run_from fuel' ctx func s0 = rr
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?f1. run_from f1 ctx func (jump_to entry s1) = rr` by
    (irule for_array_entry_block >>
     goal_assum (drule_at Any) >> simp[jump_to_def] >>
     qexistsl_tac [`cond`, `fuel`, `i1`, `i2`, `idx`] >> simp[] >>
     fs[jump_to_def, update_var_def]) >>
  irule for_start_block >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem array_code_initialization_fields[local]:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
  (!scs. not_local_ptr cenv scs idx) /\ p <> idx /\
  (!x. saved_base = Var x ==> x <> idx)
Proof
  simp[array_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem array_alloca_frame[local]:
  exec_alloca ainst s0 (sz : bytes32) = OK s1 /\
  ainst.inst_outputs = [p] ==>
  (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s1.vs_allocas aid = SOME b)
Proof
  strip_tac >> Cases_on `FLOOKUP s0.vs_allocas ainst.inst_id`
  >- (gvs[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `aid = ainst.inst_id` >> gvs[]) >>
  rename1 `FLOOKUP _ _ = SOME pair` >> PairCases_on `pair` >>
  gvs[exec_alloca_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem array_loop_initialize:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\ name <> id /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar saved_base arr_sz) /\
  eval_operand saved_base s0 = SOME array_base /\ ret_pc_ok cenv st s0 ==>
  ?dst s.
    array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es s /\
    (!fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func s0 = rr)
Proof
  strip_tac >>
  `bc.ce_imm_alloca = cenv.ce_imm_alloca` by
    fs[array_for_code_def, compile_env_component_equality] >>
  dxrule array_code_initialization_fields >> strip_tac >>
  drule_all array_allocation_safe >> strip_tac >>
  drule_all array_allocate_ready >> strip_tac >>
  rename1 `exec_alloca ainst s0 (n2w sz : bytes32) = OK s1` >>
  rename1 `lookup_var p s1 = SOME dst` >>
  qexistsl_tac [`dst`, `jump_to cond (update_var idx 0w (jump_to entry s1))`] >>
  conj_tac
  >- (irule array_entry_zero_inv >>
      simp[stmt_state_rel_jump_to, ret_pc_ok_jump_to, jump_to_def] >>
      fs[lookup_var_def] >> metis_tac[]) >>
  `step_inst_base ainst s0 = OK s1` by
    simp[step_inst_base_def, eval_operand_def] >>
  drule array_prefix_continuation >> simp[] >> metis_tac[]
QED

Theorem array_loop_initialize_framed:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\ name <> id /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar saved_base arr_sz) /\
  eval_operand saved_base s0 = SOME array_base /\ ret_pc_ok cenv st s0 /\
  (!x. not_fresh_at caller x ==> x <> p /\ x <> idx) ==>
  ?dst s.
    array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es s /\ array_run_frame ctx func caller s0 s
Proof
  strip_tac >>
  `bc.ce_imm_alloca = cenv.ce_imm_alloca` by
    fs[array_for_code_def, compile_env_component_equality] >>
  dxrule array_code_initialization_fields >> strip_tac >>
  drule_all array_allocation_safe >> strip_tac >>
  drule_all array_allocate_ready >> strip_tac >>
  rename1 `exec_alloca ainst s0 (n2w sz : bytes32) = OK s1` >>
  rename1 `lookup_var p s1 = SOME dst` >>
  drule_all array_alloca_frame >> strip_tac >>
  qexistsl_tac [`dst`, `jump_to cond (update_var idx 0w (jump_to entry s1))`] >>
  conj_tac
  >- (irule array_entry_zero_inv >>
      simp[stmt_state_rel_jump_to, ret_pc_ok_jump_to, jump_to_def] >>
      fs[lookup_var_def] >> metis_tac[]) >>
  simp[array_run_frame_def] >> rpt conj_tac
  >- (simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> metis_tac[lookup_var_def])
  >- simp[jump_to_def, update_var_def] >>
  `step_inst_base ainst s0 = OK s1` by
    simp[step_inst_base_def, eval_operand_def] >>
  drule array_prefix_continuation >> simp[] >> metis_tac[]
QED

Theorem array_caller_freshness[local]:
  sa.cs_next_var = st.cs_next_var + 5 /\
  sa.cs_next_var <= sb0.cs_next_var /\
  sa.cs_next_var <= sj.cs_next_var /\
  p = STRING #"%" (toString st.cs_next_var) /\
  idx = STRING #"%" (toString (st.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st.cs_next_var + 2)) /\
  ov = STRING #"%" (toString (st.cs_next_var + 3)) /\
  ep = STRING #"%" (toString (st.cs_next_var + 4)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  st.cs_next_var <= sa.cs_next_var
Proof
  simp[not_fresh_at_def] >> rpt strip_tac >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_for_array_code_ready_framed:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) ==>
  ?bc p idx dv ov ep nv entry cond bod incr exit sa sb0 sb1 sj ainst.
    array_for_code func cenv bc ty stmts id et tv n
      (type_memory_bytes cenv et) arr_op p (type_memory_bytes cenv et)
      ainst idx dv ov ep nv cond exit bod incr
      (st.cs_next_id + 4) (st.cs_next_id + 5)
      (st.cs_next_id + 6) (st.cs_next_id + 7)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    ainst = mk_inst st.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv et))] [p] /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb;
             bb_instructions := st.cs_current_insts ++
               [ainst; mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\ cs_extends st sa /\
    (?sd. declare_local cenv id et st = (bc,sd)) /\
    (!x. not_fresh_at st x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
    (!x. not_fresh_at st x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. arr_op = Var x ==> not_fresh_at sb0 x) /\
    st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
    (!x. not_fresh_at st x ==> x <> p /\ x <> idx)
Proof
  strip_tac >>
  `!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb` by metis_tac[] >>
  drule_all compile_for_array_parts >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `st.cs_next_var + 5 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc sa sb. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all array_register_frame >> strip_tac >>
  `st.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all array_declared_reserved >> strip_tac >>
  drule array_start_alloca_member >> strip_tac >>
  `sa.cs_next_var <= sj.cs_next_var` by simp[] >>
  `(!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
   (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
   not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
   st.cs_next_var <= sa.cs_next_var` by
    (irule array_caller_freshness >> simp[] >> qexists_tac `sj` >> simp[]) >>
  `!x. arr_op = Var x ==> not_fresh_at sb0 x` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. not_fresh_at st x ==> x <> p /\ x <> idx` by
    simp[not_fresh_at_def] >>
  qexistsl_tac [`bc`, `p`, `idx`, `dv`, `ov`, `ep`, `nv`, `entry`, `cond`,
               `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[array_for_code_def, elem_size_in_location_def, is_slot_addressed_def,
     mk_inst_def] >> gvs[] >> metis_tac[]
QED

Theorem compile_for_array_code_ready:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) ==>
  ?bc p idx dv ov ep nv entry cond bod incr exit sa sb0 sb1 sj ainst.
    array_for_code func cenv bc ty stmts id et tv n
      (type_memory_bytes cenv et) arr_op p (type_memory_bytes cenv et)
      ainst idx dv ov ep nv cond exit bod incr
      (st.cs_next_id + 4) (st.cs_next_id + 5)
      (st.cs_next_id + 6) (st.cs_next_id + 7)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    ainst = mk_inst st.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv et))] [p] /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb;
             bb_instructions := st.cs_current_insts ++
               [ainst; mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\ cs_extends st sa /\
    (?sd. declare_local cenv id et st = (bc,sd)) /\
    (!x. not_fresh_at st x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
    (!x. not_fresh_at st x ==>
      not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. arr_op = Var x ==> not_fresh_at sb0 x) /\
    st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var
Proof
  strip_tac >> drule_all compile_for_array_code_ready_framed >> strip_tac >>
  qexistsl_tac [`bc`, `p`, `idx`, `dv`, `ov`, `ep`, `nv`, `entry`, `cond`,
               `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`] >> gvs[]
QED

Theorem array_code_final_landing:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\
  (!x. not_fresh_at st x ==> x <> dv) ==>
  !es cc. array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
    ainst cond st (LENGTH vs) es cc ==>
  ?next. array_loop_landing ctx func cenv cx st exit es cc next
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv es.scopes dv` by simp[] >>
  drule_all array_condition_exit_framed >> strip_tac >>
  rename1 `next.vs_current_bb = exit` >>
  qexists_tac `next` >> simp[array_loop_landing_def, array_run_frame_def] >>
  metis_tac[]
QED

Theorem array_code_return_pc[local]:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  bc.ce_return_pc = cenv.ce_return_pc
Proof
  simp[array_for_code_def] >> strip_tac >>
  qpat_x_assum `bc with <| ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _ |> = cenv`
    (mp_tac o Q.AP_TERM `\c. c.ce_return_pc`) >> simp[]
QED

Theorem array_return_pc_transport[local]:
  bc.ce_return_pc = cenv.ce_return_pc /\ ret_pc_ok cenv st s0 /\
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) ==>
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!s. ret_pc_ok cenv st s ==> ret_pc_ok bc sb0 s)
Proof
  simp[ret_pc_ok_def] >> metis_tac[]
QED

Theorem array_code_body_prefix[local]:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\ cs_extends sb0 sb1 ==>
  ?bb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions
Proof
  strip_tac >> drule array_for_code_stmts >> strip_tac >>
  drule_all fn_has_code_start >> simp[]
QED

Theorem array_unbound_body_ptr[local]:
  local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id scopes = NONE ==>
  not_local_ptr bc (FEMPTY :: scopes) p
Proof
  rpt strip_tac >>
  `not_local_ptr bc scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  fs[not_local_ptr_def, vyperStateTheory.lookup_scopes_def]
QED

Theorem array_invariant_layout[local]:
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?addr. eval_operand saved_base s = SOME addr /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n addr + k * stride) s.vs_memory /\
        w2n addr + k * stride < dimword (:256))) /\
  (!s. ret_pc_ok cenv st s ==> ret_pc_ok bc sb0 s) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
    ainst lbl st k es s /\ k < LENGTH vs ==>
  val_in_memory tv (EL k vs) (w2n array_base + k * stride) s.vs_memory /\
  w2n array_base + k * stride < dimword (:256) /\ ret_pc_ok bc sb0 s
Proof
  simp[array_loop_inv_def] >> rpt strip_tac >>
  qpat_x_assum `!ei s. _` (qspecl_then [`es`, `s`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem array_code_step_contract:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit bod incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  cs_extends sb0 sb1 /\ LENGTH vs < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\ ret_pc_ok cenv st s0 /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?addr. eval_operand saved_base s = SOME addr /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n addr + k * stride) s.vs_memory /\
        w2n addr + k * stride < dimword (:256))) /\
  (!ei k r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes) = (r,es2) ==>
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) /\
  (!ei k r es2 sc rest.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes) = (r,es2) /\ es2.scopes = sc :: rest ==>
    stmt_res_ok (InLoop exit incr) r /\
    ((r = INL () \/ r = INR ContinueException) ==>
      P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  array_step_contract ctx func cenv cx P vs id idx saved_base array_base p dst sz
    ainst cond exit st tv stmts RetQ st
Proof
  strip_tac >> drule array_code_return_pc >> strip_tac >>
  drule_all array_return_pc_transport >> strip_tac >>
  drule_all array_code_body_prefix >> strip_tac >>
  rename1 `lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb` >>
  drule array_code_initialization_fields >> strip_tac >>
  simp[Once array_step_contract_def] >> rpt gen_tac >> strip_tac >>
  `P es /\ lookup_scopes id es.scopes = NONE` by fs[array_loop_inv_def] >>
  qpat_x_assum `!ei k r es2 sc rest. _` drule_all >> strip_tac >>
  qpat_x_assum `!ei k r es2. _` drule_all >> strip_tac >>
  `value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)` by simp[] >>
  `not_local_ptr bc (FEMPTY :: es.scopes) p` by
    (drule_all array_unbound_body_ptr >> simp[]) >>
  `val_in_memory tv (EL k vs) (w2n array_base + k * stride) cc.vs_memory /\
   w2n array_base + k * stride < dimword (:256) /\ ret_pc_ok bc sb0 cc` by
    (drule_all array_invariant_layout >> simp[]) >>
  `!s. array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst bod st k es s ==>
      val_in_memory tv (EL k vs) (w2n array_base + k * stride) s.vs_memory /\
      ret_pc_ok bc sb0 s` by
    (rpt strip_tac >> drule_all array_invariant_layout >> simp[]) >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (drule_all array_for_code_scope_frame >> simp[]) >>
  `cenv_top_ext cenv bc ((es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: es.scopes).scopes)` by
    (fs[cenv_top_ext_def, vyperStateTheory.lookup_scopes_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `stmt_frag _ _ _ _ _ _ _ ei _ _` >>
  `ei = es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes`
    by simp[Abbr `ei`] >>
  drule_all array_for_step_framed_open >>
  simp[array_run_frame_def, array_loop_landing_def]
QED

Theorem array_public_body_callback[local]:
  declare_local cenv id et st0 = (bc,sd) /\
  (!st0 bc sd ex inc ei k r es2.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes) = (r,es2) ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) ==>
  !exit incr ei k r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes) = (r,es2) ==>
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts)
      (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)
Proof
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem array_public_scope_callback[local]:
  (!ei k r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  !exit incr ei k r es2 sc rest.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes) = (r,es2) /\ es2.scopes = sc :: rest ==>
    stmt_res_ok (InLoop exit incr) r /\
    ((r = INL () \/ r = INR ContinueException) ==>
      P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)
Proof
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem array_public_loop_finish[local]:
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond sa 0 es cc /\
  array_run_frame ctx func sa s0 cc /\
  eval_for cx tv id stmts vs es = (res,es') /\ stmt_res_ok lctx res /\
  array_step_contract ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond exit sa tv stmts RetQ sa /\
  (!ei s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond sa (LENGTH vs) ei s ==>
     ?next. array_loop_landing ctx func cenv cx sa exit ei s next) /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] ==>
  (?s cenv'. stmt_lands lctx sb res s /\ ~s.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
    cenv_top_ext cenv cenv' es'.scopes /\ stmt_state_rel ctx func cenv' cx es' s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!fuel. (!e. run_from fuel ctx func s <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s0 = run_from fuel ctx func s)) \/
  (?fuel. exit_result (run_from fuel ctx func s0) /\
    stmt_exit RetQ es' res (run_from fuel ctx func s0))
Proof
  strip_tac >>
  `eval_for cx tv id stmts (DROP 0 vs) es = (res,es')` by simp[] >>
  `(res = INL () /\ ?next. array_loop_landing ctx func cenv cx sa exit es' cc next) \/
   (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
      stmt_exit RetQ es' res rr)` by
    (drule_at Any array_for_loop >> disch_then irule >> simp[] >>
     conj_tac >- (qexists_tac `lctx` >> simp[]) >>
     goal_assum (drule_at Any) >> simp[])
  >- (drule_all array_loop_landing_pullback >> strip_tac >>
      rename1 `array_loop_landing _ _ _ _ _ _ _ _ landing` >>
      disj1_tac >> qexistsl_tac [`landing`, `cenv`] >>
      fs[array_loop_landing_def, stmt_lands_def, block_is_terminated_def,
         cenv_top_ext_refl, array_run_frame_def] >> metis_tac[]) >>
  disj2_tac >> fs[array_run_frame_def] >> metis_tac[exit_result_not_error]
QED

Theorem compile_for_array_frag:
  !ctx func cx cenv lctx RetQ ty id et n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
          (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs = n /\
  n < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  name <> id /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  P es /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?base. eval_operand (Var arr_ptr) s = SOME base /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n base + k * type_memory_size tv) s.vs_memory /\
        w2n base + k * type_memory_size tv < dimword (:256))) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) /\
  (!ei k gs r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes; gas_obs := gs |>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts))
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = (uu,sb)` >>
  `uu = ()` by simp[oneTheory.one] >> gvs[] >>
  `type_memory_bytes cenv et + 64 < dimword (:256)` by simp[] >>
  drule_all compile_for_array_code_ready_framed >> strip_tac >>
  qpat_assum `!ei s. _` drule_all >> strip_tac >>
  rename1 `eval_operand (Var arr_ptr) s0 = SOME arr_base` >>
  `ainst.inst_operands = [Lit (n2w (type_memory_bytes cenv et))]` by simp[mk_inst_def] >>
  `type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  `lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
      [ainst; mk_inst (sa.cs_next_id + 1) JMP [Label entry] []]|>` by simp[] >>
  `?dst cc. array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr)
      arr_base p dst (type_memory_bytes cenv et) ainst cond sa 0 es cc /\
      array_run_frame ctx func sa s0 cc` by
    (irule array_loop_initialize_framed >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  rename1 `array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) arr_base p dst
    (type_memory_bytes cenv et) ainst cond sa 0 es cc` >>
  `cs_extends sb0 sb1` by
    (drule array_for_code_stmts >> strip_tac >>
     qpat_x_assum `!c lc sa sb. compile_stmts _ _ _ _ _ = _ ==> _` drule >> simp[]) >>
  drule array_public_body_callback >>
  disch_then drule >>
  disch_then (qspecl_then [`exit`, `incr`] assume_tac) >>
  drule array_public_scope_callback >>
  disch_then (qspecl_then [`exit`, `incr`] assume_tac) >>
  `!l. Var arr_ptr <> Label l` by simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv`
    by metis_tac[] >>
  `!x. Var arr_ptr = Var x ==> not_fresh_at sb0 x` by simp[] >>
  `array_step_contract ctx func cenv cx P vs id idx (Var arr_ptr) arr_base p dst
     (type_memory_bytes cenv et) ainst cond exit sa tv stmts RetQ sa` by
    (drule array_code_step_contract >> disch_then irule >>
     simp[] >> conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
     qexists_tac `s0` >> simp[]) >>
  `!ei s. array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) arr_base p dst
      (type_memory_bytes cenv et) ainst cond sa (LENGTH vs) ei s ==>
      ?next. array_loop_landing ctx func cenv cx sa exit ei s next` by
    (rpt strip_tac >> drule array_code_final_landing >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  drule array_public_loop_finish >> disch_then irule >> simp[] >>
  qexistsl_tac [`stmts`, `tv`] >> gvs[]
QED
