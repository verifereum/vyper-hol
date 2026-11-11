(* Compiler certification and public boundary for fixed-array loops. *)
Theory stmtSimForArrayFrag
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  stmtSimForArrayLoop stmtSimForArrayParts  stmtLowering compileEnv loweringStateRelDefs
  exprLoweringProps fragExec loweringSlice localPtrsProps emitHelperProps
  venomInst venomState venomExecSemantics list rich_list finite_map arithmetic
  stmtSimForParts gasOutcome gasContext stmtSimForRounds vyperInterpreter
  fragGasPath fragGasMode gasSummaryCompose gasSummary gasExemptCert vyperState vyperValue stmtSimDeclGas

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
  gas_marked_path F ctx func s0 0
    (OK (jump_to cond (update_var idx 0w (jump_to entry s1))))
Proof
  strip_tac >>
  `gas_marked_path F ctx func s0 0 (OK (jump_to entry s1))` by
    (irule inst_seq_jump_zero_path >>
     simp[] >>
     qexistsl_tac [`[ainst]`, `j`] >>
     simp[DROP_LENGTH_APPEND, run_inst_seq_def, is_terminator_def]) >>
  `gas_marked_path F ctx func (jump_to entry s1) 0
     (OK (jump_to cond (update_var idx 0w (jump_to entry s1))))` by
    (irule inst_seq_jump_zero_path >>
     simp[jump_to_def] >>
     qexists_tac `i2` >>
     simp[jump_to_def, mk_inst_def, is_terminator_def,
          run_inst_seq_def, step_inst_base_def, eval_operand_def]) >>
  drule_all gas_marked_path_then >> simp[]
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
    gas_marked_path F ctx func s0 0 (OK s)
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
      ainst cond st 0 es s /\ array_caller_frame caller s0 s /\
    gas_marked_path F ctx func s0 0 (OK s)
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
  conj_tac
  >- (simp[array_caller_frame_def, jump_to_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> metis_tac[lookup_var_def]) >>
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

(* A gas-free successful results prefix retains syntactic certificate binds. *)
Theorem array_values_prefix_outcome[local]:
  (!gs. source (es with gas_obs := gs) = (INL (vs:eval_result list), es with gas_obs := gs)) /\
  ~s.vs_halted /\
  gas_outcome F tops (ctx,func) (next vs) (es with gas_obs := [],s) Q R ==>
  gas_outcome F tops (ctx,func) (bind source next) (es,s) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) source (es,s) [] (INL vs) es (OK s)` by
    (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
     irule (cj 1 gas_path_rules) >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      (conj_tac
       >- (drule_all gas_marked_exec_bind_normal >> simp[]) >>
       simp[])) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ignore_bind_def] >> strip_tac >>
  drule gas_exempt_cert_bind_results >>
  disch_then (qspecl_then [`tops`, `\v. bind (next v) (\x. return ())`] mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem array_for_source_prefix:
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
     (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs = n /\ evaluate_type (get_tenv cx) et = SOME tv /\
  ~s.vs_halted /\
  gas_outcome F tops (ctx,func) (eval_for cx tv id stmts vs)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome F tops (ctx,func)
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts))
    (es,s) Q R
Proof
  strip_tac >>
  `!msg. assert T msg = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def,
       bind_return] >>
  irule array_values_prefix_outcome >> simp[] >>
  simp[compatible_bound_def, check_def, vyperStateTheory.assert_def,
    ignore_bind_def, bind_return]
QED

Theorem array_outcome_start_gas_obs[local]:
  gas_outcome F tops (ctx,func) source (es,s) Q R ==>
  gas_outcome F tops (ctx,func) source (es with gas_obs := gs,s) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def, gas_marked_exec_def] >>
      metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  drule gas_exempt_cert_start_gas_obs >> simp[]
QED

Theorem array_stmt_frag_start_gas_obs[local]:
  stmt_frag ctx func cx lctx RetQ cenv m source es ==>
  stmt_frag ctx func cx lctx RetQ cenv m source (es with gas_obs := gs)
Proof
  simp[stmt_frag_def, stmt_framed_frag_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s0` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  first_x_assum drule_all >>
  disch_then (mp_then Any mp_tac array_outcome_start_gas_obs) >> simp[]
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


Theorem array_code_loop_counted[local]:
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
  (!k. k < LENGTH vs ==> w2n arr_base + k * stride < dimword (:256)) /\
  (!ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond st 0 es cc /\ array_caller_frame st s0 cc /\
  gas_admissible (eval_for cx tv id stmts (MAP Value vs)) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_for cx tv id stmts (MAP Value vs)) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      array_caller_frame st s0 t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >> drule array_code_return_pc >> strip_tac >>
  drule_all array_return_pc_transport >> strip_tac >>
  drule_all array_code_body_prefix >> strip_tac >>
  drule array_code_initialization_fields >> strip_tac >>
  `!j ei s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst bod st j ei s /\ j < LENGTH vs ==>
      val_in_memory tv (EL j vs) (w2n arr_base + j * stride) s.vs_memory /\
      ret_pc_ok bc sb0 s` by
    (rpt strip_tac >> drule_all array_invariant_layout >> simp[]) >>
  `!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    w2n arr_base + j * stride < dimword (:256) /\
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit incr) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))` by
    suspend "callback" >>
  drule_all (SRULE [DROP_0] (Q.INST [`k` |-> `0`] array_for_loop_counted)) >> simp[]
QED

Resume array_code_loop_counted[callback]:
  rpt strip_tac
  >- metis_tac[]
  >- (irule array_unbound_body_ptr >> metis_tac[])
  >- (qpat_assum `!ei k. _` drule_all >>
      disch_then (mp_then Any mp_tac array_stmt_frag_start_gas_obs) >> simp[]) >>
  qpat_assum `!ei k gs r es2. _` drule_all >> simp[]
QED
Finalise array_code_loop_counted

Theorem array_outcome_stmt_post[local]:
  st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
  gas_outcome F tops (ctx,func) source (es,s0)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      array_caller_frame st s0 t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r) ==>
  gas_outcome F tops (ctx,func) source (es,s0)
    (stmt_post ctx func cx lctx cenv cenv st st' s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> qhdtm_x_assum `gas_outcome` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qhdtm_x_assum `gas_summary_at` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      gvs[] >> rpt strip_tac >>
      simp[stmt_post_def, stmt_lands_def, block_is_terminated_def,
           cenv_top_ext_refl, array_caller_frame_def] >>
      fs[array_caller_frame_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >> simp[]
QED

Theorem array_public_entry_ready[local]:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\ name <> id /\
  ret_pc_ok cenv st s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = st.cs_current_bb /\
  s0.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!ei t. P ei /\ stmt_state_rel ctx func cenv cx ei t ==>
    ?addr. eval_operand (Var arr_ptr) t = SOME addr /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n addr + k * type_memory_size tv) t.vs_memory /\
        w2n addr + k * type_memory_size tv < dimword (:256))) ==>
  ?bc p idx dv ov ep nv cond bod incr exit sa sb0 sb1 sj ainst sd base dst cc.
    array_for_code func cenv bc ty stmts id et tv (LENGTH vs)
      (type_memory_bytes cenv et) (Var arr_ptr) p (type_memory_bytes cenv et)
      ainst idx dv ov ep nv cond exit bod incr
      (st.cs_next_id + 4) (st.cs_next_id + 5)
      (st.cs_next_id + 6) (st.cs_next_id + 7)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    declare_local cenv id et st = (bc,sd) /\
    (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
    (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. Var arr_ptr = Var x ==> not_fresh_at sb0 x) /\
    (!k. k < LENGTH vs ==> w2n base + k * type_memory_bytes cenv et < dimword (:256)) /\
    array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) base p dst
      (type_memory_bytes cenv et) ainst cond st 0 es cc /\
    array_caller_frame st s0 cc /\ gas_marked_path F ctx func s0 0 (OK cc)
Proof
  strip_tac >> drule_all compile_for_array_code_ready_framed >> strip_tac >>
  qpat_assum `!ei t. _` drule_all >> strip_tac >>
  `type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  `ainst.inst_operands = [Lit (n2w (type_memory_bytes cenv et))]` by simp[mk_inst_def] >>
  `?dst cc. array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) addr p dst
      (type_memory_bytes cenv et) ainst cond st 0 es cc /\
      array_caller_frame st s0 cc /\ gas_marked_path F ctx func s0 0 (OK cc)` by
    (irule array_loop_initialize_framed >>
     qhdtm_assum `array_for_code` (irule_at Any) >>
     simp[] >>
     qpat_assum `lookup_block entry _ = _` (irule_at Any) >> simp[] >>
     qexistsl_tac [`name`, `st.cs_next_id + 1`, `arr_sz`] >> simp[]) >>
  qexistsl_tac [`bc`, `p`, `idx`, `dv`, `ov`, `ep`, `nv`, `cond`, `bod`, `incr`,
    `exit`, `sa`, `sb0`, `sb1`, `sj`, `ainst`, `sd`, `addr`, `dst`, `cc`] >>
  simp[]
QED

Theorem compile_for_array_frag_zero[local]:
  !ctx func cx cenv lctx RetQ ty id et n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
          (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
  LENGTH vs = n /\
  n < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  name <> id /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  P (es with gas_obs := []) /\
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
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv et + 64 < dimword (:256)` by simp[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `lookup_scopes id (es with gas_obs := []).scopes = NONE` by simp[] >>
  drule_all array_public_entry_ready >> strip_tac >>
  `gas_admissible (eval_for cx tv id stmts (MAP Value vs)) (stmt_res_ok lctx)
     (es with gas_obs := [])` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, Once evaluate_def, lift_option_type_def,
       lift_option_def, bind_return, bind_def, compatible_bound_def,
       check_def, vyperStateTheory.assert_def, ignore_bind_def, return_def]) >>
  drule array_for_code_stmts >> strip_tac >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  `!ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)` by
    (rpt strip_tac >> qpat_assum `!st0 bc sd ex inc ei k. _` drule_all >> simp[]) >>
  `!l. Var arr_ptr <> Label l` by simp[] >>
  `!ei t. P ei /\ stmt_state_rel ctx func cenv cx ei t ==>
    ?addr. eval_operand (Var arr_ptr) t = SOME addr /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n addr + k * type_memory_bytes cenv et) t.vs_memory /\
        w2n addr + k * type_memory_bytes cenv et < dimword (:256))` by
    (rpt strip_tac >> qpat_assum `!ei s. _` drule_all >> simp[]) >>
  drule_all array_code_loop_counted >> strip_tac >>
  drule_all stmtSimDeclComposeTheory.gas_outcome_zero_prefix >> strip_tac >>
  drule_all (SRULE [] (INST [``n:num`` |-> ``LENGTH (vs0:value list)``,
                              ``vs:eval_result list`` |-> ``MAP Value (vs0:value list)``]
                          array_for_source_prefix)) >> strip_tac >>
  irule array_outcome_stmt_post >> simp[] >> goal_assum (drule_at Any)
QED


Theorem gas_outcome_start_gas_obs[local]:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R ==>
  gas_outcome memory tops (ctx,func) source (es with gas_obs := gs,s0) Q R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >> fs[gas_summary_at_def, gas_marked_exec_def] >>
      metis_tac[]) >>
  disj2_tac >> drule gas_exempt_cert_start_gas_obs >> simp[] >>
  metis_tac[]
QED

Theorem stmt_frag_start_gas_obs[local]:
  stmt_frag ctx func cx lctx RetQ cenv m source es ==>
  !gs. stmt_frag ctx func cx lctx RetQ cenv m source (es with gas_obs := gs)
Proof
  rw[stmt_frag_def, stmt_framed_frag_def] >>
  irule gas_outcome_start_gas_obs >> first_x_assum irule >> simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem compile_for_array_frag:
  !ctx func cx cenv lctx RetQ ty id et n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
          (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
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
  rpt gen_tac >> strip_tac >>
  irule (Q.SPEC `\ei. ?gs. P (ei with gas_obs := gs)`
           (Q.GEN `P` (SPEC_ALL compile_for_array_frag_zero))) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`P`, `vs`] >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> rename1 `P (ei with gas_obs := g0)` >>
      first_x_assum (qspecl_then [`st0`, `bc`, `sd`, `ex`, `inc`,
        `ei with gas_obs := g0`, `k`] mp_tac) >> simp[] >>
      disch_then (qspec_then `ei.gas_obs` mp_tac o
        MATCH_MP stmt_frag_start_gas_obs) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rename1 `P (ei with gas_obs := g0)` >>
      first_x_assum (qspecl_then [`ei with gas_obs := g0`, `k`, `gs`, `r`, `es2`]
        mp_tac) >> simp[] >> strip_tac >> simp[] >>
      strip_tac >> gvs[] >> qexists `es2.gas_obs` >> simp[])
  >- (rpt strip_tac >> rename1 `P (ei with gas_obs := g0)` >>
      first_x_assum (qspecl_then [`ei with gas_obs := g0`, `s`] mp_tac) >>
      simp[] >> disch_then irule >>
      qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
      simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
      strip_tac >> asm_rewrite_tac[])
  >> qexists `es.gas_obs` >> simp[]
QED
