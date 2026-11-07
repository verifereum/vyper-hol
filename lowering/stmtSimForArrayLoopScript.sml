(* Proof interfaces for the fixed-array loop; no executable compiler here. *)
Theory stmtSimForArrayLoop
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  stmtSimForArrayParts stmtSimForArray  stmtLowering compileEnv
  fragExec loweringSlice localPtrsProps exprLoweringProps emitHelper
  venomInst venomState venomExecSemantics vyperState valueEncoding
  list rich_list finite_map words integer_word venomExecProofs emitHelperProps
  vyperEvalPreservesScopes stmtSimForParts vyperInterpreter
  fragGasSeq fragGasMode fragGasPath gasCount context gasSummary gasExemptCert
  gasContext gasOutcome gasSummaryCompose stmtSimForRounds

(* An address temporary written into an unchanged state keeps the frame. *)
val alloca_frame_update_var_same =
  Q.INST [`c0` |-> `c`, `es` |-> `ee`, `t` |-> `s0`]
    stmtSimDefsTheory.alloca_frame_update_var
  |> SIMP_RULE std_ss [stmtSimDefsTheory.alloca_frame_same];

Definition array_for_code_def:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj <=>
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
    lookup_block incr_lbl func.fn_blocks =
      SOME <| bb_label := incr_lbl;
              bb_instructions :=
                [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
                 mk_inst i2 ASSIGN [Var nv] [idx];
                 mk_inst i3 JMP [Label cond_lbl] []] |> /\
    sa.cs_current_bb = stmts_lbl /\
    sa.cs_current_insts =
      [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
       mk_inst j4 ADD [saved_base; Var ov] [ep]] /\
    compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa =
      ((),sb0) /\
    sb0.cs_current_bb = stmts_lbl /\
    sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
    same_blocks sa sb0 /\ fn_has_code sa sb0 func /\
    compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
    fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sa /\
    local_ptrs_reserved bc sb0 /\
    ~block_is_terminated sb0 /\
    (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts = sb1.cs_current_insts ++
         [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\
    fn_inst_ids_distinct func /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
           not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
           not_local_ptr cenv scs nv) /\
    ALL_DISTINCT [idx; dv; ov; ep; nv; p] /\
    (!x. saved_base = Var x ==> ~MEM x [idx; dv; ov; ep; nv]) /\
    not_fresh_at sa idx /\ not_fresh_at sa p /\ not_fresh_at sa ep /\
    (!x. saved_base = Var x ==> not_fresh_at sa x) /\
    stride = type_memory_bytes cenv et /\ stride = type_memory_size tv /\
    stride <= sz /\ stride + 64 < dimword (:256)
End

Definition array_loop_inv_def:
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st k es s <=>
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx es s /\ P es /\
    lookup_scopes id es.scopes = NONE /\ k <= LENGTH vs /\
    lookup_var idx s = SOME (n2w k) /\
    eval_operand saved_base s = SOME base /\
    lookup_var p s = SOME dst /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    ret_pc_ok cenv st s
End

Theorem array_copy_prefix_alignment:
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 ==>
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  LENGTH sb0.cs_current_insts = 2 + LENGTH (emitted_insts sa sb0)
Proof
  simp[]
QED

Theorem array_for_code_condition:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |>
Proof
  simp[array_for_code_def]
QED

Theorem array_for_code_increment:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
            bb_instructions :=
              [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
               mk_inst i2 ASSIGN [Var nv] [idx];
               mk_inst i3 JMP [Label cond_lbl] []] |>
Proof
  simp[array_for_code_def]
QED

Theorem array_for_code_prefix:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa =
    ((),sb0) /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  LENGTH sb0.cs_current_insts = 2 + LENGTH (emitted_insts sa sb0) /\
  sb0.cs_current_bb = stmts_lbl
Proof
  strip_tac >> fs[array_for_code_def]
QED

Theorem array_for_code_stmts:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((),sb1) /\
  fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
  ~block_is_terminated sb0
Proof
  simp[array_for_code_def]
QED

Theorem array_for_code_scope_frame:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id scopes = NONE ==>
  cenv_top_ext cenv bc (FEMPTY :: scopes)
Proof
  simp[array_for_code_def, cenv_top_ext_def] >> rpt strip_tac >>
  rename1 `FLOOKUP bc.ce_vars name <> FLOOKUP cenv.ce_vars name` >>
  `name = id` by
    (spose_not_then assume_tac >>
     qpat_x_assum `!name. name <> id ==> _`
       (qspec_then `name` mp_tac) >> simp[]) >>
  gvs[lookup_scopes_def] >> metis_tac[]
QED

(* The prefix length is derived from the actual two emit_op calls and the
   copy append interface, rather than fixed to the range loop's MSTORE. *)
Theorem array_emitted_prefix_alignment:
  s0.cs_current_insts = [] /\
  emit_op MUL [Var idx; Lit (n2w stride)] s0 = (Var ov,s1) /\
  emit_op ADD [saved_base; Var ov] s1 = (Var ep,sa) /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 ==>
  sb0.cs_current_insts =
    [mk_inst s0.cs_next_id MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst s1.cs_next_id ADD [saved_base; Var ov] [ep]] ++
      emitted_insts sa sb0 /\
  LENGTH sb0.cs_current_insts = 2 + LENGTH (emitted_insts sa sb0)
Proof
  rpt strip_tac >>
  imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >> gvs[]
QED

(* Operand-parametric EQ/JNZ boundary, valid at any instruction cursor. *)
Theorem eq_branch_zero_path:
  !ctx func s bb lhs rhs a b dv yes no j1 j2.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst j1 EQ [lhs; rhs] [dv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst j2 JNZ [Var dv; Label yes; Label no] []) /\
    ~s.vs_halted /\ eval_operand lhs s = SOME a /\
    eval_operand rhs s = SOME b ==>
    gas_marked_path F ctx func s 0
      (OK (jump_to (if a = b then yes else no)
        (update_var dv (bool_to_word (a = b)) s)))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var dv (bool_to_word (a = b)) s
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_path_edge ctx func s 0 (OK u)` by
    (`step_inst_base (mk_inst j1 EQ [lhs; rhs] [dv]) s =
       OK (update_var dv (bool_to_word (a = b)) s)` by
       (irule step_EQ >> simp[]) >>
     simp[Abbr `u`, gas_path_edge_def] >> qexists_tac `0` >>
     simp[mk_inst_def, is_terminator_def, step_inst_non_invoke,
          gas_count_step_def] >>
     gvs[mk_inst_def, update_var_def]) >>
  `eval_operand (Var dv) u = SOME (bool_to_word (a = b))` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE] >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`yes`, `no`, `j2`] assume_tac) >>
  `gas_path_edge ctx func u 0
    (OK (jump_to (if a = b then yes else no)
      (update_var dv (bool_to_word (a = b)) s)))` by
    (simp[gas_path_edge_def, Abbr `u`, update_var_def] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, mk_inst_def,
          gas_count_step_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if a = b then yes else no` >>
     Cases_on `a = b` >>
     gvs[bool_to_word_def, jump_to_def, update_var_def]) >>
  rewrite_tac[gas_marked_path_def] >>
  `gas_path ctx func
    (jump_to (if a = b then yes else no)
      (update_var dv (bool_to_word (a = b)) s)) 0
    (OK (jump_to (if a = b then yes else no)
      (update_var dv (bool_to_word (a = b)) s)))` by
    (irule (cj 1 gas_path_rules) >> simp[jump_to_def, update_var_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path_edge _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac (cj 2 gas_path_rules)) >>
  disch_then drule >> simp[]
QED

Theorem array_condition_block:
  !ctx func cc idx dv a b lbl exit_lbl stmts_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var idx; Lit b] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var idx cc = SOME a ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to (if a = b then exit_lbl else stmts_lbl)
           (update_var dv (bool_to_word (a = b)) cc)) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl _ = SOME bb` >>
  `!fu. run_from fu ctx func cc =
        run_from fu ctx func
          (update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1)` by
    (gen_tac >>
     `run_from fu ctx func cc = run_from fu ctx func
        (update_var dv (bool_to_word (a = b)) cc with
           vs_inst_idx := SUC cc.vs_inst_idx)` suffices_by simp[] >>
     irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst j1 EQ [Var idx; Lit b] [dv]`] >>
     simp[Abbr `bb`, get_instruction_def, mk_inst_def, is_terminator_def] >>
     simp[GSYM mk_inst_def] >> irule step_EQ >> simp[eval_operand_def]) >>
  qabbrev_tac `d1 = update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1` >>
  `jump_to (if a = b then exit_lbl else stmts_lbl) d1 =
   jump_to (if a = b then exit_lbl else stmts_lbl)
     (update_var dv (bool_to_word (a = b)) cc)` by
    simp[Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d1 = rr` by
    (irule run_from_jump_result >>
     simp[Abbr `d1`, update_var_def] >>
     qexistsl_tac [
       `mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []`,
       `if a = b then exit_lbl else stmts_lbl`] >>
     simp[Abbr `bb`, get_instruction_def,
          mk_inst_def, is_terminator_def, update_var_def] >>
     Cases_on `a = b` >>
     gvs[step_inst_base_def, bool_to_word_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE, jump_to_def, update_var_def]) >>
  fs[]
QED

Theorem array_condition_boundary:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl st
   k es cc n dv j1 j2 exit_lbl stmts_lbl.
  lookup_block cond_lbl func.fn_blocks =
    SOME <| bb_label := cond_lbl;
            bb_instructions :=
              [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
               mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond_lbl st k es cc /\
  n = LENGTH vs /\ n < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) ==>
  ?next.
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst (if k = n then exit_lbl else stmts_lbl) st k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
    next.vs_allocas = cc.vs_allocas /\
    gas_marked_path F ctx func cc 0 (OK next) /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr) /\
    alloca_frame cenv es st cc cenv es next
Proof
  rpt gen_tac >> strip_tac >>
  `k <= n` by fs[array_loop_inv_def] >>
  `(n2w k : bytes32) = n2w n <=> k = n` by
    (`k < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  qexists_tac `jump_to (if k = n then exit_lbl else stmts_lbl)
    (update_var dv (bool_to_word (k = n)) cc)` >>
  conj_tac
  >- (fs[array_loop_inv_def, lookup_var_def] >>
      `stmt_state_rel ctx func cenv cx es
         (update_var dv (bool_to_word (k = LENGTH vs)) cc)` by
        (irule stmt_state_rel_update_var >> simp[]) >>
      fs[stmt_state_rel_jump_to, jump_to_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (Cases_on `saved_base` >>
          gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
      fs[ret_pc_ok_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `x = dv` >> gvs[lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  conj_tac
  >- (`gas_marked_path F ctx func cc 0
        (OK (jump_to (if (n2w k : bytes32) = n2w n then exit_lbl else stmts_lbl)
          (update_var dv (bool_to_word ((n2w k : bytes32) = n2w n)) cc)))`
        suffices_by simp[] >>
      irule eq_branch_zero_path >>
      fs[array_loop_inv_def] >>
      simp[get_instruction_def, mk_inst_def, eval_operand_def]) >>
  reverse conj_tac
  >- (irule alloca_frame_same_state >>
      irule_at Any alloca_frame_update_var_same >>
      qexistsl_tac [`bool_to_word (k = n)`, `dv`] >>
      simp[jump_to_def, update_var_def]) >>
  fs[array_loop_inv_def] >> drule array_condition_block >>
  simp[] >> disch_then (qspecl_then [`ctx`, `cc`, `n2w k`] mp_tac) >>
  gvs[n2w_11]
QED

Theorem array_ret_pc_update[local]:
  ret_pc_ok cenv st s ==> ret_pc_ok cenv st (update_var v w s)
Proof
  rw[ret_pc_ok_def] >> first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `x = v` >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* A GAS-free straight-line block suffix followed by an unconditional jump. *)
Theorem inst_seq_jump_zero_path:
  !code s t ctx func bb iid lbl.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions =
      code ++ [mk_inst iid JMP [Label lbl] []] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) code /\
    run_inst_seq code s = OK t ==>
    gas_marked_path F ctx func s 0 (OK (jump_to lbl t))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[] >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `~t.vs_halted` by
    (drule gas_path_normal >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
     rpt strip_tac >> fs[EVERY_MEM] >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by metis_tac[] >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  `s.vs_inst_idx + LENGTH code < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP]) >>
  `get_instruction bb (s.vs_inst_idx + LENGTH code) =
     SOME (mk_inst iid JMP [Label lbl] [])` by
    (`DROP (s.vs_inst_idx + LENGTH code) bb.bb_instructions =
       [mk_inst iid JMP [Label lbl] []]` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP (LENGTH code)`) >>
        simp[DROP_DROP, DROP_LENGTH_APPEND, arithmeticTheory.ADD_COMM]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = [_]` (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_DROP]) >>
  `gas_path_edge ctx func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
     0 (OK (jump_to lbl t))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst iid JMP [Label lbl] []` >>
     conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     simp[step_inst_non_invoke, mk_inst_def,
          gas_count_step_def, is_terminator_def, step_jmp_behavior, jump_to_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  `gas_path ctx func (jump_to lbl t) 0 (OK (jump_to lbl t))` by
    (irule (cj 1 gas_path_rules) >> simp[jump_to_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_path_then) >>
  disch_then drule >> simp[gas_marked_path_def]
QED

Theorem array_increment_boundary:
  !ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond_lbl
   incr_lbl st k es dd nv i1 i2 i3.
  lookup_block incr_lbl func.fn_blocks =
    SOME <| bb_label := incr_lbl;
            bb_instructions :=
              [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
               mk_inst i2 ASSIGN [Var nv] [idx];
               mk_inst i3 JMP [Label cond_lbl] []] |> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr_lbl st k es dd /\ k < LENGTH vs /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) ==>
  ?next.
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst cond_lbl st (k+1) es next /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x dd) /\
    next.vs_allocas = dd.vs_allocas /\
    gas_marked_path F ctx func dd 0 (OK next) /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func dd = rr) /\
    alloca_frame cenv es st dd cenv es next
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `jump_to cond_lbl
    (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) dd))` >>
  conj_tac
  >- (fs[array_loop_inv_def] >>
      `stmt_state_rel ctx func cenv cx es
        (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) dd))` by
        (irule stmt_state_rel_update_var >> simp[] >>
         irule stmt_state_rel_update_var >> simp[]) >>
      `ret_pc_ok cenv st
        (update_var idx (n2w k + 1w) (update_var nv (n2w k + 1w) dd))` by
        (irule array_ret_pc_update >> irule array_ret_pc_update >> simp[]) >>
      fs[stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
      fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
         word_add_n2w] >>
      Cases_on `saved_base` >>
      gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  conj_tac
  >- (irule inst_seq_jump_zero_path >>
      fs[array_loop_inv_def] >>
      qexists_tac `i3` >>
      `step_inst_base (mk_inst i1 ADD [Var idx; Lit 1w] [nv]) dd =
         OK (update_var nv (n2w k + 1w) dd)` by
        (irule step_ADD >> simp[eval_operand_def]) >>
      simp[run_inst_seq_def] >>
      simp[mk_inst_def, is_terminator_def, step_inst_base_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  reverse conj_tac
  >- (simp[alloca_frame_def, jump_to_def, update_var_def] >>
      rpt strip_tac >> first_x_assum irule >>
      fs[local_region_def, not_local_ptr_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  fs[array_loop_inv_def] >> drule stmtSimForPartsTheory.for_incr_block >>
  simp[] >> disch_then (qspecl_then [`ctx`, `dd`, `n2w k`] mp_tac) >> simp[]
QED

Theorem array_address_prefix_run:
  !s idx saved_base arr_base k stride ov ep j3 j4.
  lookup_var idx s = SOME (n2w k) /\
  eval_operand saved_base s = SOME arr_base /\
  (!x. saved_base = Var x ==> x <> ov) ==>
  run_inst_seq
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] s =
  OK (update_var ep (n2w (w2n arr_base + k * stride))
        (update_var ov (n2w (k * stride)) s))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) s =
   OK (update_var ov (n2w (k * stride)) s)` by
    (simp[GSYM word_mul_n2w] >> irule step_MUL >> simp[eval_operand_def]) >>
  `eval_operand saved_base (update_var ov (n2w (k * stride)) s) = SOME arr_base` by
    (Cases_on `saved_base` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst j4 ADD [saved_base; Var ov] [ep])
     (update_var ov (n2w (k * stride)) s) =
   OK (update_var ep (arr_base + n2w (k * stride))
        (update_var ov (n2w (k * stride)) s))` by
    (irule step_ADD >> simp[eval_operand_def, update_var_def,
                            lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_def, GSYM word_add_n2w, n2w_w2n]
QED

Theorem array_address_prefix_boundary:
  !ctx func cenv cx es s idx saved_base arr_base k stride ov ep j3 j4 st.
  lookup_var idx s = SOME (n2w k) /\
  eval_operand saved_base s = SOME arr_base /\
  (!x. saved_base = Var x ==> x <> ov) /\
  stmt_state_rel ctx func cenv cx es s /\ ret_pc_ok cenv st s /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep ==>
  ?s1. run_inst_seq
      [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
       mk_inst j4 ADD [saved_base; Var ov] [ep]] s = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\ ret_pc_ok cenv st s1 /\
    lookup_var ep s1 = SOME (n2w (w2n arr_base + k * stride)) /\
    (s1 with vs_vars := s.vs_vars) = s /\
    (!x. x <> ov /\ x <> ep ==> lookup_var x s1 = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_address_prefix_run >>
  disch_then (qspecl_then [`stride`, `ep`, `j3`, `j4`] assume_tac) >>
  qexists_tac `update_var ep (n2w (w2n arr_base + k * stride))
    (update_var ov (n2w (k * stride)) s)` >> simp[] >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> simp[] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac
  >- (irule array_ret_pc_update >> irule array_ret_pc_update >> simp[]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem array_for_code_copy_reserved:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  local_ptrs_reserved bc sa
Proof
  simp[array_for_code_def]
QED

Theorem array_copy_live_ptrs_reserved:
  local_ptrs_reserved bc sa /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  !q. q = p \/ ~not_local_ptr bc scopes q ==> not_fresh_at sa q
Proof
  simp[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]
QED

Theorem array_empty_scope_ptr_transport:
  cenv_top_ext cenv bc (FEMPTY :: scopes) ==>
  (not_local_ptr bc (FEMPTY :: scopes) q <=> not_local_ptr cenv scopes q)
Proof
  strip_tac >>
  `!name entry. lookup_scopes name scopes = SOME entry ==>
      FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     fs[cenv_top_ext_def] >> first_x_assum drule >> simp[]) >>
  `bc.ce_imm_alloca = cenv.ce_imm_alloca` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  simp[not_local_ptr_def, lookup_scopes_def] >> metis_tac[]
QED

Theorem array_copy_run_declare:
  !ctx func cenv cx es s id p sz dw inst v tv sc rest a sa sb src ty tenv sw.
  compile_iter_elem_copy cenv src (Var p) (type_memory_size tv)
    LocMemory F ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  type_memory_size tv <= sz ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b len. b + len <= w2n dw \/ w2n dw + type_memory_size tv <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q` by
    metis_tac[array_copy_live_ptrs_reserved] >>
  `not_fresh_at sa p` by metis_tac[] >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all array_iter_copy_run >> strip_tac >>
  drule_all array_iter_copy_declare_rel >>
  disch_then (qspec_then `a` assume_tac) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem array_seq_prefix_result:
  !ctx func s t bb insts.
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  run_inst_seq insts s = OK t /\ ~s.vs_halted /\ ~t.vs_halted ==>
  !fuel. run_from fuel ctx func s =
    run_from fuel ctx func (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  drule_all exec_block_run_inst_seq >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  strip_tac >> first_x_assum drule >> strip_tac >> simp[run_from_def]
QED

Theorem array_empty_scope_rel_transport:
  !ctx func cenv bc cx es s.
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s
Proof
  rpt gen_tac >> strip_tac >>
  `!name entry. lookup_scopes name es.scopes = SOME entry ==>
      FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     fs[cenv_top_ext_def] >> first_x_assum drule >> simp[]) >>
  irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >>
  simp[stmt_state_rel_push_scope, lookup_scopes_def] >>
  fs[cenv_top_ext_def] >>
  qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _;
    ce_var_type := _|> = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem iter_memory_copy_no_gas:
  compile_iter_elem_copy cenv src dst stride LocMemory F et et sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `is_word_type et` >>
  Cases_on `is_bytestring_type et` >>
  gvs[compile_iter_elem_copy_def, compile_store_memory_def,
      compile_store_bytestring_def, compile_bytestring_copy_len_def,
      compile_copy_memory_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
      fresh_var_def, emit_def] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, mk_inst_def] >>
  Cases_on `type_memory_bytes cenv et` >>
  gvs[compile_copy_memory_def, comp_return_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, fresh_id_def, emit_def,
      emitted_insts_def, rich_listTheory.DROP_APPEND1, mk_inst_def]
QED

Theorem array_for_body_entry_run:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov ep j3 j4.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\
  not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb0) /\
    (!b len. b + len <= w2n dst \/ w2n dst + stride <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!caller. caller.cs_next_id <= sa.cs_next_id /\
      caller.cs_next_id <= ainst.inst_id ==>
      alloca_frame cenv es caller s bc
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
            :: es.scopes) t)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var ep (n2w (w2n arr_base + k * stride))
    (update_var ov (n2w (k * stride)) s)` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] s = OK s1` by
    (simp[Abbr `s1`] >> irule array_address_prefix_run >> simp[] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (simp[Abbr `s1`] >> irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s1` by
    (irule array_empty_scope_rel_transport >> qexists_tac `cenv` >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[array_copy_live_ptrs_reserved] >>
  `!x. Var ep = Var x ==> not_fresh_at sa x` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  `eval_operand (Var ep) s1 = SOME (n2w (w2n arr_base + k * stride)) /\
   eval_operand (Var p) s1 = SOME dst` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `val_in_memory tv v (w2n (n2w (w2n arr_base + k * stride) : bytes32)) s1.vs_memory` by
    gvs[Abbr `s1`, update_var_def, w2n_n2w] >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_size tv + 64 < dimword (:256)` by metis_tac[] >>
  drule_all array_iter_copy_run >> strip_tac >>
  `lookup_var p s1 = SOME dst /\
   FLOOKUP s1.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    (qpat_x_assum `lookup_var p s = SOME dst` mp_tac >>
     simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `(es with scopes := FEMPTY :: es.scopes).scopes = FEMPTY :: es.scopes /\
   lookup_scopes id (es with scopes := FEMPTY :: es.scopes).scopes = NONE /\
   not_local_ptr bc (es with scopes := FEMPTY :: es.scopes).scopes p /\
   type_memory_size tv <= sz` by (simp[lookup_scopes_def] >> gvs[]) >>
  `!q. q = p \/ ~not_local_ptr bc (es with scopes := FEMPTY :: es.scopes).scopes q ==>
    not_fresh_at sa q` by metis_tac[array_copy_live_ptrs_reserved] >>
  drule_all array_iter_copy_declare_rel >>
  disch_then (qspec_then `F` mp_tac) >>
  simp[lookup_scopes_def] >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (qpat_assum `run_inst_seq [_;_] s = OK s1`
        (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append) >>
      gvs[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s1` mp_tac >>
      simp[Abbr `s1`, update_var_def] >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[venom_state_component_equality] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
      simp[Abbr `s1`, update_var_def] >>
      disch_then irule >> decide_tac) >>
  gen_tac >> strip_tac >> suspend "entry_frame"
QED

Resume array_for_body_entry_run[entry_frame]:
  `alloca_frame bc (es with scopes := FEMPTY :: es.scopes) caller s1 bc
     (es with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
         :: es.scopes) t` by
    (irule stmtSimDeclComposeTheory.alloca_frame_declare_store >>
     qexistsl_tac [`ainst.inst_id`,
       `<|assignable := F; type := tv; value := v; popped := []|>`,
       `es with scopes := FEMPTY :: es.scopes`, `id`, `p`, `es.scopes`,
       `s1`, `sa`, `sa`, `FEMPTY`, `dst`, `sz`] >>
     simp[alloca_frame_same] >>
     conj_tac
     >- (rpt strip_tac >>
         `aid <> ainst.inst_id` by decide_tac >>
         `off + z' <= w2n dst \/ w2n dst + sz <= off` by
           (`allocas_non_overlapping s1` by
              fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
            qpat_x_assum `allocas_non_overlapping s1` mp_tac >>
            rewrite_tac[venomMemDefsTheory.allocas_non_overlapping_def] >>
            disch_then (qspecl_then
              [`aid`, `ainst.inst_id`, `off`, `z'`, `w2n dst`, `sz`] mp_tac) >>
            simp[]) >>
         first_x_assum irule >> decide_tac) >>
     fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
  `alloca_frame cenv es caller s1 bc
     (es with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
         :: es.scopes) t` by
    (irule stmtSimDeclComposeTheory.alloca_frame_cenv_pre >>
     qexists_tac `bc` >> simp[GSYM alloca_frame_push_pre] >>
     rpt strip_tac >> spose_not_then assume_tac >>
     fs[cenv_top_ext_def, lookup_scopes_def] >>
     qpat_x_assum `!n'. FLOOKUP bc.ce_vars n' <> _ ==> _`
       (qspec_then `n` mp_tac) >>
     qpat_x_assum `IS_SOME _` mp_tac >>
     qpat_x_assum `FLOOKUP cenv.ce_vars n <> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[optionTheory.IS_SOME_EXISTS, optionTheory.NOT_SOME_NONE]) >>
  irule alloca_frame_trans >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac >- simp[Abbr `s1`, update_var_def] >>
  simp[Abbr `s1`] >> irule alloca_frame_trans >>
  irule_at Any alloca_frame_update_var_same >>
  qexistsl_tac [`n2w (k * type_memory_size tv)`, `caller`, `ov`] >>
  simp[update_var_def, alloca_frame_update_var_same]
QED

Finalise array_for_body_entry_run

Theorem array_body_prefix_continuation:
  !ctx func cenv cx es s t sb bb insts.
  lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb.cs_current_insts bb.bb_instructions /\
  insts = sb.cs_current_insts /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  EVERY (\i. i.inst_opcode <> GAS) insts /\
  stmt_state_rel ctx func cenv cx es t /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s ==>
  ?s2. s2.vs_current_bb = sb.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func cenv cx es s2 /\
    s2.vs_vars = t.vs_vars /\ s2.vs_allocas = s.vs_allocas /\
    s2.vs_memory = t.vs_memory /\
    gas_marked_path F ctx func s 0 (OK s2) /\
    (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2)
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
   t.vs_halted = s.vs_halted` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  `isPREFIX insts (DROP s.vs_inst_idx bb.bb_instructions) /\
   lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\ ~t.vs_halted` by simp[] >>
  conj_tac
  >- (`FILTER (\i. i.inst_opcode = GAS) insts = []` by
        fs[FILTER_EQ_NIL, EVERY_MEM] >>
      drule_all tuple_run_inst_seq_gas_path >>
      simp[gas_marked_path_def]) >>
  drule_all array_seq_prefix_result >> simp[]
QED

Theorem array_ret_pc_copy_frame[local]:
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    lookup_var x t = lookup_var x s) ==>
  ret_pc_ok bc st t
Proof
  rw[ret_pc_ok_def] >>
  `not_fresh_at sa x /\ x <> ov /\ x <> ep` by metis_tac[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem array_for_body_entry:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov ep j3 j4 bb st.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
    ret_pc_ok bc st s2 /\ s2.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x s2 = lookup_var x s) /\
    gas_marked_path F ctx func s 0 (OK s2) /\
    (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2) /\
    (!b len. b + len <= w2n dst \/ w2n dst + stride <= b ==>
      mem_bytes_at b len s2.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!caller. caller.cs_next_id <= sa.cs_next_id /\
      caller.cs_next_id <= ainst.inst_id ==>
      alloca_frame cenv es caller s bc
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
            :: es.scopes) s2)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by
    simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule iter_memory_copy_no_gas >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    simp[mk_inst_def] >>
  `sb0.cs_current_insts = sb0.cs_current_insts` by simp[] >>
  drule_all array_body_prefix_continuation >> strip_tac >>
  `ret_pc_ok bc st t` by (irule array_ret_pc_copy_frame >> metis_tac[]) >>
  qexists_tac `s2` >> simp[] >>
  `!x. lookup_var x s2 = lookup_var x t` by simp[lookup_var_def] >>
  conj_tac
  >- (fs[ret_pc_ok_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> irule alloca_frame_same_state >>
  qexists_tac `t` >> simp[]
QED

Theorem push_scope_with_var_zero_exec:
  !ctx func es s s2 id tv v.
  gas_marked_path F ctx func s 0 (OK s2) ==>
  gas_marked_exec F (ctx,func) (push_scope_with_var id tv v) (es,s) []
    (INL ())
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes) (OK s2)
Proof
  simp[gas_marked_exec_def, gas_explicit_def, push_scope_with_var_def,
       return_def, evaluation_state_component_equality, combinTheory.APPLY_UPDATE_THM]
QED

Theorem array_body_scope_projection:
  !ctx func cenv bc c3 cx ei stmts r es2 s sc rest.
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (r,es2) /\
  cenv_top_ext bc c3 es2.scopes /\
  stmt_state_rel ctx func c3 cx es2 s /\ es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  `cenv_top_ext cenv c3 es2.scopes` by
    (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `ei.scopes`] >>
     gvs[preserves_scopes_dom_def]) >>
  drule_all stmt_state_rel_pop_top_ext >> simp[]
QED

Theorem array_condition_exit_framed:
  !ctx func cenv cx P vs id idx saved_base arr_base p dst sz ainst cond_lbl st
   es cc dv j1 j2 exit_lbl stmts_lbl caller.
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (LENGTH vs) es cc /\
  LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) ==>
  ?next. next.vs_current_bb = exit_lbl /\ next.vs_inst_idx = 0 /\
    ~next.vs_halted /\ stmt_state_rel ctx func cenv cx es next /\
    (!x w. not_fresh_at caller x /\ lookup_var x cc = SOME w ==>
      lookup_var x next = SOME w) /\
    (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
      FLOOKUP next.vs_allocas aid = SOME b) /\
    gas_marked_path F ctx func cc 0 (OK next) /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr) /\
    alloca_frame cenv es st cc cenv es next
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  drule_all array_condition_boundary >> strip_tac >>
  qexists_tac `next` >> fs[array_loop_inv_def] >> metis_tac[]
QED

(* Value-independent cleanup boundary: no predetermined body run. *)
Theorem loop_body_cleanup_exec:
  !memory ctx func body es s marks res ee r sc rest.
  gas_marked_exec memory (ctx,func) body (es,s) marks res ee r /\
  ee.scopes = sc :: rest ==>
  gas_marked_exec memory (ctx,func)
    (finally (try (do body; return F od) handle_loop_exception) pop_scope)
    (es,s) marks
    (case res of INL u => INL F
     | INR ex => if ex = BreakException then INL T
                 else if ex = ContinueException then INL F else INR ex)
    (ee with scopes := rest) r
Proof
  rpt gen_tac >> simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> simp[finally_def, try_def, ignore_bind_def, bind_def] >>
  Cases_on `res` >> simp[return_def, pop_scope_def, bind_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = BreakException` >> Cases_on `ex = ContinueException` >>
  gvs[handle_loop_exception_def, return_def, raise_def, bind_def, pop_scope_def]
QED

Theorem loop_body_cleanup_exempt_cert:
  !memory tops ctx func body es s marks err ee leaf finish sc rest.
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (body : evaluation_state -> unit evaluation_result) (return ()))
    (es,s) marks (err,ee) (leaf,finish) /\ ee.scopes = sc :: rest ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind
      (finally (try (do body; return F od) handle_loop_exception) pop_scope)
      (return ()))
    (es,s) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >>
  rewrite_tac[ignore_bind_finally_unit, ignore_bind_try_unit,
              ignore_bind_return_twice] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  conj_tac >- simp[pop_scope_def, return_def] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[handle_loop_exception_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem gas_marked_exec_all_gas_post:
  !memory ctx func source es s marks res ee r Q.
  (!gs result finish. source (es with gas_obs := gs) = (result,finish) ==>
      Q result (finish with gas_obs := [])) /\
  gas_marked_exec memory (ctx,func) source (es,s) marks res ee r ==>
  Q res (ee with gas_obs := [])
Proof
  rpt gen_tac >> simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem loop_round_exempt_cert:
  !memory tops ctx func body es s t id tv v marks err ee leaf finish sc rest.
  gas_marked_exec memory (ctx,func) (push_scope_with_var id tv v)
    (es,s) [] (INL ())
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes) (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (body : evaluation_state -> unit evaluation_result) (return ()))
    (es with <|scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes; gas_obs := []|>,t) marks (err,ee) (leaf,finish) /\
  ee.scopes = sc :: rest ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind
      (do push_scope_with_var id tv v;
          finally (try (do body; return F od) handle_loop_exception) pop_scope od)
      (return ()))
    (es,s) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_unit >> simp[] >> disch_then irule >>
  rewrite_tac[GSYM ignore_bind_def] >>
  irule loop_body_cleanup_exempt_cert >> goal_assum (drule_at Any) >> simp[]
QED

Theorem array_body_to_increment:
  !ctx func cenv cx es s r sb sj exit_lbl incr_lbl.
  stmt_lands (InLoop exit_lbl incr_lbl) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\
    fn_has_code sb sj func) ==>
  ?dd. dd.vs_current_bb = incr_lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
    stmt_state_rel ctx func cenv cx es dd /\
    dd.vs_vars = s.vs_vars /\ dd.vs_allocas = s.vs_allocas /\
    dd.vs_memory = s.vs_memory /\
    gas_marked_path F ctx func s 0 (OK dd) /\
    (!fuel rr. run_from fuel ctx func dd = rr /\ (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s = rr)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r = INL ()`
  >- (gvs[stmt_lands_def] >>
      `gas_marked_path F ctx func s 0 (OK (jump_to incr_lbl s))` by
        (simp[gas_marked_path_def] >> irule emit_jump_zero_path >>
         simp[] >> qexistsl_tac [`sb`, `sj`] >> simp[]) >>
      qexists_tac `jump_to incr_lbl s` >>
      simp[stmt_state_rel_jump_to, jump_to_def] >>
      `is_terminator (mk_inst sb.cs_next_id JMP [Label incr_lbl] []).inst_opcode /\
       (mk_inst sb.cs_next_id JMP [Label incr_lbl] []).inst_opcode <> INVOKE /\
       step_inst_base (mk_inst sb.cs_next_id JMP [Label incr_lbl] []) s =
         OK (jump_to incr_lbl s)` by
        simp[mk_inst_def, is_terminator_def, step_jmp_behavior] >>
      drule_at (Pat `fn_has_code _ _ _`) run_from_jump_end >>
      disch_then (qspecl_then [`ctx`, `s`,
        `mk_inst sb.cs_next_id JMP [Label incr_lbl] []`, `incr_lbl`] mp_tac) >>
      simp[jump_to_def]) >>
  gvs[stmt_lands_def] >> qexists_tac `s` >>
  simp[gas_marked_path_def, gas_path_rules] >> metis_tac[]
QED

(* Logical copy-entry contract, shared by counted preparation and code extraction. *)
Definition array_entry_inputs_def:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx saved_base arr_base k stride ov ep j3 j4 bb st <=>
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ret_pc_ok bc st s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep)
End

Definition array_entry_ready_def:
  array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s s2 <=>
  s2.vs_current_bb = sb0.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
  stmt_state_rel ctx func bc cx
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
  ret_pc_ok bc st s2 /\ s2.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    lookup_var x s2 = lookup_var x s) /\
  gas_marked_path F ctx func s 0 (OK s2) /\
  (!fuel. run_from fuel ctx func s = run_from fuel ctx func s2)
End

Theorem array_entry_inputs_run:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx saved_base arr_base k stride ov ep j3 j4 bb st ==>
  ?s2. array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep st s s2 /\
    (!caller. caller.cs_next_id <= sa.cs_next_id /\
      caller.cs_next_id <= ainst.inst_id ==>
      alloca_frame cenv es caller s bc
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
            :: es.scopes) s2)
Proof
  pure_rewrite_tac[array_entry_inputs_def, array_entry_ready_def] >>
  strip_tac >> drule_all array_for_body_entry >> strip_tac >>
  qexists_tac `s2` >> simp[]
QED

Theorem array_round_body_prepare:
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
    idx saved_base arr_base k stride ov ep j3 j4 bb sb0 /\
  gas_marked_path F ctx func cc 0 (OK s) /\
  ei = es with <|scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes; gas_obs := []|> /\
  stmt_frag ctx func cx lctx RetQ bc m source ei /\
  m sb0 = (bc',sb1) /\ fn_has_code sb0 sb1 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ~block_is_terminated sb0 /\ gas_admissible source (stmt_res_ok lctx) ei ==>
  ?s2. array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep sb0 s s2 /\
    gas_marked_exec F (ctx,func) (push_scope_with_var id tv v) (es,cc) []
      (INL ())
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
          :: es.scopes) (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) source (ei,s2)
      (stmt_post ctx func cx lctx bc bc' sb0 sb1 ei s2)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
    (!caller. caller.cs_next_id <= sa.cs_next_id /\
      caller.cs_next_id <= ainst.inst_id ==>
      alloca_frame cenv es caller s bc
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
            :: es.scopes) s2)
Proof
  strip_tac >> drule_all array_entry_inputs_run >> strip_tac >>
  qexists_tac `s2` >> (conj_tac >- simp[]) >>
  `gas_marked_path F ctx func cc 0 (OK s2)` by
    (fs[array_entry_ready_def] >>
     drule_all gas_marked_path_then >> simp[]) >>
  (conj_tac >- (irule push_scope_with_var_zero_exec >> simp[])) >>
  reverse conj_tac >- simp[] >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then irule >> simp[] >>
  fs[array_entry_ready_def] >>
  `!E. stmt_state_rel ctx func bc cx E s2 ==>
       stmt_state_rel ctx func bc cx (E with gas_obs := []) s2` by
    (rpt strip_tac >>
     `s2 = s2 with <|vs_gas_readings := s2.vs_gas_readings;
                     vs_inst_idx := s2.vs_inst_idx|>` by
       simp[venomStateTheory.venom_state_component_equality] >>
     pop_assum SUBST1_TAC >> irule msg_gas_state_frame >> simp[]) >>
  first_x_assum (qspec_then `es with scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes` mp_tac) >>
  impl_tac >- fs[] >>
  match_mp_tac EQ_IMPLIES >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

(* The selected body run is normalized only at its finish; P is never
   transported across an arbitrary gas update. *)
Theorem array_body_counted_post:
  gas_marked_exec F (ctx,func) (eval_stmts cx stmts) (ei,s0) marks res ee (OK t) /\
  cenv_top_ext cenv bc ei.scopes /\
  stmt_post ctx func cx lctx bc bc' sa sb ei s0 res (ee with gas_obs := []) t /\
  (!gs r es2. eval_stmts cx stmts (ei with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)) ==>
  ?sc rest. ee.scopes = sc :: rest /\
    stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb) /\
    stmt_state_rel ctx func cenv cx
      (ee with <|scopes := rest; gas_obs := []|>) t /\
    ((res = INL () \/ res = INR ContinueException) ==>
      P (ee with <|scopes := rest; gas_obs := []|>) /\
      lookup_scopes id rest = NONE) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    alloca_frame bc ei sa s0 cenv
      (ee with <|scopes := rest; gas_obs := []|>) t
Proof
  strip_tac >>
  `eval_stmts cx stmts
     (ei with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (res,ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. eval_stmts _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> gvs[stmt_post_def] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[] >>
      drule eval_stmts_preserves_scopes_dom >> strip_tac >>
      `cenv_top_ext cenv cenv'' ee.scopes` by
        (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `ei.scopes`] >>
         gvs[preserves_scopes_dom_def]) >>
      simp[] >>
      `alloca_frame bc ei sa s0 cenv ((ee with gas_obs := []) with scopes := rest) t`
        suffices_by simp[] >>
      irule alloca_frame_pop >>
      conj_tac >- (qexists_tac `sc` >> simp[]) >>
      qexists_tac `cenv''` >> gvs[]) >>
  `stmt_state_rel ctx func cenv cx
    ((ee with gas_obs := []) with scopes := rest) t` suffices_by
      simp[evaluation_state_component_equality] >>
  irule array_body_scope_projection >>
  (conj_tac >- (qexists_tac `sc` >> simp[])) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem array_body_continue_iteration_framed[local]:
  !ctx func cenv cx P vs id idx saved_base arr_base p dst sz ainst st k es s
   r sb sj exit_lbl incr_lbl cond_lbl nv i1 i2 i3.
  stmt_lands (InLoop exit_lbl incr_lbl) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst s.vs_current_bb st k es (s with vs_inst_idx := 0) /\

  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  (r = INL () ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) ==>
  ?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (k+1) es next /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x s) /\
    next.vs_allocas = s.vs_allocas /\
    gas_marked_path F ctx func s 0 (OK next) /\
    alloca_frame cenv es st s cenv es next
Proof
  rpt gen_tac >> strip_tac >>
  `~s.vs_halted /\ stmt_state_rel ctx func cenv cx es s` by
    fs[array_loop_inv_def, stmt_state_rel_inst_idx] >>
  drule array_body_to_increment >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `sj`] mp_tac) >>
  simp[] >> strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst incr_lbl st k es dd` by
    (gvs[array_loop_inv_def, stmt_state_rel_inst_idx, ret_pc_ok_def,
         lookup_var_def] >>
     Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  drule_all array_increment_boundary >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK next)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `alloca_frame cenv es st s cenv es next` by
    (qhdtm_x_assum `alloca_frame` mp_tac >>
     simp[alloca_frame_def, local_region_def, lookup_var_def]) >>
  qexists_tac `next` >> simp[lookup_var_def] >> metis_tac[]
QED

Theorem array_body_break_lands:
  stmt_lands (InLoop exit_lbl incr_lbl) sb (INR BreakException) s ==>
  s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0
Proof
  simp[stmt_lands_def]
QED

Theorem array_saved_operand_frame:
  (!l. op <> Label l) /\ eval_operand op s = SOME w /\
  (!x. op = Var x ==> lookup_var x t = lookup_var x s) ==>
  eval_operand op t = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem array_body_runtime_frame:
  !cenv bc scopes sa s0 st idx k p dst saved_base base ainst sz s.
  cenv_top_ext cenv bc scopes /\ ret_pc_ok bc sa s0 /\
  ret_pc_ok cenv st s0 /\
  lookup_var idx s0 = SOME (n2w k) /\
  lookup_var p s0 = SOME dst /\ eval_operand saved_base s0 = SOME base /\
  FLOOKUP s0.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  not_fresh_at sa idx /\ not_fresh_at sa p /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  (!l. saved_base <> Label l) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) ==>
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  eval_operand saved_base s = SOME base /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s
Proof
  rpt strip_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (irule array_saved_operand_frame >> conj_tac >- simp[] >>
      qexists_tac `s0` >> simp[] >>
      Cases_on `saved_base` >> gvs[eval_operand_def] >> metis_tac[])
  >- metis_tac[] >>
  fs[ret_pc_ok_def, cenv_top_ext_def] >>
  `bc.ce_return_pc = cenv.ce_return_pc` by
    (qpat_x_assum `_ with <|ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _|> = _` mp_tac >>
     simp[compile_env_component_equality]) >>
  metis_tac[]
QED

Theorem array_body_compiler_env:
  compile_stmts bc lctx ty stmts sa = ((),sb) ==>
  ?bc'. stmts_env bc lctx ty stmts sa = (bc',sb)
Proof
  simp[compile_stmts_env] >>
  Cases_on `stmts_env bc lctx ty stmts sa` >> simp[]
QED

(* Fully anchored logical input/output contracts for the copy prefix. *)
Theorem array_for_code_entry_inputs:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl st k es s /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\
  val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\ ret_pc_ok bc sb0 s /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  array_entry_inputs ctx func cenv bc cx es s id p sz dst ainst tv (EL k vs)
    et tenv sa sb0 idx saved_base arr_base k stride ov ep j3 j4 bb sb0
Proof
  pure_rewrite_tac[array_for_code_def, array_loop_inv_def, array_entry_inputs_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  fs[ALL_DISTINCT] >> metis_tac[]
QED

Theorem array_entry_ready_runtime:
  array_entry_ready ctx func bc cx es id tv v sb0 sa ov ep sb0 s s2 /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst lbl st k es s /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  lookup_var idx s2 = SOME (n2w k) /\
  eval_operand saved_base s2 = SOME arr_base /\ lookup_var p s2 = SOME dst /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok cenv st s2
Proof
  strip_tac >>
  `ret_pc_ok cenv st s2` by
    (irule array_ret_pc_copy_frame >>
     fs[array_entry_ready_def, array_loop_inv_def] >> metis_tac[]) >>
  fs[array_entry_ready_def, array_loop_inv_def] >>
  irule array_saved_operand_frame >> metis_tac[]
QED

Theorem array_for_code_iteration_static:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  fn_has_code sb0 sb1 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv) /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep)
Proof
  simp[array_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED

Theorem array_for_code_entry_static:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj ==>
  (!scs. not_local_ptr cenv scs dv) /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv)
Proof
  simp[array_for_code_def, ALL_DISTINCT] >> metis_tac[]
QED


Definition array_caller_frame_def:
  array_caller_frame caller (s:venom_state) t <=>
    (!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b)
End

Theorem array_caller_frame_refl[simp]:
  array_caller_frame caller s s
Proof
  simp[array_caller_frame_def]
QED

Theorem array_caller_frame_trans:
  array_caller_frame caller s t /\ array_caller_frame caller t u ==>
  array_caller_frame caller s u
Proof
  simp[array_caller_frame_def] >> metis_tac[]
QED

Theorem array_body_finish_counted:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\ k < LENGTH vs /\
  gas_marked_exec F (ctx,func) (eval_stmts cx stmts) (entry,s2) marks res ee (OK t) /\
  stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 entry s2
    res (ee with gas_obs := []) t /\
  cenv_top_ext cenv bc entry.scopes /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)) /\
  lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
  eval_operand saved_base s2 = SOME arr_base /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  array_caller_frame caller cc s2 /\
  alloca_frame cenv es caller cc bc entry s2 /\
  caller.cs_next_id <= sb0.cs_next_id /\ caller.cs_next_id <= st.cs_next_id ==>
  ?rest u. ee.scopes <> [] /\ rest = TL ee.scopes /\
    gas_marked_path F ctx func t 0 (OK u) /\ array_caller_frame caller cc u /\
    ((res = INR BreakException /\ u.vs_current_bb = exit_lbl /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      stmt_state_rel ctx func cenv cx
        (ee with <|scopes := rest; gas_obs := []|>) u) \/
     ((res = INL () \/ res = INR ContinueException) /\
      array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
        ainst cond_lbl st (SUC k) (ee with <|scopes := rest; gas_obs := []|>) u)) /\
    alloca_frame cenv es caller cc cenv
      (ee with <|scopes := rest; gas_obs := []|>) u
Proof
  strip_tac >> drule_all array_body_counted_post >> strip_tac >>
  `alloca_frame cenv es caller cc cenv
     (ee with <|scopes := rest; gas_obs := []|>) t` by
    (irule alloca_frame_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> fs[array_caller_frame_def]) >>
  `array_caller_frame caller cc t` by
    (fs[array_caller_frame_def] >> metis_tac[]) >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`rest`, `t`] >>
      fs[stmt_lands_def, gas_marked_path_def, gas_path_rules]) >>
  `res = INL () \/ res = INR ContinueException` by fs[stmt_lands_def] >>
  drule_all array_body_runtime_frame >> strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst t.vs_current_bb st k (ee with <|scopes := rest; gas_obs := []|>)
    (t with vs_inst_idx := 0)` by
      (fs[array_loop_inv_def, stmt_state_rel_inst_idx, lookup_var_def,
           ret_pc_ok_def] >>
       Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  drule array_for_code_iteration_static >> strip_tac >>
  `res = INL () ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func` by
    fs[array_for_code_def] >>
  qhdtm_x_assum `array_for_code` kall_tac >>
  `?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (ee with <|scopes := rest; gas_obs := []|>) next /\
     (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x t) /\
     next.vs_allocas = t.vs_allocas /\ gas_marked_path F ctx func t 0 (OK next) /\
     alloca_frame cenv (ee with <|scopes := rest; gas_obs := []|>) st t cenv
       (ee with <|scopes := rest; gas_obs := []|>) next` by
    (irule array_body_continue_iteration_framed >> simp[] >>
     goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
     goal_assum (drule_at (Pat `stmt_lands _ _ _ _`)) >>
     qexists_tac `sj` >> simp[]) >>
  `alloca_frame cenv es caller cc cenv
     (ee with <|scopes := rest; gas_obs := []|>) next` by
    (irule alloca_frame_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> fs[array_caller_frame_def]) >>
  qexistsl_tac [`rest`, `next`] >> simp[arithmeticTheory.ADD1] >>
  fs[array_caller_frame_def] >> metis_tac[]
QED

Theorem array_round_prepare:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry /\
  caller.cs_next_id <= sa.cs_next_id /\ caller.cs_next_id <= ainst.inst_id /\
  caller.cs_next_id <= st.cs_next_id ==>
  ?s2 bc'.
    stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
    eval_operand saved_base s2 = SOME arr_base /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    array_caller_frame caller cc s2 /\
    gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
      (es,cc) [] (INL ())
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
      (OK s2) /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
      (stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 entry s2)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
    alloca_frame cenv es caller cc bc entry s2
Proof
  strip_tac >>
  drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  `LENGTH vs = LENGTH vs` by simp[] >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  drule_all array_condition_boundary >> strip_tac >>
  rename1 `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` >>
  `k <> LENGTH vs` by decide_tac >> gvs[] >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule array_for_code_scope_frame >> fs[array_loop_inv_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  drule_all array_for_code_entry_inputs >> strip_tac >>
  drule array_for_code_iteration_static >> strip_tac >>
  drule array_for_code_stmts >> strip_tac >>
  drule array_body_compiler_env >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_frag _ _ _ _ _ _ _ _ entry` >>
  `entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|>` by simp[Abbr `entry`] >>
  qhdtm_x_assum `array_for_code` kall_tac >>
  drule_all array_round_body_prepare >> strip_tac >>
  drule_all array_entry_ready_runtime >> strip_tac >>
  `alloca_frame cenv es caller s bc entry s2` by
    (qpat_x_assum `!caller. _` (qspec_then `caller` mp_tac) >>
     simp[Abbr `entry`, alloca_frame_def]) >>
  `alloca_frame cenv es caller cc cenv es s` by
    (qpat_x_assum `alloca_frame cenv es st cc cenv es s` mp_tac >>
     qpat_x_assum `caller.cs_next_id <= st.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[alloca_frame_def] >>
     disch_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
     `aid < st.cs_next_id` by (fs[] >> decide_tac) >>
     first_x_assum irule >> fs[] >> metis_tac[]) >>
  `alloca_frame cenv es caller cc bc entry s2` by
    (irule alloca_frame_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`s2`, `bc'`] >> simp[] >>
  qhdtm_x_assum `array_entry_ready` mp_tac >>
  qpat_x_assum `!x. not_fresh_at caller x ==> _` mp_tac >>
  qpat_x_assum `!x. x <> dv ==> _` mp_tac >>
  qpat_x_assum `s.vs_allocas = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[array_entry_ready_def, array_caller_frame_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem array_for_round_counted:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv (EL k vs) /\
  val_wf tv (EL k vs) /\ w2n arr_base + k * stride < dimword (:256) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st k es s ==>
     val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) entry /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)) /\
  caller.cs_next_id <= sa.cs_next_id /\ caller.cs_next_id <= ainst.inst_id /\
  caller.cs_next_id <= st.cs_next_id /\ caller.cs_next_id <= sb0.cs_next_id ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (es,cc)
    (\res ee t. ?broke. res = INL broke /\ array_caller_frame caller cc t /\
      (broke ==> t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        stmt_state_rel ctx func cenv cx ee t) /\
      (~broke ==> array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base
        p dst sz ainst cond_lbl st (SUC k) ee t) /\
      alloca_frame cenv es caller cc cenv ee t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  `gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl)) entry` by
    (qpat_x_assum `!gs r es2. _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_admissible_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) round (es,cc) Q R` >>
  drule_all array_round_prepare >> strip_tac >>
  qhdtm_x_assum `stmt_frag` kall_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >> rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "ordinary"
  >> suspend "exempt"
QED

Resume array_for_round_counted[exempt]:
  `?sc rest. ee.scopes = sc :: rest` by
    (drule gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  gvs[] >>
  drule_all loop_round_exempt_cert >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  simp[Abbr `round`] >> goal_assum (drule_at Any)
QED

Resume array_for_round_counted[ordinary]:
  qhdtm_x_assum `gas_summary_at` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  `?sc rest. ee.scopes = sc :: rest` by
    (qhdtm_assum `gas_marked_exec` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  drule_all loop_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec F (ctx,func) cleanup _ _ wrapped fin r` >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin r` by
    (simp[Abbr `round`, ignore_bind_def] >>
     irule (SRULE [] (Q.INST [`left` |-> `[]`] gas_marked_exec_bind_normal)) >>
     goal_assum (drule_at Any) >> gvs[]) >>
  strip_tac >- suspend "normal_finish" >> suspend "exit_finish"
QED

Resume array_for_round_counted[exit_finish]:
  fs[] >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
     metis_tac[stmt_exit_loop_ctl]) >>
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `r`] >> simp[] >> disj2_tac >>
  gvs[Abbr `R`, Abbr `fin`, Abbr `wrapped`, stmt_exit_def]
QED

Resume array_for_round_counted[normal_finish]:
  fs[] >>
  `cenv_top_ext cenv bc entry.scopes` by
    (drule array_for_code_scope_frame >>
     fs[array_loop_inv_def, cenv_top_ext_def] >> metis_tac[]) >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule_all array_body_finish_counted >> strip_tac >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin (OK u)` by
    (qhdtm_x_assum `gas_marked_path` mp_tac >>
     qpat_x_assum `gas_marked_exec _ _ round _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     rpt strip_tac >> simp[] >>
     qpat_x_assum `gas_marked_path _ _ _ cc _ _` mp_tac >>
     disch_then (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `OK u`] >> simp[] >> disj1_tac >>
  simp[Abbr `Q`, Abbr `fin`, Abbr `wrapped`] >>
  gvs[]
QED
Finalise array_for_round_counted

Theorem array_loop_last_counted:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (LENGTH vs) es s /\
  LENGTH vs < dimword (:256) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\ array_caller_frame caller old s /\
  caller.cs_next_id <= st.cs_next_id /\
  alloca_frame cenv origin_es caller old cenv es s ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx (es with gas_obs := []) t /\
    array_caller_frame caller old t /\
    alloca_frame cenv origin_es caller old cenv (es with gas_obs := []) t
Proof
  strip_tac >> drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv es.scopes dv` by simp[] >>
  drule_all array_condition_exit_framed >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) next` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`next.vs_gas_readings`, `next.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  `alloca_frame cenv origin_es caller old cenv es next` by
    (irule alloca_frame_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> fs[array_caller_frame_def]) >>
  `alloca_frame cenv origin_es caller old cenv (es with gas_obs := []) next` by
    (qpat_x_assum `alloca_frame cenv origin_es caller old cenv es next` mp_tac >>
     simp[alloca_frame_def]) >>
  qexists_tac `next` >> simp[] >>
  fs[array_caller_frame_def] >> metis_tac[]
QED

Theorem array_for_loop_counted:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\ evaluate_type tenv et = SOME tv /\
  (!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)) /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!j ei s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst stmts_lbl st j ei s /\ j < LENGTH vs ==>
     val_in_memory tv (EL j vs) (w2n arr_base + j * stride) s.vs_memory /\
     ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\ (!l. saved_base <> Label l) /\
  (!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    w2n arr_base + j * stride < dimword (:256) /\
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\
          lookup_scopes id rest = NONE))) /\
  k <= LENGTH vs /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\ array_caller_frame caller old cc /\
  gas_admissible (eval_for cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es /\
  caller.cs_next_id <= sa.cs_next_id /\ caller.cs_next_id <= ainst.inst_id /\
  caller.cs_next_id <= st.cs_next_id /\ caller.cs_next_id <= sb0.cs_next_id /\
  alloca_frame cenv origin_es caller old cenv es cc ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts (DROP k vs)) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      array_caller_frame caller old t /\
      alloca_frame cenv origin_es caller old cenv ee t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  qabbrev_tac `Inv = \j ei s.
    array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst cond_lbl st j ei s /\ array_caller_frame caller old s /\
      alloca_frame cenv origin_es caller old cenv ei s` >>
  qabbrev_tac `Done = \ei s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
    ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ei s /\
    array_caller_frame caller old s /\
    alloca_frame cenv origin_es caller old cenv ei s` >>
  qabbrev_tac `R = \ex ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r` >>
  `(!j ei s. j < LENGTH vs /\ Inv j ei s /\
      gas_admissible (eval_for cx tv id stmts (DROP j vs)) (stmt_res_ok lctx) ei ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (do push_scope_with_var id tv (EL j vs);
            finally (try (do eval_stmts cx stmts; return F od)
              handle_loop_exception) pop_scope od) (ei,s)
        (\res ee t. ?broke. res = INL broke /\
          (broke ==> Done ee t) /\ (~broke ==> Inv (SUC j) ee t))
        (\res ee r. ?ex. res = INR ex /\ R ex ee r)) /\
    (!ei s. Inv (LENGTH vs) ei s ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\ Done (ei with gas_obs := []) t)` by
    (conj_tac >- suspend "round" >> suspend "last") >>
  drule eval_for_rounds >>
  disch_then (qspecl_then [`k`, `es`, `cc`] mp_tac) >>
  simp[Abbr `Inv`, Abbr `Done`, Abbr `R`]
QED

Resume array_for_loop_counted[last]:
  rpt gen_tac >> simp[Abbr `Inv`, Abbr `Done`] >> strip_tac >>
  `!x. not_fresh_at caller x ==> x <> dv` by metis_tac[] >>
  drule_all array_loop_last_counted >> simp[]
QED

Resume array_for_loop_counted[round]:
  rpt gen_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `P ei /\ lookup_scopes id ei.scopes = NONE` by fs[array_loop_inv_def] >>
  qpat_assum `!ei j. _` drule_all >> strip_tac >>
  `value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)` by metis_tac[] >>
  qabbrev_tac `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` >>
  `!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\
        lookup_scopes id rest = NONE)` by
    (qpat_x_assum `!gs r es2. _` mp_tac >> simp[Abbr `entry`]) >>
  `!t. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst stmts_lbl st j ei t ==>
    val_in_memory tv (EL j vs) (w2n arr_base + j * stride) t.vs_memory /\
    ret_pc_ok bc sb0 t` by metis_tac[] >>
  `entry = ei with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
    gas_obs := []|>` by simp[Abbr `entry`] >>
  drule_all array_for_round_counted >> strip_tac >>
  qhdtm_x_assum `gas_outcome` mp_tac >>
  qpat_x_assum `array_caller_frame caller old s` mp_tac >>
  qpat_x_assum `alloca_frame cenv origin_es caller old cenv ei s` mp_tac >>
  simp[Abbr `Done`, Abbr `R`, NoAsms] >>
  rpt (pop_assum kall_tac) >> strip_tac >> strip_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qhdtm_x_assum `gas_summary_at` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      suspend "round_post") >>
  qexists_tac `marks` >> disj2_tac >> goal_assum (drule_at Any)
QED
Resume array_for_loop_counted[round_post]:
  markerLib.RESUME_TAC >> gvs[] >>
  `array_caller_frame caller old t` by
    (irule array_caller_frame_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `alloca_frame cenv origin_es caller old cenv es_end t` by
    (irule alloca_frame_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> fs[array_caller_frame_def]) >>
  simp[]
QED
Finalise array_for_loop_counted
