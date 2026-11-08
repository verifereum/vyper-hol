Theory bodyPtrBytestringBuiltinsZeroCheck
Ancestors
  bodyPtrBytestringBuiltinsBounds venomExecSemantics venomState venomInst
  fragGasPathPtr ptrDiscipline ptrSafeRun finite_map list
  fragExec emitHelperProps compileEnv emitHelper arithmetic

Theorem zero_check_iszero_step:
  eval_operand y s = SOME w ==>
  step_inst_base (mk_inst id ISZERO [y] [z]) s =
    OK (update_var z (bool_to_word (w = 0w)) s)
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def]
QED

Theorem zero_check_iszero_edge:
  eval_operand y s = SOME w /\ op_taint tn y = {} /\ op_prov G y = NONE /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ISZERO [y] [z]) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {z})) (tn with t_var := tn.t_var |+ (z,{}))
    (OK ((update_var z (bool_to_word (w = 0w)) s) with
       vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ISZERO [y] [z]) s =
     OK (update_var z (bool_to_word (w = 0w)) s)` by
    simp[zero_check_iszero_step] >>
  `step_prov PG G (mk_inst id ISZERO [y] [z])
     (update_var z (bool_to_word (w = 0w)) s) = DRESTRICT G (COMPL {z}) /\
   step_taint (mk_inst id ISZERO [y] [z]) s
     (update_var z (bool_to_word (w = 0w)) s) tn =
      (tn with t_var := tn.t_var |+ (z,{}))` by
    (irule slice_scalar_ghost >> simp[update_var_def]) >>
  qpat_x_assum `step_prov _ _ _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule slice_scalar_counted_edge >> simp[update_var_def] >> metis_tac[]
QED

Theorem zero_check_abort_counted:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ISZERO [y] [z]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) ISZERO [Var z] [nz]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME (mk_inst (id+2) ASSERT [Var nz] []) /\
  eval_operand y s = SOME 0w /\ op_taint tn y = {} /\ op_prov G y = NONE ==>
  ?s1 s2.
    s1 = (update_var z 1w s) with vs_inst_idx := SUC s.vs_inst_idx /\
    s2 = (update_var nz 0w s1) with vs_inst_idx := SUC s1.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (DRESTRICT (DRESTRICT G (COMPL {z})) (COMPL {nz}))
      ((tn with t_var := tn.t_var |+ (z,{})) with
        t_var := (tn.t_var |+ (z,{})) |+ (nz,{}))
      (Abort Revert_abort (revert_state (set_returndata [] s2)))
Proof
  strip_tac >>
  qabbrev_tac `s1 = (update_var z 1w s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var nz 0w s1) with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {z})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (z,{})` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {nz})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (nz,{})` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`] >>
     irule (Q.INST [`w` |-> `0w`] zero_check_iszero_edge |> SIMP_RULE (srw_ss()) []) >>
     simp[] >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` by
    (simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
     irule (Q.INST [`w` |-> `1w`] zero_check_iszero_edge |> SIMP_RULE (srw_ss()) []) >>
     simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`, update_var_def,
          eval_operand_def, lookup_var_def, op_taint_def, op_prov_def,
          FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
     qexistsl_tac [`id+1`,`Var z`] >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G2 tn2
     (Abort Revert_abort (revert_state (set_returndata [] s2)))` by
    (irule slice_assert_abort_counted >>
     simp[Abbr `s2`, Abbr `s1`, Abbr `tn2`, Abbr `tn1`, update_var_def,
       op_taint_def, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qexistsl_tac [`s1`,`s2`] >> simp[] >>
  `gas_path_ptr D 0 ctx fn PG G tn s (0+0+0) G2 tn2
     (Abort Revert_abort (revert_state (set_returndata [] s2)))` by
    (irule (cj 2 gas_path_ptr_rules) >>
     qexistsl_tac [`G1`,`s1`,`tn1`] >> simp[] >>
     irule (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL (cj 2 gas_path_ptr_rules)) |> SIMP_RULE (srw_ss()) []) >>
     qexistsl_tac [`G2`,`s2`,`tn2`] >> simp[]) >>
  gvs[Abbr `G2`, Abbr `tn2`, Abbr `G1`, Abbr `tn1`]
QED

Theorem zero_check_emit_layout:
  emit_op ISZERO [y] sa = (Var z,sb) /\
  emit_op ISZERO [Var z] sb = (Var nz,sc) /\
  emit_void ASSERT [Var nz] sc = ((),sd) /\ fn_has_code sa sd fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ISZERO [y] [z]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id+1) ISZERO [Var z] [nz]) /\
    get_instruction bb (SUC (SUC (LENGTH sa.cs_current_insts))) =
      SOME (mk_inst (sa.cs_next_id+2) ASSERT [Var nz] [])
Proof
  strip_tac >>
  `sd.cs_current_bb = sa.cs_current_bb /\
   sd.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ISZERO [y] [z];
     mk_inst (sa.cs_next_id+1) ISZERO [Var z] [nz];
     mk_inst (sa.cs_next_id+2) ASSERT [Var nz] []]` by
    (fs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_assum (qspec_then `1` mp_tac) >>
  first_x_assum (qspec_then `2` mp_tac) >> simp[ADD1]
QED

Theorem zero_check_emit_abort_counted:
  emit_op ISZERO [y] sa = (Var z,sb) /\
  emit_op ISZERO [Var z] sb = (Var nz,sc) /\
  emit_void ASSERT [Var nz] sc = ((),sd) /\ fn_has_code sa sd fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand y s = SOME 0w /\ op_taint tn y = {} /\ op_prov G y = NONE ==>
  ?s1 s2.
    s1 = (update_var z 1w s) with vs_inst_idx := SUC s.vs_inst_idx /\
    s2 = (update_var nz 0w s1) with vs_inst_idx := SUC s1.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (DRESTRICT (DRESTRICT G (COMPL {z})) (COMPL {nz}))
      ((tn with t_var := tn.t_var |+ (z,{})) with
        t_var := (tn.t_var |+ (z,{})) |+ (nz,{}))
      (Abort Revert_abort (revert_state (set_returndata [] s2)))
Proof
  strip_tac >> drule_all zero_check_emit_layout >> strip_tac >>
  irule zero_check_abort_counted >> metis_tac[]
QED
