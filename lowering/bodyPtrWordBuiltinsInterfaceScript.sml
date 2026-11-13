(* Interface probe: word values carry no provenance restriction.  The
   two-variable EQ in Abs therefore needs more than untainted operands. *)
Theory bodyPtrWordBuiltinsInterface
Ancestors
  bodyPtrDefs ptrSafeRun ptrDiscipline venomState venomInst venomInstProofs
  finite_map words compileEnv contextCodegenRel codegenRel
  builtinSimple emitHelper builtinMisc emitHelperProps fragGasPathPtr
Libs
  wordsLib

Theorem abs_word_provenance_probe:
  !fn s.
    lookup_var "arg" s = SOME (1w : bytes32) /\
    lookup_var "neg" s = SOME (-1w : bytes32) ==>
    ~access_ok 0
      (FEMPTY |+ ("arg", (0,1)) |+ ("neg", (0,1))) fn
      (mk_inst 0 EQ [Var "arg"; Var "neg"] ["test"]) s
Proof
  rpt strip_tac >>
  gvs[access_ok_def, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, eval_operand_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `w2n _ <= _` mp_tac >> EVAL_TAC
QED

Theorem abs_prefix_provenance_probe:
  !PG s.
    lookup_var "arg" s = SOME (1w : bytes32) ==>
    FLOOKUP
      (step_prov PG
        (step_prov PG (FEMPTY |+ ("arg", (0,1)))
          (mk_inst 0 SUB [Lit 0w; Var "arg"] ["%0"])
          (update_var "%0" (-1w) s))
        (mk_inst 1 SLT [Var "arg"; Lit 0w] ["%1"])
        (update_var "%1" 0w (update_var "%0" (-1w) s))) "%0" = SOME (0,1)
Proof
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
       set_prov_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem abs_eq_unsafe_probe:
  !D fuel ctx fn PG tn s.
    lookup_var "arg" s = SOME (1w : bytes32) /\
    lookup_var "neg" s = SOME (-1w : bytes32) ==>
    ~ptr_safe_step D 0 fuel ctx fn PG
      (FEMPTY |+ ("arg", (0,1)) |+ ("neg", (0,1))) tn
      (mk_inst 0 EQ [Var "arg"; Var "neg"] ["test"]) s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abs_word_provenance_probe >>
  simp[ptr_safe_step_def, ptr_inst_ok_def]
QED

Theorem abs_compiled_prefix_probe:
  !st.
    st.cs_next_var = 0 /\ st.cs_next_id = 0 /\
    st.cs_current_insts = [] ==>
    TAKE 3 (SND (compile_builtin_abs (Var "arg") st)).cs_current_insts =
      [mk_inst 0 SUB [Lit 0w; Var "arg"] ["%0"];
       mk_inst 1 SLT [Var "arg"; Lit 0w] ["%1"];
       mk_inst 2 EQ [Var "arg"; Var "%0"] ["%2"]]
Proof
  rpt strip_tac >>
  simp[compile_builtin_abs_def, compile_select_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> EVAL_TAC >> asm_rewrite_tac[] >> EVAL_TAC
QED

Theorem abs_prefix_run_probe:
  !s.
    lookup_var "arg" s = SOME (1w : bytes32) ==>
    step_inst_base (mk_inst 0 SUB [Lit 0w; Var "arg"] ["%0"]) s =
      OK (update_var "%0" (-1w) s) /\
    step_inst_base (mk_inst 1 SLT [Var "arg"; Lit 0w] ["%1"])
      (update_var "%0" (-1w) s) =
      OK (update_var "%1" 0w (update_var "%0" (-1w) s))
Proof
  rpt strip_tac
  >- (mp_tac (Q.SPECL [`Lit 0w`, `Var "arg"`, `0w`, `1w`, `0`, `"%0"`, `s`] step_SUB) >>
      simp[eval_operand_def]) >>
  mp_tac (Q.SPECL [`Var "arg"`, `Lit 0w`, `1w`, `0w`, `1`, `"%1"`,
                   `update_var "%0" (-1w) s`] step_SLT) >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> EVAL_TAC
QED

Theorem abs_reached_eq_unsafe_probe:
  !D fuel ctx fn PG tn s.
    lookup_var "arg" s = SOME (1w : bytes32) ==>
    ~ptr_safe_step D 0 fuel ctx fn PG
      (step_prov PG
        (step_prov PG (FEMPTY |+ ("arg", (0,1)))
          (mk_inst 0 SUB [Lit 0w; Var "arg"] ["%0"])
          (update_var "%0" (-1w) s))
        (mk_inst 1 SLT [Var "arg"; Lit 0w] ["%1"])
        (update_var "%1" 0w (update_var "%0" (-1w) s))) tn
      (mk_inst 2 EQ [Var "arg"; Var "%0"] ["%2"])
      (update_var "%1" 0w (update_var "%0" (-1w) s))
Proof
  rpt gen_tac >> strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def] >>
  disj1_tac >>
  gvs[access_ok_def, step_prov_def, out_prov_def, first_prov_def,
      op_prov_def, set_prov_def, mk_inst_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def,
      eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  qpat_x_assum `w2n _ <= _` mp_tac >> EVAL_TAC
QED

Theorem gas_path_ptr_unsafe_front:
  !D lo ctx fn PG G tn s n G' tn' r bb i.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    (!fuel. ~ptr_safe_step D lo fuel ctx fn PG G tn i s) /\
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    n = 0 /\ G' = G /\ tn' = tn /\ r = OK s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once gas_path_ptr_cases] >>
  simp[gas_path_ptr_edge_def] >> metis_tac[]
QED
