Theory bodyPtrBytestringBuiltinsZeroTrace
Ancestors
  bodyPtrBytestringBuiltinsCapacityProbe exprSimUint2Str ptrDiscipline ptrSafeRun gasPathPtrExec

(* Only the counters are read by the zero-block templates. *)
Definition zero_probe_compile_state_def:
  zero_probe_compile_state = ARB with
    <|cs_next_var := 1; cs_next_id := 1; cs_next_label := 0;
      cs_current_bb := "entry"; cs_blocks := [];
      cs_current_insts := [mk_inst 0 ALLOCA [Lit 128w] ["%0"]]|>
End

(* A complete finite function for the emitted layout, stopped at its exit. *)
Definition zero_probe_function_def:
  zero_probe_function = ARB with fn_blocks :=
    u2s_blocks zero_probe_compile_state (Lit 0w) (Var "%0") 78 ++
    [<|bb_label := u2s_label zero_probe_compile_state 5;
       bb_instructions := [mk_inst 31 STOP [] []]|>]
End

Theorem zero_probe_full_run:
  case run_from 10 ctx zero_probe_function
    (s with <|vs_vars := FEMPTY; vs_allocas := FEMPTY;
              vs_alloca_next := 0; vs_current_bb := "entry";
              vs_inst_idx := 0; vs_halted := F|>) of
    Halt t => eval_operand (Var "%3") t = SOME 77w /\
              FLOOKUP t.vs_allocas 0 = SOME (0,128)
  | _ => F
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem zero_probe_full_ghost:
  FLOOKUP
    (FST (ghost_run 10 ctx zero_probe_function PG FEMPTY tn
      (s with <|vs_vars := FEMPTY; vs_allocas := FEMPTY;
                vs_alloca_next := 0; vs_current_bb := "entry";
                vs_inst_idx := 0; vs_halted := F|>)))
    "%3" = SOME (0,128)
Proof
  EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_DRESTRICT,
                   finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC
QED

Theorem zero_probe_compile_allocation:
  compile_alloc_buffer 128
    (zero_probe_compile_state with
      <|cs_next_var := 0; cs_next_id := 0; cs_current_insts := []|>) =
  (<|buf_operand := Var "%0"; buf_size := 128|>, zero_probe_compile_state)
Proof
  EVAL_TAC
QED

Theorem zero_probe_compile_layout:
  compile_uint2str (Lit 0w) 78 128
    (zero_probe_compile_state with
      <|cs_next_var := 0; cs_next_id := 0; cs_current_insts := []|>) =
  (Var "%3", u2s_end zero_probe_compile_state (Lit 0w) (Var "%0") 78)
Proof
  mp_tac zero_probe_compile_allocation >>
  strip_tac >> drule compile_uint2str_layout_eq >>
  simp[u2s_var_def, zero_probe_compile_state_def,
       compileEnvTheory.fresh_var_def]
QED

Theorem ptr_run_success_unique:
  (!err. frame_run n ctx fn s <> Error err) /\
  (!err. frame_run m ctx fn s <> Error err) ==>
  frame_run n ctx fn s = frame_run m ctx fn s /\
  ghost_run n ctx fn PG G tn s = ghost_run m ctx fn PG G tn s
Proof
  strip_tac >> Cases_on `n <= m`
  >- metis_tac[frame_run_fuel_mono, ghost_run_fuel_mono_up]
  >> `m <= n` by decide_tac >>
  metis_tac[frame_run_fuel_mono, ghost_run_fuel_mono_up]
QED

Theorem zero_probe_exit_run:
  t.vs_current_bb = u2s_label zero_probe_compile_state 5 /\
  t.vs_inst_idx = 0 ==>
  run_from 0 ctx zero_probe_function t =
    Halt (t with <|vs_returndata := []; vs_halted := T|>) /\
  ghost_run 0 ctx zero_probe_function PG G tn t = (G, tn)
Proof
  strip_tac >>
  `lookup_block (u2s_label zero_probe_compile_state 5)
     zero_probe_function.fn_blocks =
     SOME <|bb_label := u2s_label zero_probe_compile_state 5;
            bb_instructions := [mk_inst 31 STOP [] []]|>` by EVAL_TAC >>
  simp[fragExecTheory.run_from_def, ghost_run_def] >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       Once ghost_block_def, venomInstTheory.get_instruction_def] >>
  EVAL_TAC >> simp[]
QED

Theorem zero_probe_path_result:
  gas_path_ptr D lo ctx zero_probe_function PG FEMPTY tn
    (s with <|vs_vars := FEMPTY; vs_allocas := FEMPTY;
              vs_alloca_next := 0; vs_current_bb := "entry";
              vs_inst_idx := 0; vs_halted := F|>) n G' tn' (OK t) /\
  t.vs_current_bb = u2s_label zero_probe_compile_state 5 /\
  t.vs_inst_idx = 0 ==>
  eval_operand (Var "%3") t = SOME 77w /\
  FLOOKUP G' "%3" = SOME (0,128)
Proof
  strip_tac >> drule gas_path_ptr_exec >>
  simp[fragExecTheory.exit_result_def] >> strip_tac >>
  drule_all zero_probe_exit_run >> strip_tac >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `run_from fuel' ctx zero_probe_function _ = _` >>
  qmatch_asmsub_abbrev_tac `run_from fuel' ctx zero_probe_function initial` >>
  `!err. frame_run fuel' ctx zero_probe_function initial <> Error err` by
    gvs[frame_run_def, block_run_def, fragExecTheory.run_from_def] >>
  `!err. frame_run 10 ctx zero_probe_function initial <> Error err` by
    (simp[Abbr `initial`, frame_run_def, block_run_def] >> EVAL_TAC >> simp[]) >>
  `frame_run fuel' ctx zero_probe_function initial =
   frame_run 10 ctx zero_probe_function initial /\
   ghost_run fuel' ctx zero_probe_function PG FEMPTY tn initial =
   ghost_run 10 ctx zero_probe_function PG FEMPTY tn initial` by
    (irule ptr_run_success_unique >> simp[]) >>
  conj_tac
  >- (`run_from 10 ctx zero_probe_function initial =
       Halt (t with <|vs_returndata := []; vs_halted := T|>)` by
        gvs[frame_run_def, block_run_def, fragExecTheory.run_from_def] >>
      `case run_from 10 ctx zero_probe_function initial of
         Halt v => eval_operand (Var "%3") v = SOME 77w /\
                   FLOOKUP v.vs_allocas 0 = SOME (0,128)
       | _ => F` by
        (mp_tac zero_probe_full_run >>
         simp[Abbr `initial`]) >>
      gvs[venomStateTheory.eval_operand_def,
          venomStateTheory.lookup_var_def]) >>
  mp_tac zero_probe_full_ghost >>
  gvs[Abbr `initial`] >> metis_tac[]
QED

Theorem zero_probe_path_buffer_failure:
  gas_path_ptr D lo ctx zero_probe_function PG FEMPTY tn
    (s with <|vs_vars := FEMPTY; vs_allocas := FEMPTY;
              vs_alloca_next := 0; vs_current_bb := "entry";
              vs_inst_idx := 0; vs_halted := F|>) n G' tn' (OK t) /\
  t.vs_current_bb = u2s_label zero_probe_compile_state 5 /\
  t.vs_inst_idx = 0 ==>
  ~ptr_buf_ok cenv
    (Builtin (BaseT (StringT 78)) (Uint2Str 78) args) (Var "%3") G' t
Proof
  strip_tac >> drule_all zero_probe_path_result >> strip_tac >>
  irule uint2str_78_interior_site_failure >>
  qexistsl_tac [`0`, `77w`] >> simp[]
QED

Theorem zero_probe_unwrap_output:
  unwrap_value cenv
    (FST (as_ptr_val (BaseT (StringT 78)) LocMemory
      (compile_uint2str (Lit 0w) 78 128
        (zero_probe_compile_state with
          <|cs_next_var := 0; cs_next_id := 0; cs_current_insts := []|>))))
    (u2s_end zero_probe_compile_state (Lit 0w) (Var "%0") 78) =
  (Var "%3", u2s_end zero_probe_compile_state (Lit 0w) (Var "%0") 78)
Proof
  simp[zero_probe_compile_layout, exprLoweringTheory.as_ptr_val_def,
       exprLoweringTheory.unwrap_value_def, contextTheory.mk_ptr_def,
       compileEnvTheory.is_word_type_def, compileEnvTheory.comp_return_def]
QED
