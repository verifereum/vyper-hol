Theory unwrapCopyProbe
Ancestors
  exprLowering venomExecSemantics venomState valueEncoding exprSim
  compileEnv vyperState vyperContext exprLoweringProps venomInst fcgDefs relation
  vyperStorage vyperLookupStorage context fragExec
Libs
  wordsLib

Theorem copy_probe_type:
  ~is_word_type (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
  type_memory_bytes cenv (ArrayT (BaseT (UintT 256)) (Fixed 1)) = 32 /\
  type_memory_size (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) = 32
Proof
  EVAL_TAC
QED

Theorem copy_probe_storage_compile:
  let sm = st with <| cs_next_var := 0; cs_next_id := 0;
                      cs_current_insts := [] |> in
  let (op,sb) = unwrap_value cenv
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Var "%0") LocStorage)) sm in
  op = Var "%0" /\
  sb.cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 32w] ["%0"];
     mk_inst 1 SLOAD [Var "%0"] ["%1"];
     mk_inst 2 MSTORE [Var "%0"; Var "%1"] []]
Proof
  EVAL_TAC
QED

Theorem copy_probe_code_compile:
  let sm = st with <| cs_next_var := 0; cs_next_id := 0;
                      cs_current_insts := [] |> in
  let (op,sb) = unwrap_value (cenv with ce_is_ctor := F)
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Var "%0") LocCode)) sm in
  op = Var "%0" /\
  sb.cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 32w] ["%0"];
     mk_inst 1 DLOAD [Var "%0"] ["%1"];
     mk_inst 2 MSTORE [Var "%0"; Var "%1"] []]
Proof
  EVAL_TAC
QED

Definition probe_start_def:
  probe_start = update_var "%0" 32w
    (sstore 32w 7w (init_venom_state "entry"))
End

Theorem copy_probe_storage_trace:
  eval_operand (Var "%0") probe_start = SOME 32w /\
  sload 32w probe_start = 7w /\
  ?s1 s2 s3.
    step_inst_base (mk_inst 0 ALLOCA [Lit 32w] ["%0"]) probe_start = OK s1 /\
    eval_operand (Var "%0") s1 = SOME 0w /\
    step_inst_base (mk_inst 1 SLOAD [Var "%0"] ["%1"]) s1 = OK s2 /\
    eval_operand (Var "%1") s2 = SOME 0w /\
    step_inst_base (mk_inst 2 MSTORE [Var "%0"; Var "%1"] []) s2 = OK s3 /\
    mload 0 s3 = 0w
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition probe_code_start_def:
  probe_code_start = (update_var "%0" 32w (init_venom_state "entry"))
    with vs_data_section := REPLICATE 63 0w ++ [7w]
End

Theorem copy_probe_code_trace:
  eval_operand (Var "%0") probe_code_start = SOME 32w /\
  step_inst_base (mk_inst 1 DLOAD [Var "%0"] ["%1"]) probe_code_start =
    OK (update_var "%1" 7w probe_code_start) /\
  ?s1 s2 s3.
    step_inst_base (mk_inst 0 ALLOCA [Lit 32w] ["%0"]) probe_code_start = OK s1 /\
    eval_operand (Var "%0") s1 = SOME 0w /\
    step_inst_base (mk_inst 1 DLOAD [Var "%0"] ["%1"]) s1 = OK s2 /\
    eval_operand (Var "%1") s2 = SOME 0w /\
    step_inst_base (mk_inst 2 MSTORE [Var "%0"; Var "%1"] []) s2 = OK s3 /\
    mload 0 s3 = 0w
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition probe_env_def:
  probe_env ce = ce with <| ce_vars := FEMPTY; ce_module_vars := FEMPTY;
                           ce_is_ctor := F; ce_imm_alloca := NONE |>
End

Definition probe_source_def:
  probe_source = empty_state with <| accounts := probe_start.vs_accounts;
                                     outcomes := SOME [] |>
End

Theorem copy_probe_state_rel:
  state_rel func (probe_env ce) empty_evaluation_context probe_source probe_start
Proof
  EVAL_TAC >> simp[]
QED

Definition probe_insts_def:
  probe_insts = [mk_inst 0 ALLOCA [Lit 32w] ["%0"];
                 mk_inst 1 SLOAD [Var "%0"] ["%1"];
                 mk_inst 2 MSTORE [Var "%0"; Var "%1"] []]
End

Definition probe_func_def:
  probe_func = mk_raw_function "probe"
    [<| bb_label := "entry";
        bb_instructions := probe_insts ++ [mk_inst 3 STOP [] []] |>]
End

Definition probe_ctx_def:
  probe_ctx = mk_venom_context [probe_func] (SOME "probe")
End

Theorem copy_probe_no_calls:
  fn_directly_calls probe_ctx = (\x y. F)
Proof
  simp[FUN_EQ_THM, fn_directly_calls_def] >>
  rpt gen_tac >> EVAL_TAC >> Cases_on `x = "probe"` >> gvs[] >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem copy_probe_stmt_state_rel:
  stmt_state_rel probe_ctx probe_func (probe_env ce)
    empty_evaluation_context probe_source probe_start
Proof
  simp[stmt_state_rel_def, copy_probe_state_rel, immutable_alloca_sep_def,
       probe_env_def, alloca_room_def, copy_probe_no_calls,
       Once TC_CASES1] >> EVAL_TAC >> simp[Once TC_CASES1] >>
  simp[Once TC_CASES1]
QED

Definition probe_value_def:
  probe_value = ArrayV (SArrayV [(0, IntV 7)])
End

Theorem copy_probe_storage_holds:
  storage_holds empty_evaluation_context F
    (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Value probe_value) 32w probe_source
Proof
  EVAL_TAC >> simp[decode_value_def, slots_in_range_def] >> EVAL_TAC >> simp[]
QED

Definition probe_sm_def:
  probe_sm = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
                cs_current_bb := "entry"; cs_current_insts := [];
                cs_blocks := []; cs_data_sections := [] |>
End

Theorem copy_probe_vv_post:
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 1) ==>
  vv_post probe_ctx probe_func (probe_env ce) empty_evaluation_context e
    probe_source probe_sm probe_sm probe_start probe_source (Value probe_value)
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Var "%0") LocStorage)) probe_start
Proof
  strip_tac >>
  simp[vv_post_def, copy_probe_stmt_state_rel, vv_holds_def, mk_ptr_def,
       vv_at_def] >>
  `eval_operand (Var "%0") probe_start = SOME 32w` by EVAL_TAC >>
  simp[copy_probe_storage_holds] >> EVAL_TAC >> simp[]
QED

Theorem copy_probe_run_memory:
  run_from fuel probe_ctx probe_func probe_start = Halt s ==>
  mload 0 s = 0w
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Definition probe_final_def:
  probe_final = (mstore 0 0w (update_var "%1" 0w (update_var "%0" 0w
    (probe_start with <| vs_allocas := FEMPTY |+ (0,(0,32));
                         vs_alloca_next := 32 |>)))) with vs_inst_idx := 3
End

Theorem copy_probe_run:
  run_from fuel probe_ctx probe_func probe_start = Halt (halt_state probe_final)
Proof
  EVAL_TAC
QED

Theorem copy_probe_continuation:
  s.vs_current_bb = "entry" /\ s.vs_inst_idx = 3 ==>
  run_from 0 probe_ctx probe_func s =
    Halt (halt_state (s with vs_returndata := []))
Proof
  strip_tac >> irule run_from_halt >>
  qexistsl_tac [`<| bb_label := "entry"; bb_instructions :=
                    probe_insts ++ [mk_inst 3 STOP [] []] |>`,
                 `mk_inst 3 STOP [] []`] >>
  simp[probe_func_def, mk_raw_function_def, lookup_block_def,
       get_instruction_def, probe_insts_def, mk_inst_def] >>
  EVAL_TAC
QED

Theorem copy_probe_bad_value:
  ~expr_val_rel empty_evaluation_context
    (ArrayT (BaseT (UintT 256)) (Fixed 1)) probe_value (Var "%0")
    (halt_state probe_final)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem copy_probe_value_halt:
  expr_val_rel cx t v op (halt_state (s with vs_returndata := [])) =
  expr_val_rel cx t v op s
Proof
  Cases_on `op` >>
  simp[expr_val_rel_def, halt_state_def, eval_operand_def, lookup_var_def]
QED

Definition probe_sb_def:
  probe_sb = SND (unwrap_value (probe_env ARB)
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Var "%0") LocStorage)) probe_sm)
End

Theorem copy_probe_sb_fields:
  probe_sb.cs_current_bb = "entry" /\
  probe_sb.cs_current_insts = probe_insts /\
  probe_sb.cs_next_id = 3 /\ probe_sb.cs_blocks = []
Proof
  EVAL_TAC
QED

Theorem copy_probe_has_code:
  fn_has_code probe_sm probe_sb probe_func
Proof
  simp[fn_has_code_def, emitted_blocks_def, copy_probe_sb_fields,
       probe_sm_def, probe_func_def, mk_raw_function_def,
       lookup_block_def] >> EVAL_TAC >> simp[]
QED

Theorem copy_probe_not_frag:
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 1) ==>
  ~frag_exec probe_ctx probe_sm probe_sb
    (\s. vv_post probe_ctx probe_func (probe_env ce) empty_evaluation_context e
       probe_source probe_sm probe_sm probe_start probe_source (Value probe_value)
       (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
         (mk_ptr (Var "%0") LocStorage)) s)
    (\s. expr_post probe_ctx probe_func (probe_env ce) empty_evaluation_context e
       probe_source probe_sm probe_sb probe_start probe_source probe_value (Var "%0") s)
    (\r. F)
Proof
  strip_tac >> simp[frag_exec_def] >>
  qexistsl_tac [`probe_func`, `probe_start`] >>
  simp[copy_probe_has_code, copy_probe_vv_post] >>
  `~probe_start.vs_halted /\ probe_start.vs_current_bb = probe_sm.cs_current_bb /\
   probe_start.vs_inst_idx = LENGTH probe_sm.cs_current_insts` by EVAL_TAC >>
  simp[copy_probe_sb_fields, probe_insts_def] >>
  qx_gen_tac `s'` >> rpt disch_tac >>
  Cases_on `expr_val_rel empty_evaluation_context (expr_type e)
              probe_value (Var "%0") s'`
  >- (disj2_tac >> disj2_tac >> qexists_tac `0` >>
      simp[copy_probe_continuation, copy_probe_run] >>
      metis_tac[copy_probe_bad_value, copy_probe_value_halt]) >>
  disj1_tac >> simp[expr_post_def]
QED

Theorem copy_probe_storage_antecedent:
  unwrap_value (probe_env ce)
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 1))
      (mk_ptr (Var "%0") LocStorage)) probe_sm = (Var "%0", probe_sb) /\
  ((mk_ptr (Var "%0") LocStorage).ptr_location = LocStorage \/
   (mk_ptr (Var "%0") LocStorage).ptr_location = LocTransient) /\
  ~is_word_type (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
  local_ptrs_reserved (probe_env ce) probe_sm /\
  probe_sm.cs_next_var <= probe_sm.cs_next_var /\
  probe_sm.cs_next_id <= probe_sm.cs_next_id /\
  fn_has_code probe_sm probe_sb probe_func /\ fn_inst_ids_distinct probe_func /\
  (!tvt. evaluate_type (get_tenv empty_evaluation_context)
            (ArrayT (BaseT (UintT 256)) (Fixed 1)) = SOME tvt ==>
     type_memory_bytes (probe_env ce) (ArrayT (BaseT (UintT 256)) (Fixed 1)) =
       type_memory_size tvt /\ type_memory_size tvt < 2 ** 64)
Proof
  simp[copy_probe_has_code] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

(* A checked counterexample to the frozen storage obligation, not an
   application of that (still cheated) theorem. *)
Theorem unwrap_storage_copy_counterexample:
  ?ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    ~frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  qexistsl_tac [`probe_ctx`, `probe_func`, `probe_env ARB`,
    `empty_evaluation_context`,
    `Name (ArrayT (BaseT (UintT 256)) (Fixed 1)) "probe"`,
    `probe_source`, `probe_sm`, `probe_sm`, `probe_sb`, `probe_start`,
    `probe_source`, `probe_value`, `ArrayT (BaseT (UintT 256)) (Fixed 1)`,
    `mk_ptr (Var "%0") LocStorage`, `Var "%0"`, `\r. F`] >>
  simp[copy_probe_storage_antecedent] >>
  irule copy_probe_not_frag >> EVAL_TAC
QED
