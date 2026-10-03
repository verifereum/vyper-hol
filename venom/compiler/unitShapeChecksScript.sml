(* Permanent small checks for the PLAN §5.8 syntactic hypotheses.
 * They test positions, not instruction well-formedness (a separate property).
 *)
Theory unitShapeChecks
Ancestors
  unitShapeDefs venomCompilerTypes venomInst venomState stackPlanTypes
  stackPlanGen contextCodegenRel list

Definition shape_probe_fn_def:
  shape_probe_fn insts = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions := insts |>]
End

(* ===== Entry order, parameters and reserved labels ===== *)

Theorem entry_order_checks:
  entry_fn_first (mk_venom_context
    [mk_raw_function "entry" []; mk_raw_function "callee" []] (SOME "entry")) /\
  ~entry_fn_first (mk_venom_context
    [mk_raw_function "callee" []; mk_raw_function "entry" []] (SOME "entry")) /\
  ~entry_fn_first (mk_venom_context [] (SOME "entry")) /\
  ~entry_fn_first (mk_venom_context [mk_raw_function "entry" []] NONE)
Proof
  simp[entry_fn_first_def, mk_venom_context_def, mk_raw_function_def]
QED

Theorem reserved_label_checks:
  reserved_label "revert" /\ reserved_label "code_end" /\
  reserved_label "return_label_" /\ reserved_label "return_label_17" /\
  reserved_label "reachable_" /\ reserved_label "reachable_3" /\
  ~reserved_label "reverter" /\ ~reserved_label "code_ending" /\
  ~reserved_label "return_label" /\ ~reserved_label "reachable" /\
  ~reserved_label "my_return_label_17"
Proof
  EVAL_TAC
QED

Theorem entry_parameter_checks:
  get_params [mk_inst 0 PARAM [Lit 0w] ["x"]] <> [] /\
  get_params [mk_inst 0 FMP_PARAM [Lit 0w] ["x"]] <> [] /\
  get_params [mk_inst 0 RETPC_PARAM [Lit 0w] ["x"]] <> [] /\
  get_params [mk_inst 0 STOP [] []] = [] /\
  (* The plan's get_params test is precisely a PREFIX test. *)
  get_params [mk_inst 0 NOP [] []; mk_inst 1 PARAM [Lit 0w] ["x"]] = [] /\
  ~entry_fn_no_ret (shape_probe_fn [mk_inst 0 RET [Var "pc"] []]) /\
  entry_fn_no_ret (shape_probe_fn [mk_inst 0 RETURN [Lit 0w; Lit 0w] []])
Proof
  EVAL_TAC
QED

(* ===== Exact read0 table and raw/output distinction ===== *)

Theorem read0_table_checks:
  EVERY is_read0_opcode
    [ADDRESS; BASEFEE; BLOBBASEFEE; CALLDATASIZE; CALLER; CALLVALUE;
     CHAINID; CODESIZE; COINBASE; GAS; GASLIMIT; GASPRICE; MEMTOP;
     NUMBER; ORIGIN; PREVRANDAO; RETURNDATASIZE; SELFBALANCE; TIMESTAMP] /\
  EVERY (\op. ~is_read0_opcode op)
    [BALANCE; BLOCKHASH; BLOBHASH; CALLDATALOAD; EXTCODESIZE; EXTCODEHASH;
     MLOAD; SLOAD; GETFMP; INITIAL_FMP; PARAM; RETPC_PARAM]
Proof
  EVAL_TAC
QED

Theorem read0_operand_checks:
  EVERY (\op. ~inst_shape_ok (mk_inst 0 op [Lit 0w] ["x"]))
    [ADDRESS; BASEFEE; BLOBBASEFEE; CALLDATASIZE; CALLER; CALLVALUE;
     CHAINID; CODESIZE; COINBASE; GAS; GASLIMIT; GASPRICE; MEMTOP;
     NUMBER; ORIGIN; PREVRANDAO; RETURNDATASIZE; SELFBALANCE; TIMESTAMP] /\
  EVERY (\op. inst_shape_ok (mk_inst 0 op [] ["x"]))
    [ADDRESS; BASEFEE; BLOBBASEFEE; CALLDATASIZE; CALLER; CALLVALUE;
     CHAINID; CODESIZE; COINBASE; GAS; GASLIMIT; GASPRICE; MEMTOP;
     NUMBER; ORIGIN; PREVRANDAO; RETURNDATASIZE; SELFBALANCE; TIMESTAMP]
Proof
  EVAL_TAC
QED

Theorem excluded_opcode_checks:
  EVERY (\op. ~inst_shape_ok (mk_inst 0 op [] []))
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT; DJMP; OFFSET] /\
  EVERY (\op. ~raw_opcode_ok op)
    [ASSERT_UNREACHABLE; DLOAD; DLOADBYTES; DALLOCA; DRET; GETFMP; SETFMP;
     RETFMP; INITIAL_FMP; BUMP; FMP_PARAM; MEMTOP] /\
  EVERY (\op. inst_shape_ok (mk_inst 0 op [] []))
    [ASSERT_UNREACHABLE; DLOAD; DLOADBYTES; DALLOCA; DRET; GETFMP; SETFMP;
     RETFMP; INITIAL_FMP; BUMP; FMP_PARAM; MEMTOP; RET] /\
  raw_opcode_ok RET
Proof
  EVAL_TAC
QED

(* ===== Label and opaque operand positions ===== *)

Theorem label_position_checks:
  label_positions_ok (mk_inst 0 JMP [Label "target"] []) /\
  label_positions_ok (mk_inst 0 JNZ [Var "c"; Label "t"; Label "f"] []) /\
  ~label_positions_ok (mk_inst 0 JNZ [Label "c"; Label "t"; Label "f"] []) /\
  label_positions_ok (mk_inst 0 PHI [Label "p"; Var "x"] ["y"]) /\
  label_positions_ok (mk_inst 0 INVOKE [Label "callee"; Var "arg"] []) /\
  ~label_positions_ok (mk_inst 0 INVOKE [Label "callee"; Label "arg"] []) /\
  ~label_positions_ok (mk_inst 0 RETURN [Label "b"; Lit 0w] []) /\
  ~label_positions_ok (mk_inst 0 ADD [Label "b"; Lit 0w] ["x"]) /\
  ~label_positions_ok (mk_inst 0 JMP [Label "a"; Label "b"] []) /\
  ~label_positions_ok (mk_inst 0 JNZ [Var "c"; Label "t"] [])
Proof
  EVAL_TAC
QED

Theorem gas_position_checks:
  gas_use_ok (mk_inst 0 CALL [Var "g"; Var "a"] ["r"]) "g" /\
  gas_use_ok (mk_inst 0 STATICCALL [Var "g"; Var "a"] ["r"]) "g" /\
  ~gas_use_ok (mk_inst 0 CALL [Var "a"; Var "g"] ["r"]) "g" /\
  ~gas_use_ok (mk_inst 0 CALL [Var "g"; Var "g"] ["r"]) "g" /\
  ~gas_use_ok (mk_inst 0 SSTORE [Lit 0w; Var "g"] []) "g" /\
  gas_use_ok (mk_inst 0 ASSIGN [Var "g"] ["h"]) "g" /\
  gas_use_ok (mk_inst 0 PHI [Label "p"; Var "g"] ["h"]) "g"
Proof
  simp[gas_use_ok_def, mk_inst_def]
QED

Theorem retpc_position_checks:
  retpc_use_ok (mk_inst 0 RET [Var "result"; Var "pc"] []) "pc" /\
  ~retpc_use_ok (mk_inst 0 RET [Var "pc"; Var "result"] []) "pc" /\
  ~retpc_use_ok (mk_inst 0 RET [Var "pc"; Var "pc"] []) "pc" /\
  ~retpc_use_ok (mk_inst 0 RETURN [Var "pc"; Lit 0w] []) "pc" /\
  retpc_use_ok (mk_inst 0 ASSIGN [Var "pc"] ["q"]) "pc" /\
  retpc_use_ok (mk_inst 0 PHI [Label "p"; Var "pc"] ["q"]) "pc"
Proof
  simp[retpc_use_ok_def, mk_inst_def, APPEND_EQ_CONS]
QED

(* ===== Seeded and unseeded cyclic graphs ===== *)

Definition shape_probe_cycle_def:
  shape_probe_cycle origin seeded = shape_probe_fn
    ((if seeded then [mk_inst 0 origin [] ["g"]] else []) ++
     [mk_inst 1 ASSIGN [Var "b"] ["a"];
      mk_inst 2 PHI [Label "entry"; Var "a"; Label "loop"; Var "g"] ["b"]])
End

Theorem unseeded_cycle_checks:
  (!x. ~gas_var (shape_probe_cycle GAS F) x) /\
  (!x. ~retpc_var (shape_probe_cycle RETPC_PARAM F) x)
Proof
  simp[gas_var_def, retpc_var_def] >> conj_tac >>
  irule copy_phi_var_no_seed >>
  simp[shape_probe_cycle_def, shape_probe_fn_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def] >> rw[] >> simp[]
QED

Theorem seeded_cycle_checks:
  !origin. copy_phi_var origin (shape_probe_cycle origin T) "a"
Proof
  gen_tac >> irule copy_phi_var_assign >>
  qexistsl_tac [`mk_inst 1 ASSIGN [Var "b"] ["a"]`, `"b"`] >>
  simp[shape_probe_cycle_def, shape_probe_fn_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def] >>
  irule copy_phi_var_phi >>
  qexistsl_tac [`mk_inst 2 PHI
    [Label "entry"; Var "a"; Label "loop"; Var "g"] ["b"]`, `"g"`] >>
  simp[shape_probe_cycle_def, shape_probe_fn_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def] >>
  irule copy_phi_var_seed >> qexists_tac `mk_inst 0 origin [] ["g"]` >>
  simp[shape_probe_cycle_def, shape_probe_fn_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def]
QED

Theorem seeded_opaque_cycle_checks:
  gas_var (shape_probe_cycle GAS T) "a" /\
  retpc_var (shape_probe_cycle RETPC_PARAM T) "a"
Proof
  simp[gas_var_def, retpc_var_def, seeded_cycle_checks]
QED

(* A GAS-to-storage use is rejected by the full function predicate, not just
 * by the local position check. *)
Theorem opaque_gas_misuse_check:
  ~opaque_use_ok (shape_probe_fn
    [mk_inst 0 GAS [] ["g"]; mk_inst 1 SSTORE [Lit 0w; Var "g"] []])
Proof
  strip_tac >>
  `gas_var (shape_probe_fn
    [mk_inst 0 GAS [] ["g"]; mk_inst 1 SSTORE [Lit 0w; Var "g"] []]) "g"`
    by (simp[gas_var_def] >> irule copy_phi_var_seed >>
        qexists_tac `mk_inst 0 GAS [] ["g"]` >>
        simp[shape_probe_fn_def, mk_raw_function_def, fn_insts_def,
             fn_insts_blocks_def, mk_inst_def]) >>
  `gas_use_ok (mk_inst 1 SSTORE [Lit 0w; Var "g"] []) "g"` by
    (irule opaque_use_ok_gas_use >> simp[mk_inst_def] >>
     qexists_tac `shape_probe_fn
       [mk_inst 0 GAS [] ["g"]; mk_inst 1 SSTORE [Lit 0w; Var "g"] []]` >>
     simp[shape_probe_fn_def, mk_raw_function_def, fn_insts_def,
          fn_insts_blocks_def, mk_inst_def]) >>
  fs[gas_use_ok_def, mk_inst_def]
QED

Theorem opaque_retpc_misuse_check:
  ~opaque_use_ok (shape_probe_fn
    [mk_inst 0 RETPC_PARAM [Lit 0w] ["pc"];
     mk_inst 1 RETURN [Var "pc"; Lit 0w] []])
Proof
  strip_tac >>
  `retpc_var (shape_probe_fn
    [mk_inst 0 RETPC_PARAM [Lit 0w] ["pc"];
     mk_inst 1 RETURN [Var "pc"; Lit 0w] []]) "pc"`
    by (simp[retpc_var_def] >> irule copy_phi_var_seed >>
        qexists_tac `mk_inst 0 RETPC_PARAM [Lit 0w] ["pc"]` >>
        simp[shape_probe_fn_def, mk_raw_function_def, fn_insts_def,
             fn_insts_blocks_def, mk_inst_def]) >>
  `retpc_use_ok (mk_inst 1 RETURN [Var "pc"; Lit 0w] []) "pc"` by
    (irule opaque_use_ok_retpc_use >> simp[mk_inst_def] >>
     qexists_tac `shape_probe_fn
       [mk_inst 0 RETPC_PARAM [Lit 0w] ["pc"];
        mk_inst 1 RETURN [Var "pc"; Lit 0w] []]` >>
     simp[shape_probe_fn_def, mk_raw_function_def, fn_insts_def,
          fn_insts_blocks_def, mk_inst_def]) >>
  fs[retpc_use_ok_def, mk_inst_def]
QED

Theorem opaque_gas_call_allowed_check:
  opaque_use_ok (shape_probe_fn
    [mk_inst 0 GAS [] ["g"]; mk_inst 1 ASSIGN [Var "g"] ["h"];
     mk_inst 2 CALL [Var "h"; Lit 0w] ["r"]])
Proof
  `!x. ~retpc_var (shape_probe_fn
    [mk_inst 0 GAS [] ["g"]; mk_inst 1 ASSIGN [Var "g"] ["h"];
     mk_inst 2 CALL [Var "h"; Lit 0w] ["r"]]) x` by
    (simp[retpc_var_def] >> irule copy_phi_var_no_seed >>
     simp[shape_probe_fn_def, mk_raw_function_def, fn_insts_def,
          fn_insts_blocks_def, mk_inst_def] >> rw[] >> simp[]) >>
  simp[opaque_use_ok_def, shape_probe_fn_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def, gas_use_ok_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opaque_retpc_return_allowed_check:
  opaque_use_ok (shape_probe_fn
    [mk_inst 0 RETPC_PARAM [Lit 0w] ["pc"];
     mk_inst 1 ASSIGN [Var "pc"] ["q"]; mk_inst 2 RET [Lit 1w; Var "q"] []])
Proof
  `!x. ~gas_var (shape_probe_fn
    [mk_inst 0 RETPC_PARAM [Lit 0w] ["pc"];
     mk_inst 1 ASSIGN [Var "pc"] ["q"]; mk_inst 2 RET [Lit 1w; Var "q"] []]) x` by
    (simp[gas_var_def] >> irule copy_phi_var_no_seed >>
     simp[shape_probe_fn_def, mk_raw_function_def, fn_insts_def,
          fn_insts_blocks_def, mk_inst_def] >> rw[] >> simp[]) >>
  simp[opaque_use_ok_def, shape_probe_fn_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def, retpc_use_ok_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

(* ===== Raw-only control-flow restrictions ===== *)

Theorem internal_termination_checks:
  internal_termination_ok (mk_venom_context
    [shape_probe_fn [mk_inst 0 STOP [] []]] (SOME "entry")) /\
  ~internal_termination_ok (mk_venom_context
    [shape_probe_fn []; mk_raw_function "callee"
      [<| bb_label := "callee"; bb_instructions := [mk_inst 0 STOP [] []] |>]]
    (SOME "entry")) /\
  ~internal_termination_ok (mk_venom_context
    [shape_probe_fn []; mk_raw_function "callee"
      [<| bb_label := "callee";
          bb_instructions := [mk_inst 0 RETURN [Lit 0w; Lit 0w] []] |>]]
    (SOME "entry"))
Proof
  simp[internal_termination_ok_def, shape_probe_fn_def, mk_venom_context_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def]
QED

Definition shape_probe_unit_def:
  shape_probe_unit insts =
    <| cu_context := mk_venom_context [shape_probe_fn insts] (SOME "entry");
       cu_data_segment := [] |>
End

(* These are shape hypotheses, not a replacement for ctx_wf: an empty entry
 * block is not ruled out here, and output-only forms remain admissible. *)
Theorem complete_unit_shape_checks:
  unit_shape_ok (shape_probe_unit []) /\
  o1_source_unit_ok (shape_probe_unit [mk_inst 0 STOP [] []]) /\
  unit_shape_ok (shape_probe_unit [mk_inst 0 MEMTOP [] ["x"]]) /\
  ~o1_source_unit_ok (shape_probe_unit [mk_inst 0 MEMTOP [] ["x"]]) /\
  unit_shape_ok (shape_probe_unit [mk_inst 0 ASSERT_UNREACHABLE [] []]) /\
  ~o1_source_unit_ok (shape_probe_unit [mk_inst 0 ASSERT_UNREACHABLE [] []]) /\
  ~unit_shape_ok (shape_probe_unit [mk_inst 0 RET [Lit 0w] []]) /\
  ~unit_shape_ok (shape_probe_unit [mk_inst 0 CALLER [Lit 0w] ["x"]]) /\
  ~unit_shape_ok (shape_probe_unit [mk_inst 0 PARAM [Lit 0w] ["x"]]) /\
  ~o1_source_unit_ok (shape_probe_unit [mk_inst 0 JMP [Label "entry"] []])
Proof
  simp[unit_shape_ok_def, o1_source_unit_ok_def, shape_probe_unit_def,
       entry_fn_first_def, fn_shape_ok_def, shape_probe_fn_def,
       mk_venom_context_def, mk_raw_function_def, fn_entry_label_def,
       entry_block_def, opaque_use_ok_def, fn_insts_def, fn_insts_blocks_def,
       entry_fn_no_ret_def, get_params_def, inst_shape_ok_def,
       is_read0_opcode_def, label_positions_ok_def, is_label_operand_def,
       reserved_label_def, raw_opcode_ok_def, internal_termination_ok_def,
       first_block_no_preds_def, bb_succs_def, get_successors_def, get_label_def,
       is_terminator_def, is_param_opcode_def, mk_inst_def] >> EVAL_TAC
QED

(* Output shape permits hidden parameters and internal RET; the raw-only
 * FMP_PARAM exclusion must not leak into the output shape. *)
Theorem internal_output_shape_check:
  unit_shape_ok
    <| cu_context := mk_venom_context
         [shape_probe_fn [mk_inst 0 STOP [] []];
          mk_raw_function "callee"
            [<| bb_label := "callee";
                bb_instructions := [mk_inst 1 FMP_PARAM [Lit 0w] ["fmp"];
                                    mk_inst 2 RET [Lit 0w] []] |>]]
         (SOME "entry");
       cu_data_segment := [] |>
Proof
  simp[unit_shape_ok_def, entry_fn_first_def, fn_shape_ok_def,
       shape_probe_fn_def, mk_venom_context_def, mk_raw_function_def,
       fn_entry_label_def, entry_block_def, opaque_use_ok_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM,
       fn_insts_def, fn_insts_blocks_def, entry_fn_no_ret_def,
       get_params_def, inst_shape_ok_def, is_read0_opcode_def,
       label_positions_ok_def, is_label_operand_def, reserved_label_def,
       is_param_opcode_def, mk_inst_def] >> EVAL_TAC
QED

Theorem first_block_predecessor_checks:
  first_block_no_preds (shape_probe_fn [mk_inst 0 STOP [] []]) /\
  ~first_block_no_preds (shape_probe_fn [mk_inst 0 JMP [Label "entry"] []]) /\
  ~first_block_no_preds (mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "b"] []] |>;
     <| bb_label := "b"; bb_instructions := [mk_inst 1 JMP [Label "entry"] []] |>])
Proof
  EVAL_TAC
QED
