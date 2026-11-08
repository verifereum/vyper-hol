(* A real internal call satisfies the scalar inliner contract. *)
Theory functionInlinerCallWitness
Ancestors
  functionInlinerContract functionInlinerDefs unitShapeDefs
  callLayoutDefs venomInst venomWf venomState venomExecSemantics
  fcgDefs finite_map list relation words
Libs wordsLib

Definition inliner_witness_callee_def:
  inliner_witness_callee = mk_raw_function "add1"
    [<| bb_label := "add1";
        bb_instructions :=
          [instruction 3 PARAM [Lit 0w] ["x"];
           instruction 4 RETPC_PARAM [Lit 1w] ["pc"];
           instruction 5 ADD [Var "x"; Lit 1w] ["y"];
           instruction 6 RET [Var "y"; Var "pc"] []] |>]
End

Definition inliner_witness_caller_def:
  inliner_witness_caller = mk_raw_function "main"
    [<| bb_label := "main";
        bb_instructions :=
          [instruction 0 INVOKE [Label "add1"; Lit 41w] ["answer"];
           instruction 1 SSTORE [Lit 0w; Var "answer"] [];
           instruction 2 STOP [] []] |>]
End

Definition inliner_witness_context_def:
  inliner_witness_context = mk_venom_context
    [inliner_witness_caller; inliner_witness_callee] (SOME "main")
End

Theorem inliner_witness_reachable[local]:
  reachable_fn inliner_witness_caller = inliner_witness_caller /\
  reachable_fn inliner_witness_callee = inliner_witness_callee
Proof
  simp[reachable_fn_def, inliner_witness_caller_def,
       inliner_witness_callee_def, mk_raw_function_def, fn_reachable_def,
       fn_entry_label_def, entry_block_def, reachable_inst_def]
QED

Theorem inliner_witness_retpc[local]:
  (!x. ~retpc_var inliner_witness_caller x) /\
  (!x. retpc_var inliner_witness_callee x <=> x = "pc")
Proof
  conj_tac
  >- (simp[retpc_var_def] >> irule copy_phi_var_no_seed >>
      simp[inliner_witness_caller_def, mk_raw_function_def,
           fn_insts_def, fn_insts_blocks_def] >>
      rpt strip_tac >> gvs[]) >>
  gen_tac >> simp[retpc_var_def] >>
  once_rewrite_tac[copy_phi_var_cases] >>
  simp[inliner_witness_caller_def, inliner_witness_callee_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem inliner_witness_opaque_shape[local]:
  opaque_use_ok inliner_witness_caller /\
  opaque_use_ok inliner_witness_callee /\
  retpc_shape_ok inliner_witness_caller /\
  retpc_shape_ok inliner_witness_callee
Proof
  simp[opaque_use_ok_def, retpc_shape_ok_def, inliner_witness_reachable,
       inliner_witness_retpc] >>
  simp[inliner_witness_caller_def,
       inliner_witness_callee_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, retpc_use_ok_def] >>
  simp[GSYM IMP_DISJ_THM] >>
  rpt strip_tac >> gvs[] >> CCONTR_TAC >> gvs[]
QED

Theorem inliner_witness_callees[local]:
  !name. fcg_get_callees (fcg_analyze inliner_witness_context) name =
    if name = "main" then ["add1"] else []
Proof
  gen_tac >> EVAL_TAC >> rw[]
QED

Theorem inliner_witness_input_ok:
  inliner_input_ok inliner_witness_context
Proof
  simp[inliner_input_ok_def, inliner_witness_callees,
       inliner_witness_context_def, mk_venom_context_def,
       inliner_witness_opaque_shape, GSYM RIGHT_EXISTS_AND_THM] >>
  qexists_tac `\name. if name = "main" then 1n else 0` >>
  EVAL_TAC >> rw[] >> EVAL_TAC >> gvs[fn_insts_blocks_def]
QED

Theorem inliner_witness_call_removed:
  LENGTH (function_inliner_ctx 0 inliner_witness_context).ctx_functions = 1 /\
  EVERY (\fn. EVERY (\inst. inst.inst_opcode <> INVOKE) (fn_insts fn))
    (function_inliner_ctx 0 inliner_witness_context).ctx_functions
Proof
  EVAL_TAC
QED

Theorem inliner_witness_source_stores_42:
  case run_context 20 inliner_witness_context (init_venom_state "main") of
    Halt s => sload 0w s = 42w
  | _ => F
Proof
  EVAL_TAC
QED

Theorem inliner_witness_target_stores_42:
  case run_context 20 (function_inliner_ctx 0 inliner_witness_context)
         (init_venom_state "main") of
    Halt s => sload 0w s = 42w
  | _ => F
Proof
  EVAL_TAC
QED
