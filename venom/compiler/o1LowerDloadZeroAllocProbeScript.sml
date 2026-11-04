(* Checked interface probe: distinct zero-size sites share source
   provenance, but an inserted scratch allocation can separate them. *)
Theory o1LowerDloadZeroAllocProbe
Ancestors
  venomExecSemantics venomState venomInst ptrDiscipline words o1PassContract unitShapeDefs pointerConfinedDefs While unitTransformDefs lowerDloadDefs byte spillSim

(* Shared concrete syntax, not a new logical definition. *)
val zero_alias_fn = ``mk_raw_function "entry"
  [<| bb_label := "entry"; bb_instructions :=
    [<| inst_id := 0; inst_opcode := ALLOCA;
        inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["p"] |>;
     <| inst_id := 1; inst_opcode := DLOAD;
        inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["x"] |>;
     <| inst_id := 2; inst_opcode := ALLOCA;
        inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["q"] |>;
     <| inst_id := 3; inst_opcode := EQ;
        inst_operands := [Var "p"; Var "q"]; inst_outputs := ["e"] |>;
     <| inst_id := 4; inst_opcode := ASSERT;
        inst_operands := [Var "e"]; inst_outputs := [] |>;
     <| inst_id := 5; inst_opcode := STOP;
        inst_operands := []; inst_outputs := [] |>] |>]``;

Theorem zero_alias_no_opaque[local]:
  !x. ~copy_phi_var GAS ^zero_alias_fn x /\
      ~copy_phi_var RETPC_PARAM ^zero_alias_fn x
Proof
  gen_tac >> conj_tac >> irule copy_phi_var_no_seed >> EVAL_TAC >>
  rpt strip_tac >> gvs[]
QED

Theorem zero_alias_ctx_shape:
  o1_ctx_shape (mk_venom_context [^zero_alias_fn] (SOME "entry"))
Proof
  simp[reachable_inst_def] >> EVAL_TAC >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[reachable_inst_def, fn_insts_blocks_def, SRULE [mk_raw_function_def, default_internal_call_abi_def]
             zero_alias_no_opaque]
QED

Theorem zero_alloc_sites_alias:
  case exec_alloca
    <| inst_id := 0; inst_opcode := ALLOCA;
       inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["p"] |>
    (init_venom_state "entry") (0w:bytes32) of
  | OK s1 =>
    (case exec_alloca
      <| inst_id := 2; inst_opcode := ALLOCA;
         inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["q"] |>
      s1 (0w:bytes32) of
     | OK s2 => lookup_var "p" s2 = SOME (0w:bytes32) /\
                lookup_var "q" s2 = SOME (0w:bytes32) /\
                FLOOKUP s2.vs_allocas 0 = SOME (0,0) /\
                FLOOKUP s2.vs_allocas 2 = SOME (0,0)
     | _ => F)
  | _ => F
Proof
  EVAL_TAC >> simp[dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem scratch_separates_zero_alloc_sites:
  case exec_alloca
    <| inst_id := 0; inst_opcode := ALLOCA;
       inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["p"] |>
    (init_venom_state "entry") (0w:bytes32) of
  | OK s1 =>
    (case exec_alloca
      <| inst_id := 4; inst_opcode := ALLOCA;
         inst_operands := [Lit (32w:bytes32)]; inst_outputs := ["scratch"] |>
      s1 (32w:bytes32) of
     | OK s2 =>
       (case exec_alloca
         <| inst_id := 2; inst_opcode := ALLOCA;
            inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["q"] |>
         s2 (0w:bytes32) of
        | OK s3 => lookup_var "p" s3 = SOME (0w:bytes32) /\
                   lookup_var "q" s3 = SOME (32w:bytes32) /\
                   FLOOKUP s3.vs_allocas 0 = SOME (0,0) /\
                   FLOOKUP s3.vs_allocas 2 = SOME (32,0)
        | _ => F)
     | _ => F)
  | _ => F
Proof
  EVAL_TAC >> simp[dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem zero_alias_roots[local]:
  ptr_roots (\nm. {}) ^zero_alias_fn = {"p"; "q"}
Proof
  simp[ptr_roots_def, alloca_roots_def, fn_insts_def,
       fn_insts_blocks_def, mk_raw_function_def, inst_output_def,
       pred_setTheory.EXTENSION, DISJ_IMP_THM, FORALL_AND_THM,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem zero_alias_pv[local]:
  fn_pv (\nm. {}) ^zero_alias_fn = {"p"; "q"}
Proof
  simp[fn_pv_def, zero_alias_roots, pointer_derived_vars_def] >>
  EVAL_TAC >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[listTheory.SET_TO_LIST_INV, listTheory.MEM_SET_TO_LIST]
QED

Theorem zero_alias_fn_ptr_ok:
  fn_ptr_ok (\nm. {}) ^zero_alias_fn
Proof
  simp[fn_ptr_ok_def, zero_alias_pv, affine_pointer_ops_def,
       phi_pv_all_var_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

val zero_alias_ctx = ``mk_venom_context [^zero_alias_fn] (SOME "entry")``;
val zero_alias_unit = ``<| cu_context := ^zero_alias_ctx;
                           cu_data_segment := [] |>``;
val zero_alias_supply = ``init_ir_supply ^zero_alias_unit``;
val zero_alias_out = ``THE (execute_configured_fn_pass rpolicy
  (CFP_Simple VP_LowerDload) ^zero_alias_unit ^zero_alias_supply
  ^zero_alias_fn)``;

Theorem zero_alias_pass_step:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) ^zero_alias_unit
    ^zero_alias_supply ^zero_alias_fn ^zero_alias_out
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem zero_alias_stage:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) any_view
    ^zero_alias_ctx
    (mk_venom_context [(^zero_alias_out).fpo_function] (SOME "entry"))
Proof
  simp[ctx_pass_stage_def, mk_venom_context_def] >>
  qexistsl [`^zero_alias_unit`, `^zero_alias_supply`, `^zero_alias_out`] >>
  simp[zero_alias_pass_step, any_view_def, ctx_fn_names_def,
       mk_venom_context_def]
QED

val zero_alias_v = ``(init_venom_state "entry") with
  vs_labels := FEMPTY |+ ("code_end", (0w:bytes32))``;

Theorem zero_alias_run_state_ok:
  o1_run_state_ok ^zero_alias_v
Proof
  simp[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
       lowerDloadDefsTheory.code_layout_valid_def, init_venom_state_def] >>
  EVAL_TAC
QED

val za_i0 = ``<| inst_id := 0; inst_opcode := ALLOCA;
  inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["p"] |>``;
val za_i1 = ``<| inst_id := 1; inst_opcode := DLOAD;
  inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["x"] |>``;
val za_i2 = ``<| inst_id := 2; inst_opcode := ALLOCA;
  inst_operands := [Lit (0w:bytes32)]; inst_outputs := ["q"] |>``;
val za_i3 = ``<| inst_id := 3; inst_opcode := EQ;
  inst_operands := [Var "p"; Var "q"]; inst_outputs := ["e"] |>``;
val za_i4 = ``<| inst_id := 4; inst_opcode := ASSERT;
  inst_operands := [Var "e"]; inst_outputs := [] |>``;
val za_i5 = ``<| inst_id := 5; inst_opcode := STOP;
  inst_operands := []; inst_outputs := [] |>``;
val za_s0 = zero_alias_v;
val za_u0 = ``^za_s0 with <|
  vs_vars := FEMPTY |+ ("p", (0w:bytes32));
  vs_allocas := FEMPTY |+ (0,(0,0)) |>``;
val za_s1 = ``^za_u0 with vs_inst_idx := 1``;
val za_u1 = ``^za_s1 with vs_vars :=
  FEMPTY |+ ("p", (0w:bytes32)) |+ ("x", (0w:bytes32))``;
val za_s2 = ``^za_u1 with vs_inst_idx := 2``;
val za_u2 = ``^za_s2 with <|
  vs_vars := FEMPTY |+ ("p", (0w:bytes32)) |+ ("x", (0w:bytes32))
                    |+ ("q", (0w:bytes32));
  vs_allocas := FEMPTY |+ (0,(0,0)) |+ (2,(0,0)) |>``;
val za_s3 = ``^za_u2 with vs_inst_idx := 3``;
val za_u3 = ``^za_s3 with vs_vars :=
  FEMPTY |+ ("p", (0w:bytes32)) |+ ("x", (0w:bytes32))
         |+ ("q", (0w:bytes32)) |+ ("e", (1w:bytes32))``;
val za_s4 = ``^za_u3 with vs_inst_idx := 4``;
val za_u4 = za_s4;
val za_s5 = ``^za_u4 with vs_inst_idx := 5``;

Theorem zero_alias_step0:
  step_inst fuel ^zero_alias_ctx ^za_i0 ^za_s0 = OK ^za_u0
Proof
  EVAL_TAC >> simp[dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem zero_alias_step1:
  step_inst fuel ^zero_alias_ctx ^za_i1 ^za_s1 = OK ^za_u1
Proof
  EVAL_TAC >> simp[dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  simp[SRULE [word_of_bytes_def]
    (Q.SPECL [`be`, `a`, `[]`] word_of_bytes_append_zeros)]
QED

Theorem zero_alias_step2:
  step_inst fuel ^zero_alias_ctx ^za_i2 ^za_s2 = OK ^za_u2
Proof
  EVAL_TAC >> simp[dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem zero_alias_step3:
  step_inst fuel ^zero_alias_ctx ^za_i3 ^za_s3 = OK ^za_u3
Proof
  EVAL_TAC >> simp[dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem zero_alias_step4:
  step_inst fuel ^zero_alias_ctx ^za_i4 ^za_s4 = OK ^za_u4
Proof
  EVAL_TAC >> simp[]
QED

Theorem zero_alias_step5:
  step_inst fuel ^zero_alias_ctx ^za_i5 ^za_s5 =
    Halt (halt_state (^za_s5 with vs_returndata := []))
Proof
  EVAL_TAC
QED
