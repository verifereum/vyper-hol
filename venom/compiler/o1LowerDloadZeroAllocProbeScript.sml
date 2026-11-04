(* Checked interface probe: distinct zero-size sites share source
   provenance, but an inserted scratch allocation can separate them. *)
Theory o1LowerDloadZeroAllocProbe
Ancestors
  venomExecSemantics venomState venomInst ptrDiscipline words o1PassContract unitShapeDefs pointerConfinedDefs While

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
  EVAL_TAC >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[SRULE [mk_raw_function_def, default_internal_call_abi_def]
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
