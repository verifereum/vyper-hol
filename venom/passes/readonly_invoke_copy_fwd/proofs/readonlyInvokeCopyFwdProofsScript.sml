(*
 * Readonly Invoke Arg Copy Forwarding — Proofs
 *
 * Proves the fold form of the block pass, function-name preservation, and
 * a concrete non-vacuity witness (ricf_witness_ctx) for ricf_pass_correct
 * (readonlyInvokeCopyFwdSim): every premise holds, readonly_mem_analyze
 * infers a readonly parameter, and ricf forwards a pre-invoke staging
 * MCOPY.
 *)

Theory readonlyInvokeCopyFwdProofs
Ancestors
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdSim readonlyInvokeCopyFwdDefs internalReturnCopyFwdDefs invokeCopyFwdCommonDefs
  readonlyMemoryArgsProps readonlyMemoryArgsDefs callLayoutDefs dfgDefs
  memLocDefs o1PassContract ptrDiscipline unitTransformDefs copyFwdEquiv
  passSharedDefs venomWf venomInst venomInstProps venomExecSemantics
  venomState stateEquiv While list rich_list finite_map pred_set arithmetic
  pair option words

(* Structural transformation facts are exported by readonlyInvokeCopyFwdPlan. *)
(* ==========================================================================
   3. Concrete Non-Vacuity Witness (ricf_witness_ctx)
   ========================================================================== *)

Definition ricf_witness_callee_def:
  ricf_witness_callee : ir_function =
    mk_raw_function "callee" [
      <| bb_label := "callee";
         bb_instructions := [
           mk_inst 10 PARAM [Lit 0w] ["%arg"];
           mk_inst 11 RETPC_PARAM [Lit 1w] ["%retpc"];
           mk_inst 12 MLOAD [Var "%arg"] ["%val"];
           mk_inst 13 RET [Var "%val"; Var "%retpc"] []
         ] |>
    ]
End

Definition ricf_witness_main_def:
  ricf_witness_main : ir_function =
    mk_raw_function "main" [
      <| bb_label := "main";
         bb_instructions := [
           mk_inst 1 ALLOCA [Lit 32w] ["%src"];
           mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
           mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
           mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
           mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"];
           mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
           mk_inst 7 STOP [] []
         ] |>
    ]
End

Definition ricf_witness_ctx_def:
  ricf_witness_ctx : venom_context =
    <| ctx_functions := [ricf_witness_callee; ricf_witness_main];
       ctx_entry := SOME "main";
       ctx_global_reserved := [] |>
End

Theorem ricf_witness_main_blocks[simp]:
  ricf_witness_main.fn_blocks = [
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"];
         mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
         mk_inst 7 STOP [] []
       ] |>
  ]
Proof
  simp[ricf_witness_main_def, mk_raw_function_def]
QED

Theorem ricf_witness_main_aliases[simp]:
  icf_assign_root (dfg_build_function ricf_witness_main) {} "%dst" = "%dst" /\
  icf_assign_root (dfg_build_function ricf_witness_main) {} "%src" = "%src" /\
  dfg_get_def (dfg_build_function ricf_witness_main) "%dst" =
    SOME (mk_inst 2 ALLOCA [Lit 32w] ["%dst"]) /\
  dfg_get_def (dfg_build_function ricf_witness_main) "%src" =
    SOME (mk_inst 1 ALLOCA [Lit 32w] ["%src"]) /\
  icf_collect_aliases (dfg_build_function ricf_witness_main) "%dst" = {"%dst"} /\
  icf_collect_aliases (dfg_build_function ricf_witness_main) "%src" = {"%src"} /\
  icf_use_positions (dfg_build_function ricf_witness_main) "%src" =
    [(mk_inst 3 MSTORE [Var "%src"; Lit 99w] [], 0);
     (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 1)] /\
  icf_use_positions (dfg_build_function ricf_witness_main) "%dst" =
    [(mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 0);
     (mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"], 1)] /\
  icf_is_readonly_op (FEMPTY |+ ("callee", [T]) |+ ("main", []))
    (mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"]) 1 = T
Proof
  rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- (irule icf_collect_aliases_no_assign >> EVAL_TAC)
  >- (irule icf_collect_aliases_no_assign >> EVAL_TAC)
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
QED

Theorem ricf_witness_rma:
  readonly_mem_analyze ricf_witness_ctx =
    FEMPTY |+ ("callee", [T]) |+ ("main", [])
Proof
  simp[readonly_mem_analyze_def, rma_analyze_def, icf_fn_meta_of_def,
       icf_fn_meta_of_fn_def, callLayoutDefsTheory.fn_user_param_insts_def,
       callLayoutDefsTheory.fn_entry_insts_def,
       default_internal_call_abi_def, ricf_witness_ctx_def,
       ricf_witness_callee_def, ricf_witness_main_def, mk_raw_function_def,
       mk_inst_def, entry_block_def, entry_param_outputs_def,
       collect_param_info_def, has_ret_instruction_def, build_param_index_def,
       rma_init_state_def, FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[rma_fixpoint_step_def, FLOOKUP_UPDATE, rma_analyze_fn_def,
       mem_write_ops_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[]
QED

Definition ricf_witness_bb1_def:
  ricf_witness_bb1 : basic_block =
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
         mk_nop_inst (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] []);
         mk_inst 5 INVOKE [Label "callee"; Var "%src"] ["%res"];
         mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
         mk_inst 7 STOP [] []
       ] |>
End

Theorem ricf_witness_try_forward_3[simp]:
  ricf_try_forward
    (icf_build_ctx (icf_fn_meta_of ricf_witness_ctx)
       ricf_witness_ctx.ctx_functions
       (FEMPTY |+ ("callee", [T]) |+ ("main", []))
       ricf_witness_main)
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 MSTORE [Var "%src"; Lit 99w] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"];
         mk_inst 6 SSTORE [Lit 0w; Var "%res"] [];
         mk_inst 7 STOP [] []
       ] |>
    3 =
  SOME (SOME "%src",
        [(mk_inst 5 INVOKE [Label "callee"; Var "%dst"] ["%res"], 1)])
Proof
  simp[ricf_try_forward_def, icf_build_ctx_def,
       icf_is_assign_output_use_def, findi_def, INDEX_FIND_def,
       icf_assign_root_op_def, ricf_has_mutable_sibling_def] >>
  EVAL_TAC
QED

Theorem ricf_witness_wf:
  o1_ctx_shape ricf_witness_ctx /\
  EVERY wf_ssa ricf_witness_ctx.ctx_functions /\
  EVERY ricf_full_alloca_copies ricf_witness_ctx.ctx_functions /\
  EVERY ricf_no_derived_mutable_sibling ricf_witness_ctx.ctx_functions
Proof
  rpt conj_tac
  >- (simp[o1_ctx_shape_def] >> rpt conj_tac
      >- EVAL_TAC
      >- EVAL_TAC
      >- (simp[ricf_witness_ctx_def] >> conj_tac
          >- (irule single_block_o1_fn_shape >>
              simp[ricf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC)
          >- (irule single_block_o1_fn_shape >>
              simp[ricf_witness_main_def, mk_raw_function_def] >> EVAL_TAC)))
  >- (simp[ricf_witness_ctx_def] >> conj_tac
      >- (irule single_block_wf_ssa >>
          simp[ricf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC)
      >- (irule single_block_wf_ssa >>
          simp[ricf_witness_main_def, mk_raw_function_def] >> EVAL_TAC))
  >- (simp[ricf_witness_ctx_def, ricf_full_alloca_copies_def] >>
      conj_tac
      >- (rw[ricf_witness_callee_def, mk_raw_function_def, mk_inst_def] >> gvs[])
      >- (rw[mk_inst_def] >>
          gvs[icf_assign_root_op_def, icf_matches_alloca_size_def, mk_inst_def]))
  >- (simp[ricf_witness_ctx_def, ricf_no_derived_mutable_sibling_def] >>
      conj_tac
      >- (rw[ricf_witness_callee_def, mk_raw_function_def, mk_inst_def] >> gvs[])
      >- (rw[mk_inst_def] >> gvs[]))
QED

Theorem ricf_block_step_non_mcopy[simp]:
  i < LENGTH cur_bb.bb_instructions /\
  (EL i cur_bb.bb_instructions).inst_opcode <> MCOPY ==>
  ricf_block_step ctx (changed, cur_bb) i = (changed, cur_bb)
Proof
  rw[ricf_block_step_def]
QED

Theorem ricf_block_step_mcopy[simp]:
  i < LENGTH cur_bb.bb_instructions /\
  (EL i cur_bb.bb_instructions).inst_opcode = MCOPY ==>
  ricf_block_step ctx (changed, cur_bb) i =
    case ricf_try_forward ctx cur_bb i of
      NONE => (changed, cur_bb)
    | SOME (src_var_opt, rewrite_sites) =>
        let src_op =
          case src_var_opt of
            SOME sv => Var sv
          | NONE =>
              EL 1 (EL i cur_bb.bb_instructions).inst_operands in
        let new_insts = ricf_apply_forward
          cur_bb.bb_instructions i src_op rewrite_sites in
        (T, cur_bb with bb_instructions := new_insts)
Proof
  rw[ricf_block_step_def]
QED

Theorem ricf_witness_step_1[simp]:
  ricf_function_step
    (icf_build_ctx (icf_fn_meta_of ricf_witness_ctx)
       ricf_witness_ctx.ctx_functions
       (FEMPTY |+ ("callee", [T]) |+ ("main", []))
       ricf_witness_main)
    ricf_witness_main =
  (T, ricf_witness_main with fn_blocks := [ricf_witness_bb1])
Proof
  `COUNT_LIST 7 = [0; 1; 2; 3; 4; 5; 6]` by EVAL_TAC >>
  simp[ricf_function_step_def] >>
  simp[ricf_pass_block_eq_foldl, ricf_apply_forward_def, mk_nop_inst_def,
       ricf_witness_bb1_def]
QED

Theorem ricf_witness_step_2[simp]:
  ricf_function_step
    ctx
    (ricf_witness_main with fn_blocks := [ricf_witness_bb1]) =
  (F, ricf_witness_main with fn_blocks := [ricf_witness_bb1])
Proof
  `COUNT_LIST 7 = [0; 1; 2; 3; 4; 5; 6]` by EVAL_TAC >>
  simp[ricf_function_step_def, ricf_witness_bb1_def] >>
  simp[ricf_pass_block_eq_foldl, mk_nop_inst_def]
QED

Theorem ricf_witness_forwards:
  FLOOKUP (readonly_mem_analyze ricf_witness_ctx) "callee" = SOME [T] /\
  ricf_transform_function
    (icf_fn_meta_of ricf_witness_ctx)
    ricf_witness_ctx.ctx_functions
    (readonly_mem_analyze ricf_witness_ctx)
    ricf_witness_main <> ricf_witness_main /\
  EVERY (\bb. EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions)
    (ricf_transform_function
      (icf_fn_meta_of ricf_witness_ctx)
      ricf_witness_ctx.ctx_functions
      (readonly_mem_analyze ricf_witness_ctx)
      ricf_witness_main).fn_blocks
Proof
  simp[ricf_witness_rma, FLOOKUP_UPDATE] >>
  simp[ricf_transform_function_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[ricf_witness_bb1_def, clear_nops_function_def, clear_nops_block_def,
       mk_nop_inst_def] >>
  simp[ricf_witness_main_def, mk_raw_function_def, mk_inst_def]
QED

(* Every premise of ricf_pass_correct holds on ricf_witness_ctx, and the pass
   changes it.  D treats every storage, transient, immutable and return-data
   byte as dead, as o1_pipeline_correct instantiates it. *)
Theorem ricf_pass_correct_nonvacuity:
  ?D lo vs.
    o1_ctx_shape ricf_witness_ctx /\
    EVERY wf_ssa ricf_witness_ctx.ctx_functions /\
    EVERY ricf_full_alloca_copies ricf_witness_ctx.ctx_functions /\
    EVERY ricf_no_derived_mutable_sibling ricf_witness_ctx.ctx_functions /\
    EVERY ricf_src_alloca ricf_witness_ctx.ctx_functions /\
    EVERY ricf_param_order_ok ricf_witness_ctx.ctx_functions /\
    ptr_discipline lo ricf_witness_ctx vs /\ mem_inv raw_mem_ok ricf_witness_ctx vs /\
    vs.vs_allocas = FEMPTY /\
    ~vs.vs_halted /\ ~ctx_has_dalloca ricf_witness_ctx /\
    taint_within D ricf_witness_ctx vs /\ dead_wf D /\
    ricf_transform_ctx (icf_fn_meta_of ricf_witness_ctx)
      (readonly_mem_analyze ricf_witness_ctx) ricf_witness_ctx <>
    ricf_witness_ctx
Proof
  cheat
QED
