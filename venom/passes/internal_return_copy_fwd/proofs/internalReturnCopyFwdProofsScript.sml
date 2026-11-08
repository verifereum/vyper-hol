(*
 * Internal Return Copy Forwarding — Proofs
 *
 * Proves structural compatibility, wf_function preservation, context-level
 * simulation (ircf_pass_correct) under ptr_discipline and rma_sound, and a
 * concrete non-vacuity witness (ircf_witness_ctx) where ircf forwards a
 * post-invoke return-buffer MCOPY and eliminates the copy instruction.
 *)

Theory internalReturnCopyFwdProofs
Ancestors
  internalReturnCopyFwdDefs invokeCopyFwdCommonDefs readonlyMemoryArgsProps
  readonlyMemoryArgsDefs callLayoutDefs memLocDefs o1PassContract
  ptrDiscipline unitTransformDefs copyFwdEquiv passSharedDefs venomWf
  venomInst venomInstProps venomExecSemantics venomState stateEquiv While
  list rich_list finite_map pred_set arithmetic pair option words

(* ==========================================================================
   1. Instruction and Block Compatibility of ircf_try_forward
   ========================================================================== *)

Theorem get_label_replace_set:
  !replace_set src_root op.
    get_label
      (case op of
         Var v => if v IN replace_set then Var src_root else op
       | _ => op) =
    get_label op
Proof
  ntac 2 gen_tac >> Cases >> rw[get_label_def]
QED

Theorem icf_inst_cfg_compat_replace_set:
  !replace_set src_root inst.
    icf_inst_cfg_compat inst
      (inst with inst_operands :=
        MAP (\op.
          case op of
            Var v => if v IN replace_set then Var src_root else op
          | _ => op)
          inst.inst_operands)
Proof
  rw[icf_inst_cfg_compat_def, icf_inst_compat_def, MAP_MAP_o,
     combinTheory.o_DEF] >>
  irule LIST_EQ >> simp[EL_MAP, get_label_replace_set]
QED

Theorem FILTER_sing_MEM[local]:
  !P l x. FILTER P l = [x] ==> MEM x l /\ P x
Proof
  rpt gen_tac >> strip_tac >>
  `MEM x (FILTER P l)` by simp[] >>
  fs[MEM_FILTER]
QED

Theorem ircf_is_ret_buf_source_auth:
  !ctx bb_insts src_root cid cidx.
    ircf_is_ret_buf_source ctx bb_insts src_root cid cidx ==>
    icf_auth_ok ctx.icf_fn_meta ctx.icf_functions ctx.icf_rma
Proof
  simp[ircf_is_ret_buf_source_def] >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `LENGTH inv_sites = 1` >>
  Cases_on `inv_sites` >> simp[] >>
  Cases_on `t` >> simp[] >>
  PairCases_on `h` >> simp[] >>
  Cases_on `findi (\el. el.inst_id = h1.inst_id) bb_insts` >> simp[] >>
  strip_tac >> gvs[] >>
  drule FILTER_sing_MEM >> strip_tac >>
  gvs[icf_auth_ok_def] >> metis_tac[]
QED

Theorem ircf_try_forward_cfg_compat:
  !ctx bb copy_idx new_insts.
    ircf_try_forward ctx bb copy_idx = SOME new_insts ==>
    copy_idx < LENGTH bb.bb_instructions /\
    (EL copy_idx bb.bb_instructions).inst_opcode = MCOPY /\
    (EL copy_idx new_insts).inst_opcode = NOP /\
    icf_auth_ok ctx.icf_fn_meta ctx.icf_functions ctx.icf_rma /\
    LIST_REL icf_inst_cfg_compat bb.bb_instructions new_insts
Proof
  simp[ircf_try_forward_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule ircf_is_ret_buf_source_auth >> strip_tac >>
  simp[LIST_REL_EL_EQN] >>
  rpt strip_tac >>
  rw[icf_inst_cfg_compat_mk_nop, icf_inst_cfg_compat_replace_set]
QED

(* ==========================================================================
   2. Block and Function Transformation Compatibility and wf Preservation
   ========================================================================== *)

Definition ircf_block_step_def:
  ircf_block_step (ctx : icf_ctx) (changed : bool, cur_bb : basic_block)
                  (i : num) =
    if i >= LENGTH cur_bb.bb_instructions then (changed, cur_bb)
    else
      let inst = EL i cur_bb.bb_instructions in
      if inst.inst_opcode <> MCOPY then (changed, cur_bb)
      else
        case ircf_try_forward ctx cur_bb i of
          NONE => (changed, cur_bb)
        | SOME new_insts =>
            (T, cur_bb with bb_instructions := new_insts)
End

Theorem ircf_block_step_cfg_compat:
  !ctx bb c0 cur_bb i c1 next_bb.
    cur_bb.bb_label = bb.bb_label /\
    LIST_REL icf_inst_cfg_compat bb.bb_instructions cur_bb.bb_instructions /\
    ircf_block_step ctx (c0, cur_bb) i = (c1, next_bb) ==>
    next_bb.bb_label = bb.bb_label /\
    LIST_REL icf_inst_cfg_compat bb.bb_instructions next_bb.bb_instructions
Proof
  rw[ircf_block_step_def] >> gvs[AllCaseEqs()] >>
  drule ircf_try_forward_cfg_compat >> strip_tac >>
  metis_tac[LIST_REL_icf_inst_cfg_compat_trans]
QED

Theorem FOLDL_ircf_block_step_cfg_compat:
  !idxs ctx bb c0 cur_bb.
    cur_bb.bb_label = bb.bb_label /\
    LIST_REL icf_inst_cfg_compat bb.bb_instructions cur_bb.bb_instructions ==>
    (SND (FOLDL (ircf_block_step ctx) (c0, cur_bb) idxs)).bb_label =
      bb.bb_label /\
    LIST_REL icf_inst_cfg_compat bb.bb_instructions
      (SND (FOLDL (ircf_block_step ctx) (c0, cur_bb) idxs)).bb_instructions
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `ircf_block_step ctx (c0, cur_bb) h` >>
  drule_all ircf_block_step_cfg_compat >> strip_tac >>
  first_x_assum (qspecl_then [`ctx`, `bb`, `q`, `r`] mp_tac) >>
  simp[]
QED

Theorem ircf_block_step_compat:
  !fn_meta ctx_fns rma fn bb c0 cur_bb i c1 next_bb.
    wf_ssa fn /\
    ircf_no_dst_write_alias fn /\
    icf_block_compat fn_meta ctx_fns rma fn bb cur_bb /\
    ircf_block_step (icf_build_ctx fn_meta ctx_fns rma fn)
      (c0, cur_bb) i = (c1, next_bb) ==>
    icf_block_compat fn_meta ctx_fns rma fn bb next_bb
Proof
  rw[ircf_block_step_def] >> gvs[AllCaseEqs()] >>
  drule ircf_try_forward_cfg_compat >> strip_tac >>
  `LIST_REL icf_inst_compat cur_bb.bb_instructions new_insts` by
    (irule LIST_REL_icf_inst_cfg_imp_compat >> simp[]) >>
  `icf_mcopy_noped cur_bb (cur_bb with bb_instructions := new_insts)` by
    (irule icf_mcopy_noped_step >> simp[] >>
     qexistsl_tac [`cur_bb`, `i`] >> gvs[]) >>
  `icf_fwd_step fn_meta ctx_fns rma fn cur_bb i
     (cur_bb with bb_instructions := new_insts)` by
    (simp[icf_fwd_step_def] >> disj1_tac >> simp[]) >>
  `icf_auth_ok fn_meta ctx_fns rma` by fs[icf_build_ctx_def] >>
  metis_tac[icf_block_compat_step]
QED

Theorem FOLDL_ircf_block_step_compat:
  !idxs fn_meta ctx_fns rma fn bb c0 cur_bb.
    wf_ssa fn /\
    ircf_no_dst_write_alias fn /\
    icf_block_compat fn_meta ctx_fns rma fn bb cur_bb ==>
    icf_block_compat fn_meta ctx_fns rma fn bb
      (SND (FOLDL (ircf_block_step (icf_build_ctx fn_meta ctx_fns rma fn))
              (c0, cur_bb) idxs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `ircf_block_step (icf_build_ctx fn_meta ctx_fns rma fn)
              (c0, cur_bb) h` >>
  drule_all ircf_block_step_compat >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem ircf_transform_block_eq_foldl:
  !ctx bb.
    ircf_transform_block ctx bb =
    FOLDL (ircf_block_step ctx) (F, bb)
      (COUNT_LIST (LENGTH bb.bb_instructions))
Proof
  rw[ircf_transform_block_def, ircf_block_step_def] >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD, ircf_block_step_def]
QED

Theorem ircf_transform_block_cfg_compat:
  !ctx bb changed new_bb.
    ircf_transform_block ctx bb = (changed, new_bb) ==>
    new_bb.bb_label = bb.bb_label /\
    LIST_REL icf_inst_cfg_compat bb.bb_instructions new_bb.bb_instructions
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`COUNT_LIST (LENGTH bb.bb_instructions)`,
                   `ctx`, `bb`, `F`, `bb`]
          FOLDL_ircf_block_step_cfg_compat) >>
  simp[GSYM ircf_transform_block_eq_foldl]
QED

Theorem ircf_transform_block_compat:
  !fn_meta ctx_fns rma fn bb changed new_bb.
    wf_ssa fn /\
    ircf_no_dst_write_alias fn /\
    ircf_transform_block (icf_build_ctx fn_meta ctx_fns rma fn) bb =
      (changed, new_bb) ==>
    icf_block_compat fn_meta ctx_fns rma fn bb new_bb
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`COUNT_LIST (LENGTH bb.bb_instructions)`,
                   `fn_meta`, `ctx_fns`, `rma`, `fn`, `bb`, `F`, `bb`]
          FOLDL_ircf_block_step_compat) >>
  simp[GSYM ircf_transform_block_eq_foldl]
QED

Theorem ircf_transform_blocks_preserves_wf:
  !ctx fn.
    wf_function fn ==>
    wf_function
      (fn with fn_blocks :=
        MAP (\bb. SND (ircf_transform_block ctx bb)) fn.fn_blocks)
Proof
  rpt strip_tac >>
  `!bb. bb_well_formed (SND (ircf_transform_block ctx bb)) <=>
        bb_well_formed bb` by
    (gen_tac >> Cases_on `ircf_transform_block ctx bb` >>
     drule ircf_transform_block_cfg_compat >> strip_tac >>
     drule_all LIST_REL_icf_inst_cfg_compat_bb_wf_succs >> simp[]) >>
  `!bb. bb_succs (SND (ircf_transform_block ctx bb)) = bb_succs bb` by
    (gen_tac >> Cases_on `ircf_transform_block ctx bb` >>
     drule ircf_transform_block_cfg_compat >> strip_tac >>
     drule_all LIST_REL_icf_inst_cfg_compat_bb_wf_succs >> simp[]) >>
  `!bb. (SND (ircf_transform_block ctx bb)).bb_label = bb.bb_label` by
    (gen_tac >> Cases_on `ircf_transform_block ctx bb` >>
     drule ircf_transform_block_cfg_compat >> simp[]) >>
  `!bb. MAP (\i. i.inst_id)
          (SND (ircf_transform_block ctx bb)).bb_instructions =
        MAP (\i. i.inst_id) bb.bb_instructions` by
    (gen_tac >> Cases_on `ircf_transform_block ctx bb` >>
     drule ircf_transform_block_cfg_compat >> strip_tac >>
     drule_all LIST_REL_icf_inst_cfg_compat_bb_wf_succs >> simp[]) >>
  fs[wf_function_def, fn_labels_def, fn_has_entry_def, fn_succs_closed_def,
     fn_inst_ids_distinct_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP,
     PULL_EXISTS] >>
  metis_tac[]
QED

Theorem ircf_transform_function_fn_compat:
  !fn_meta ctx_fns rma fn.
    wf_ssa fn /\
    ircf_no_dst_write_alias fn ==>
    icf_fn_compat fn_meta ctx_fns rma fn
      (ircf_transform_function fn_meta ctx_fns rma fn)
Proof
  rpt strip_tac >>
  simp[ircf_transform_function_def] >>
  qabbrev_tac `ctx = icf_build_ctx fn_meta ctx_fns rma fn` >>
  pairarg_tac >> gvs[] >>
  `new_blocks = MAP (\bb. SND (ircf_transform_block ctx bb)) fn.fn_blocks` by
    (mp_tac (Q.SPECL [`ircf_transform_block ctx`, `fn.fn_blocks`, `F`, `[]`]
               FOLDL_block_pass_SND) >>
     simp[]) >>
  gvs[] >>
  simp[icf_fn_compat_def] >> disj2_tac >>
  qexists_tac `MAP (\bb. SND (ircf_transform_block ctx bb)) fn.fn_blocks` >>
  conj_tac
  >- (rw[LIST_REL_EL_EQN, EL_MAP] >>
      Cases_on `ircf_transform_block ctx (EL n fn.fn_blocks)` >>
      qunabbrev_tac `ctx` >>
      drule_all ircf_transform_block_compat >> simp[])
  >- rw[]
QED

(* ==========================================================================
   3. Context-Level Transformation and Correctness (ircf_pass_correct)
   ========================================================================== *)

Definition ircf_transform_ctx_def:
  ircf_transform_ctx (fn_meta : (string, invoke_fn_meta) fmap)
                     (rma : (string, bool list) fmap)
                     (ctx : venom_context) : venom_context =
    ctx with ctx_functions :=
      MAP (ircf_transform_function fn_meta ctx.ctx_functions rma)
          ctx.ctx_functions
End

Theorem ircf_transform_ctx_entry[simp]:
  !ctx fn_meta rma.
    (ircf_transform_ctx fn_meta rma ctx).ctx_entry = ctx.ctx_entry
Proof
  simp[ircf_transform_ctx_def]
QED

Theorem ircf_transform_ctx_fn_compat:
  !ctx fn_meta rma.
    EVERY wf_ssa ctx.ctx_functions /\
    EVERY ircf_no_dst_write_alias ctx.ctx_functions ==>
    LIST_REL (icf_fn_compat fn_meta ctx.ctx_functions rma)
      ctx.ctx_functions
      (ircf_transform_ctx fn_meta rma ctx).ctx_functions
Proof
  rw[ircf_transform_ctx_def, LIST_REL_EL_EQN, EL_MAP] >>
  irule ircf_transform_function_fn_compat >>
  fs[EVERY_EL]
QED

Theorem ircf_pass_correct:
  !D lo ctx fn_meta rma vs.
    o1_ctx_shape ctx /\
    EVERY wf_ssa ctx.ctx_functions /\
    EVERY ircf_no_dst_write_alias ctx.ctx_functions /\
    ptr_discipline lo ctx vs /\
    fn_meta = icf_fn_meta_of ctx /\
    rma = readonly_mem_analyze ctx /\
    rma_sound ctx rma ==>
    ctx_sim D ctx (ircf_transform_ctx fn_meta rma ctx) vs vs
Proof
  rpt strip_tac >>
  irule icf_ctx_sim_from_fn_compat >> simp[] >>
  qexistsl_tac [`lo`, `fn_meta`, `rma`] >>
  simp[ircf_transform_ctx_fn_compat]
QED

(* ==========================================================================
   4. Concrete Non-Vacuity Witness (ircf_witness_ctx)
   ========================================================================== *)

Definition ircf_witness_callee_def:
  ircf_witness_callee : ir_function =
    (mk_raw_function "callee" [
      <| bb_label := "callee";
         bb_instructions := [
           mk_inst 10 PARAM [Lit 0w] ["%buf"];
           mk_inst 11 RETPC_PARAM [Lit 1w] ["%retpc"];
           mk_inst 12 MSTORE [Var "%buf"; Lit 42w] [];
           mk_inst 13 RET [Var "%retpc"] []
         ] |>
    ]) with fn_call_abi :=
      <| ica_has_memory_return_buffer := SOME T;
         ica_user_return_count := SOME 0 |>
End

Definition ircf_witness_main_def:
  ircf_witness_main : ir_function =
    mk_raw_function "main" [
      <| bb_label := "main";
         bb_instructions := [
           mk_inst 1 ALLOCA [Lit 32w] ["%src"];
           mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
           mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
           mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
           mk_inst 5 MLOAD [Var "%dst"] ["%x"];
           mk_inst 6 SSTORE [Lit 0w; Var "%x"] [];
           mk_inst 7 STOP [] []
         ] |>
    ]
End

Definition ircf_witness_ctx_def:
  ircf_witness_ctx : venom_context =
    <| ctx_functions := [ircf_witness_callee; ircf_witness_main];
       ctx_entry := SOME "main";
       ctx_global_reserved := [] |>
End

Theorem ircf_witness_main_blocks[simp]:
  ircf_witness_main.fn_blocks = [
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 MLOAD [Var "%dst"] ["%x"];
         mk_inst 6 SSTORE [Lit 0w; Var "%x"] [];
         mk_inst 7 STOP [] []
       ] |>
  ]
Proof
  simp[ircf_witness_main_def, mk_raw_function_def]
QED

Theorem ircf_witness_main_aliases[simp]:
  icf_assign_root (dfg_build_function ircf_witness_main) {} "%dst" = "%dst" /\
  icf_assign_root (dfg_build_function ircf_witness_main) {} "%src" = "%src" /\
  dfg_get_def (dfg_build_function ircf_witness_main) "%dst" =
    SOME (mk_inst 2 ALLOCA [Lit 32w] ["%dst"]) /\
  dfg_get_def (dfg_build_function ircf_witness_main) "%src" =
    SOME (mk_inst 1 ALLOCA [Lit 32w] ["%src"]) /\
  icf_collect_aliases (dfg_build_function ircf_witness_main) "%dst" = {"%dst"} /\
  icf_collect_aliases (dfg_build_function ircf_witness_main) "%src" = {"%src"} /\
  icf_use_positions (dfg_build_function ircf_witness_main) "%src" =
    [(mk_inst 3 INVOKE [Label "callee"; Var "%src"] [], 1);
     (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 1)] /\
  icf_use_positions (dfg_build_function ircf_witness_main) "%dst" =
    [(mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 0);
     (mk_inst 5 MLOAD [Var "%dst"] ["%x"], 0)] /\
  icf_invoke_has_ret_buf (icf_fn_meta_of ircf_witness_ctx)
    ircf_witness_ctx.ctx_functions
    (mk_inst 3 INVOKE [Label "callee"; Var "%src"] []) = T
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

Theorem ircf_witness_callee_root_buf[local,simp]:
  !dfg.
    root_param_indices_op dfg (FEMPTY |+ ("%buf", 0)) 1 {} (Var "%buf") = {0}
Proof
  simp[root_param_indices_op_def, Once root_param_indices_def, FLOOKUP_UPDATE]
QED

Theorem ircf_witness_rma:
  readonly_mem_analyze ircf_witness_ctx =
    FEMPTY |+ ("callee", [F]) |+ ("main", [])
Proof
  simp[readonly_mem_analyze_def, rma_analyze_def, icf_fn_meta_of_def,
       icf_fn_meta_of_fn_def, callLayoutDefsTheory.fn_user_param_insts_def,
       callLayoutDefsTheory.fn_entry_insts_def,
       default_internal_call_abi_def, ircf_witness_ctx_def,
       ircf_witness_callee_def, ircf_witness_main_def, mk_raw_function_def,
       mk_inst_def, entry_block_def, entry_param_outputs_def,
       collect_param_info_def, has_ret_instruction_def, build_param_index_def,
       rma_init_state_def, FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[rma_fixpoint_step_def, FLOOKUP_UPDATE, rma_analyze_fn_def,
       mem_write_ops_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[rma_fixpoint_step_def, FLOOKUP_UPDATE, rma_analyze_fn_def,
       mem_write_ops_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >>
  simp[fmap_eq_flookup, FLOOKUP_UPDATE] >> rw[]
QED

Theorem ircf_witness_callee_run_blocks:
  !fuel ctx args s cs.
    setup_callee ircf_witness_callee args s = SOME cs ==>
    case fuel of
      0 => run_blocks fuel ctx ircf_witness_callee cs = Error "out of fuel"
    | SUC _ =>
        case args of
          [] => run_blocks fuel ctx ircf_witness_callee cs =
                  Error "param: index out of range"
        | v0 :: _ =>
            ?rs.
              run_blocks fuel ctx ircf_witness_callee cs =
                IntRet <| iret_values := []; iret_adopt_fmp := NONE |> rs /\
              merge_callee_state s rs = mstore (w2n v0) 42w s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[Once run_blocks_def] >>
  Cases_on `args` >>
  gvs[setup_callee_def, ircf_witness_callee_def, mk_raw_function_def, mk_inst_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, eval_phis_def,
       phi_prefix_length_def] >>
  ntac 4
    (simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, is_terminator_def, exec_write2_def,
          eval_operands_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, mstore_def]) >>
  simp[merge_callee_state_def, mstore_def, venom_state_component_equality]
QED

Definition ircf_witness_bb0_def:
  ircf_witness_bb0 : basic_block =
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 MLOAD [Var "%dst"] ["%x"];
         mk_inst 6 SSTORE [Lit 0w; Var "%x"] [];
         mk_inst 7 STOP [] []
       ] |>
End

Definition ircf_witness_bb2_def:
  ircf_witness_bb2 : basic_block =
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
         mk_nop_inst (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] []);
         mk_inst 5 MLOAD [Var "%src"] ["%x"];
         mk_inst 6 SSTORE [Lit 0w; Var "%x"] [];
         mk_inst 7 STOP [] []
       ] |>
End

Theorem ircf_witness_try_forward_3[simp]:
  ircf_try_forward
    (icf_build_ctx (icf_fn_meta_of ircf_witness_ctx)
       ircf_witness_ctx.ctx_functions
       (readonly_mem_analyze ircf_witness_ctx)
       ircf_witness_main)
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 MLOAD [Var "%dst"] ["%x"];
         mk_inst 6 SSTORE [Lit 0w; Var "%x"] [];
         mk_inst 7 STOP [] []
       ] |>
    3 =
  SOME [
    mk_inst 1 ALLOCA [Lit 32w] ["%src"];
    mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
    mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
    mk_nop_inst (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] []);
    mk_inst 5 MLOAD [Var "%src"] ["%x"];
    mk_inst 6 SSTORE [Lit 0w; Var "%x"] [];
    mk_inst 7 STOP [] []
  ]
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[ircf_try_forward_def, icf_build_ctx_def,
       ircf_is_ret_buf_source_def, icf_is_alloca_def,
       icf_matches_alloca_size_def, icf_is_assign_output_use_def,
       is_mem_addr_position_def, findi_def, INDEX_FIND_def,
       rich_listTheory.COUNT_LIST_def] >>
  simp[mk_inst_def, wordsTheory.dimword_def]
QED

Theorem ircf_witness_main_fwd_step_eq[local]:
  !bb1 copy_idx bb2.
    icf_mcopy_noped ircf_witness_bb0 bb1 /\
    icf_fwd_step (icf_fn_meta_of ircf_witness_ctx)
      ircf_witness_ctx.ctx_functions
      (readonly_mem_analyze ircf_witness_ctx)
      ircf_witness_main bb1 copy_idx bb2 ==>
    bb1 = ircf_witness_bb0 /\ copy_idx = 3 /\ bb2 = ircf_witness_bb2
Proof
  rpt strip_tac >>
  drule icf_fwd_step_structural >> strip_tac >>
  `3 < LENGTH ircf_witness_bb0.bb_instructions /\
   (EL 3 ircf_witness_bb0.bb_instructions).inst_opcode = MCOPY /\
   (!j. j < LENGTH ircf_witness_bb0.bb_instructions /\ j <> 3 ==>
        (EL j ircf_witness_bb0.bb_instructions).inst_opcode <> MCOPY)` by
    (simp[ircf_witness_bb0_def] >> irule unique_mcopy_7_at_3 >> simp[]) >>
  `bb1 = ircf_witness_bb0 /\ copy_idx = 3` by
    metis_tac[icf_mcopy_noped_unique_mcopy] >>
  gvs[] >>
  qpat_x_assum `icf_fwd_step _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [icf_fwd_step_def]) >>
  gvs[ircf_witness_bb0_def, ircf_witness_bb2_def] >>
  `icf_mcopy_noped ircf_witness_bb0 b` by
    (qpat_x_assum `icf_mcopy_noped _ b` mp_tac >>
     simp[GSYM ircf_witness_bb0_def]) >>
  `3 < LENGTH b.bb_instructions /\
   (EL 3 b.bb_instructions).inst_opcode = MCOPY` by
    (irule icf_mcopy_noped_mcopy_back >>
     qexists_tac `ircf_witness_bb0` >> simp[ircf_witness_bb0_def]) >>
  `b = ircf_witness_bb0` by
    metis_tac[icf_mcopy_noped_unique_mcopy] >>
  `ircf_witness_main with fn_blocks := [ircf_witness_bb0] =
   ircf_witness_main` by
    simp[ircf_witness_main_def, mk_raw_function_def,
         ircf_witness_bb0_def, ir_function_component_equality] >>
  gvs[ricf_try_forward_def, icf_build_ctx_def, icf_is_assign_output_use_def,
      ircf_witness_bb0_def]
QED

Theorem ircf_witness_rma_sound:
  rma_sound ircf_witness_ctx (readonly_mem_analyze ircf_witness_ctx)
Proof
  rw[rma_sound_def]
  >- (gvs[ircf_witness_rma] >>
      `callee_fn = ircf_witness_callee` by
        (fs[ircf_witness_ctx_def] >>
         `~has_ret_instruction ircf_witness_main` by EVAL_TAC >>
         gvs[]) >>
      gvs[] >>
      qpat_x_assum `setup_callee ircf_witness_callee args1 s1 = SOME cs1`
        (mp_tac o MATCH_MP ircf_witness_callee_run_blocks) >>
      disch_then (qspecl_then [`fuel`, `ircf_witness_ctx`] mp_tac) >>
      qpat_x_assum `setup_callee ircf_witness_callee args2 s2 = SOME cs2`
        (mp_tac o MATCH_MP ircf_witness_callee_run_blocks) >>
      disch_then (qspecl_then [`fuel`, `ircf_witness_ctx`] mp_tac) >>
      Cases_on `fuel` >- simp[callee_return_rel_def] >>
      `LENGTH args2 = LENGTH args1` by fs[rma_args_ok_def] >>
      Cases_on `args1` >> Cases_on `args2` >> gvs[callee_return_rel_def] >>
      rpt strip_tac >> gvs[callee_return_rel_def] >>
      `rma_arg_pair_ok (FEMPTY |+ ("callee", [F]) |+ ("main", []))
         ircf_witness_callee.fn_name dst_addr src_addr sz 0 h h'` by
        (fs[rma_args_ok_def] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      `ircf_witness_callee.fn_name = "callee" /\
       rma_is_readonly (FEMPTY |+ ("callee", [F]) |+ ("main", [])) "callee" 0 = F` by
        EVAL_TAC >>
      gvs[rma_arg_pair_ok_def] >>
      irule mstore_preserves_copy_fwd_state_rel_disjoint >> simp[])
  >- (fs[ircf_witness_ctx_def] >> gvs[]
      >- (`EVERY (\i. i.inst_opcode <> MCOPY) bb0.bb_instructions` by
            (gvs[ircf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC) >>
          `bb1 = bb0` by metis_tac[icf_mcopy_noped_no_mcopy] >>
          metis_tac[icf_fwd_step_has_mcopy])
      >- (`icf_mcopy_noped ircf_witness_bb0 bb1` by
            (qpat_x_assum `icf_mcopy_noped _ bb1` mp_tac >>
             simp[GSYM ircf_witness_bb0_def]) >>
          qpat_x_assum `icf_fwd_step _ _ _ _ _ _ _` mp_tac >>
          simp[GSYM ircf_witness_ctx_def] >> strip_tac >>
          drule_all ircf_witness_main_fwd_step_eq >> strip_tac >> gvs[] >>
          `s_phi = s /\ phi_prefix_length ircf_witness_bb0.bb_instructions = 0` by
            gvs[ircf_witness_bb0_def, eval_phis_def, phi_prefix_length_def,
                mk_inst_def] >>
          gvs[] >>
          drule prefix_steps_3_from_0 >>
          simp[ircf_witness_bb0_def, get_instruction_def] >> strip_tac >>
          qpat_x_assum `step_inst _ _ (mk_inst 1 ALLOCA _ _) _ = OK s1`
            (strip_assume_tac o MATCH_MP step_inst_alloca_ok) >>
          qpat_x_assum `step_inst _ _ (mk_inst 2 ALLOCA _ _) _ = OK s2`
            (strip_assume_tac o MATCH_MP step_inst_alloca_ok) >>
          `lookup_var "%src" s2 = SOME v` by
            (first_x_assum (qspec_then `"%src"` mp_tac) >>
             fs[lookup_var_def]) >>
          `lookup_var "%dst" s3 = SOME v' /\ lookup_var "%src" s3 = SOME v` by
            (drule venomInstPropsTheory.step_preserves_non_output_vars >>
             simp[is_terminator_def] >> strip_tac >>
             first_assum (qspec_then `"%dst"` mp_tac) >>
             first_x_assum (qspec_then `"%src"` mp_tac) >>
             fs[lookup_var_def]) >>
          qexistsl_tac [`v'`, `v`] >>
          simp[ircf_witness_bb0_def, eval_operand_def, lookup_var_def] >>
          conj_tac
          >- (rpt strip_tac >>
              `j = 4 \/ j = 5 \/ j = 6` by decide_tac >> gvs[])
          >- (rpt strip_tac >>
              `j = 4 \/ j = 5 \/ j = 6` by decide_tac >> gvs[]
              >- (simp[ircf_witness_bb0_def, ircf_witness_bb2_def,
                       icf_suffix_inst_rel_def, is_terminator_def] >>
                  irule step_inst_base_mload_cross_copy_fwd_state_rel >>
                  simp[lookup_var_def])
              >- simp[ircf_witness_bb0_def, ircf_witness_bb2_def,
                      icf_suffix_inst_rel_def, is_terminator_def,
                      step_inst_base_sstore_copy_fwd_state_rel]
              >- simp[ircf_witness_bb0_def, ircf_witness_bb2_def,
                      icf_suffix_inst_rel_def, is_terminator_def,
                      step_inst_base_stop_copy_fwd_state_rel])))
QED

Theorem ircf_witness_wf:
  o1_ctx_shape ircf_witness_ctx /\
  EVERY wf_ssa ircf_witness_ctx.ctx_functions /\
  EVERY ircf_no_dst_write_alias ircf_witness_ctx.ctx_functions /\
  rma_sound ircf_witness_ctx (readonly_mem_analyze ircf_witness_ctx)
Proof
  rpt conj_tac
  >- (simp[o1_ctx_shape_def] >> rpt conj_tac
      >- EVAL_TAC
      >- EVAL_TAC
      >- (simp[ircf_witness_ctx_def] >> conj_tac
          >- (irule single_block_o1_fn_shape >>
              simp[ircf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC)
          >- (irule single_block_o1_fn_shape >>
              simp[ircf_witness_main_def, mk_raw_function_def] >> EVAL_TAC)))
  >- (simp[ircf_witness_ctx_def] >> conj_tac
      >- (irule single_block_wf_ssa >>
           simp[ircf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC)
      >- (irule single_block_wf_ssa >>
          simp[ircf_witness_main_def, mk_raw_function_def] >> EVAL_TAC))
  >- (simp[ircf_witness_ctx_def, ircf_no_dst_write_alias_def] >>
      conj_tac
      >- (rw[ircf_witness_callee_def, mk_raw_function_def, mk_inst_def] >> gvs[])
      >- (rw[mk_inst_def] >> gvs[mem_write_ops_def]))
  >- simp[ircf_witness_rma_sound]
QED

Theorem ircf_block_step_non_mcopy[simp]:
  i < LENGTH cur_bb.bb_instructions /\
  (EL i cur_bb.bb_instructions).inst_opcode <> MCOPY ==>
  ircf_block_step ctx (changed, cur_bb) i = (changed, cur_bb)
Proof
  rw[ircf_block_step_def]
QED

Theorem ircf_block_step_mcopy[simp]:
  i < LENGTH cur_bb.bb_instructions /\
  (EL i cur_bb.bb_instructions).inst_opcode = MCOPY ==>
  ircf_block_step ctx (changed, cur_bb) i =
    case ircf_try_forward ctx cur_bb i of
      NONE => (changed, cur_bb)
    | SOME new_insts =>
        (T, cur_bb with bb_instructions := new_insts)
Proof
  rw[ircf_block_step_def]
QED

Theorem ircf_witness_forwards:
  ircf_transform_function
    (icf_fn_meta_of ircf_witness_ctx)
    ircf_witness_ctx.ctx_functions
    (readonly_mem_analyze ircf_witness_ctx)
    ircf_witness_main <> ircf_witness_main /\
  EVERY (\bb. EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions)
    (ircf_transform_function
      (icf_fn_meta_of ircf_witness_ctx)
      ircf_witness_ctx.ctx_functions
      (readonly_mem_analyze ircf_witness_ctx)
      ircf_witness_main).fn_blocks
Proof
  `COUNT_LIST 7 = [0; 1; 2; 3; 4; 5; 6]` by EVAL_TAC >>
  simp[ircf_transform_function_def] >>
  simp[ircf_transform_block_eq_foldl,
       clear_nops_function_def, clear_nops_block_def,
       mk_nop_inst_def] >>
  simp[ircf_witness_main_def, mk_raw_function_def, mk_inst_def]
QED
