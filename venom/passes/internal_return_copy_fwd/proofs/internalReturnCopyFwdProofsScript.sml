(*
 * Internal Return Copy Forwarding — Proofs
 *
 * Proves CFG compatibility and wf_function preservation of the transform,
 * and a concrete non-vacuity witness (ircf_witness_ctx) for
 * ircf_pass_correct (internalReturnCopyFwdSim): every premise holds and ircf
 * forwards a post-invoke return-buffer MCOPY, eliminating the copy.
 *)

Theory internalReturnCopyFwdProofs
Ancestors
  internalReturnCopyFwdSim internalReturnCopyFwdDefs invokeCopyFwdCommonDefs
  readonlyMemoryArgsProps
  readonlyMemoryArgsDefs callLayoutDefs memLocDefs o1PassContract
  ptrDiscipline ptrSafeRun ptrOkCheck unitTransformDefs copyFwdEquiv passSharedDefs venomWf
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

(* ==========================================================================
   3. Context-Level Transformation
   ========================================================================== *)

Theorem ircf_transform_ctx_entry[simp]:
  !ctx fn_meta rma.
    (ircf_transform_ctx fn_meta rma ctx).ctx_entry = ctx.ctx_entry
Proof
  simp[ircf_transform_ctx_def]
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

Theorem ircf_witness_wf:
  o1_ctx_shape ircf_witness_ctx /\
  EVERY wf_ssa ircf_witness_ctx.ctx_functions /\
  EVERY ircf_no_dst_write_alias ircf_witness_ctx.ctx_functions
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

Theorem ircf_witness_ptr_static:
  EVERY (fn_ptr_ok (\nm. if nm = "callee" then {0} else {}))
    ircf_witness_ctx.ctx_functions /\
  EVERY (\f. fn_ptr_ok (\nm. if nm = "callee" then {0} else {})
    (reachable_fn f)) ircf_witness_ctx.ctx_functions /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) ircf_witness_ctx.ctx_functions
Proof
  `reachable_fn ircf_witness_callee = fn_reachable_blocks ircf_witness_callee` by
    (sym_tac >> irule fn_reachable_blocks_reachable_fn >> EVAL_TAC) >>
  `reachable_fn ircf_witness_main = fn_reachable_blocks ircf_witness_main` by
    (sym_tac >> irule fn_reachable_blocks_reachable_fn >> EVAL_TAC) >>
  ` (\nm:string. if nm = "callee" then {0:num} else {}) =
    (\nm. set (if nm = "callee" then [0] else []))` by
    (simp[FUN_EQ_THM] >> gen_tac >> IF_CASES_TAC >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[ircf_witness_ctx_def] >> rpt conj_tac
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- (match_mp_tac (BETA_RULE (Q.SPEC `\nm. if nm = "callee" then [0] else []` fn_ptr_ok_check_sound)) >> EVAL_TAC >> simp[])
  >- EVAL_TAC
  >- EVAL_TAC
QED

(* Every premise of ircf_pass_correct holds on ircf_witness_ctx, and the pass
   changes it.  D treats every storage, transient, immutable and return-data
   byte as dead, as o1_pipeline_correct instantiates it. *)
Theorem ircf_pass_correct_nonvacuity:
  ?D lo vs.
    o1_ctx_shape ircf_witness_ctx /\
    EVERY wf_ssa ircf_witness_ctx.ctx_functions /\
    EVERY ircf_no_dst_write_alias ircf_witness_ctx.ctx_functions /\
    ptr_discipline lo ircf_witness_ctx vs /\ vs.vs_allocas = FEMPTY /\
    ~vs.vs_halted /\ ~ctx_has_dalloca ircf_witness_ctx /\
    taint_within D ircf_witness_ctx vs /\ dead_wf D /\
    ircf_transform_ctx (icf_fn_meta_of ircf_witness_ctx)
      (readonly_mem_analyze ircf_witness_ctx) ircf_witness_ctx <>
    ircf_witness_ctx
Proof
  cheat
QED
