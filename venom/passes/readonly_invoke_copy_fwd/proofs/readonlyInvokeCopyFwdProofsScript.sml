(*
 * Readonly Invoke Arg Copy Forwarding — Proofs
 *
 * Proves structural compatibility, function-name preservation, context-level
 * simulation (ricf_pass_correct) under ptr_discipline and rma_sound, and a
 * concrete non-vacuity witness (ricf_witness_ctx) where readonly_mem_analyze
 * infers a readonly parameter and ricf forwards a pre-invoke staging MCOPY.
 *)

Theory readonlyInvokeCopyFwdProofs
Ancestors
  readonlyInvokeCopyFwdDefs internalReturnCopyFwdDefs invokeCopyFwdCommonDefs
  readonlyMemoryArgsProps readonlyMemoryArgsDefs callLayoutDefs dfgDefs
  memLocDefs o1PassContract ptrDiscipline unitTransformDefs copyFwdEquiv
  passSharedDefs venomWf venomInst venomInstProps venomExecSemantics
  venomState stateEquiv While list rich_list finite_map pred_set arithmetic
  pair option words

(* ==========================================================================
   1. Instruction and Block Compatibility of ricf_try_forward / ricf_apply_forward
   ========================================================================== *)

Definition ricf_site_accum_step_def:
  ricf_site_accum_step (rma : (string, bool list) fmap) (copy_id : num)
                       (acc : (instruction # num) list option)
                       (v : string, inst : instruction, pos : num) =
    case acc of
      NONE => NONE
    | SOME sites =>
        if icf_is_assign_output_use inst pos then SOME sites
        else if inst.inst_opcode = MCOPY /\ pos = 0 then
          if inst.inst_id = copy_id then SOME sites
          else NONE
        else if inst.inst_opcode = INVOKE /\
                icf_is_readonly_op rma inst pos
        then SOME ((inst, pos) :: sites)
        else NONE
End

Theorem FOLDL_ricf_site_accum_every[local]:
  !ups rma copy_id acc sites.
    FOLDL (ricf_site_accum_step rma copy_id) acc ups = SOME sites /\
    (case acc of
       NONE => F
     | SOME acc0 =>
         EVERY (\(inst, pos).
           inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos) acc0) ==>
    EVERY (\(inst, pos).
      inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos) sites
Proof
  Induct >- (Cases_on `acc` >> simp[]) >>
  simp[pairTheory.FORALL_PROD, ricf_site_accum_step_def] >>
  rpt gen_tac >> Cases_on `acc` >> simp[] >>
  rw[] >> first_x_assum drule >> simp[]
QED

Theorem ricf_try_forward_auth:
  !ctx bb copy_idx src_var_opt rewrite_sites.
    ricf_try_forward ctx bb copy_idx = SOME (src_var_opt, rewrite_sites) ==>
    copy_idx < LENGTH bb.bb_instructions /\
    (EL copy_idx bb.bb_instructions).inst_opcode = MCOPY /\
    icf_auth_ok ctx.icf_fn_meta ctx.icf_functions ctx.icf_rma
Proof
  simp[ricf_try_forward_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `FOLDL _ (SOME []) _ = SOME (h::t)` >>
  qmatch_asmsub_abbrev_tac `FOLDL step_fn (SOME []) ups = SOME (h::t)` >>
  `step_fn = ricf_site_accum_step ctx.icf_rma
               (EL copy_idx bb.bb_instructions).inst_id` by
    (simp[Abbr `step_fn`, FUN_EQ_THM, pairTheory.FORALL_PROD,
          ricf_site_accum_step_def]) >>
  gvs[] >>
  drule FOLDL_ricf_site_accum_every >> simp[] >> strip_tac >>
  PairCases_on `h` >> fs[icf_auth_ok_def] >> metis_tac[]
QED

Theorem ricf_apply_forward_compat:
  !insts copy_idx src rewrite_sites.
    copy_idx < LENGTH insts /\
    (EL copy_idx insts).inst_opcode = MCOPY ==>
    (EL copy_idx
       (ricf_apply_forward insts copy_idx src rewrite_sites)).inst_opcode =
      NOP /\
    LIST_REL icf_inst_compat insts
      (ricf_apply_forward insts copy_idx src rewrite_sites)
Proof
  rw[ricf_apply_forward_def, LIST_REL_EL_EQN] >>
  Cases_on `n = copy_idx` >> simp[icf_inst_compat_mk_nop] >>
  rw[icf_inst_compat_def]
QED

(* ==========================================================================
   2. Block, Step, and Fixpoint Compatibility of ricf
   ========================================================================== *)

Definition ricf_block_step_def:
  ricf_block_step (ctx : icf_ctx) (changed : bool, cur_bb : basic_block)
                  (i : num) =
    if i >= LENGTH cur_bb.bb_instructions then (changed, cur_bb)
    else
      let inst = EL i cur_bb.bb_instructions in
      if inst.inst_opcode <> MCOPY then (changed, cur_bb)
      else
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
End

Theorem ricf_block_step_compat:
  !fn_meta ctx_fns rma fn cur_bbs b bb0 c0 cur_bb i c1 next_bb.
    wf_ssa fn /\
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn /\
    LIST_REL icf_mcopy_noped fn.fn_blocks cur_bbs /\
    MEM b cur_bbs /\
    icf_mcopy_noped b cur_bb /\
    icf_block_compat fn_meta ctx_fns rma fn bb0 cur_bb /\
    ricf_block_step
      ((icf_build_ctx fn_meta ctx_fns rma fn) with
         icf_dfg := dfg_build_function (fn with fn_blocks := cur_bbs))
      (c0, cur_bb) i = (c1, next_bb) ==>
    icf_mcopy_noped b next_bb /\
    icf_block_compat fn_meta ctx_fns rma fn bb0 next_bb
Proof
  rw[ricf_block_step_def] >> gvs[AllCaseEqs()] >>
  drule ricf_try_forward_auth >> strip_tac >>
  `icf_auth_ok fn_meta ctx_fns rma` by fs[icf_build_ctx_def] >>
  drule_all ricf_apply_forward_compat >>
  disch_then (qspecl_then [
    `case src_var_opt of
       NONE => EL 1 (EL i cur_bb.bb_instructions).inst_operands
     | SOME sv => Var sv`,
    `rewrite_sites`] strip_assume_tac) >>
  qabbrev_tac `new_insts =
    ricf_apply_forward cur_bb.bb_instructions i
      (case src_var_opt of
         NONE => EL 1 (EL i cur_bb.bb_instructions).inst_operands
       | SOME sv => Var sv) rewrite_sites` >>
  `icf_mcopy_noped cur_bb (cur_bb with bb_instructions := new_insts)` by
    (irule icf_mcopy_noped_step >>
     qexistsl_tac [`cur_bb`, `i`] >> gvs[Abbr `new_insts`]) >>
  `icf_fwd_step fn_meta ctx_fns rma fn cur_bb i
     (cur_bb with bb_instructions := new_insts)` by
    (simp[icf_fwd_step_def, LET_THM] >> disj2_tac >>
     qexistsl_tac [`cur_bbs`, `b`, `src_var_opt`, `rewrite_sites`] >>
     gvs[Abbr `new_insts`]) >>
  metis_tac[icf_mcopy_noped_trans, icf_block_compat_step]
QED

Theorem FOLDL_ricf_block_step_compat:
  !idxs fn_meta ctx_fns rma fn cur_bbs b bb0 c0 cur_bb.
    wf_ssa fn /\
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn /\
    LIST_REL icf_mcopy_noped fn.fn_blocks cur_bbs /\
    MEM b cur_bbs /\
    icf_mcopy_noped b cur_bb /\
    icf_block_compat fn_meta ctx_fns rma fn bb0 cur_bb ==>
    icf_mcopy_noped b
      (SND (FOLDL (ricf_block_step
                     ((icf_build_ctx fn_meta ctx_fns rma fn) with
                        icf_dfg := dfg_build_function (fn with fn_blocks := cur_bbs)))
              (c0, cur_bb) idxs)) /\
    icf_block_compat fn_meta ctx_fns rma fn bb0
      (SND (FOLDL (ricf_block_step
                     ((icf_build_ctx fn_meta ctx_fns rma fn) with
                        icf_dfg := dfg_build_function (fn with fn_blocks := cur_bbs)))
              (c0, cur_bb) idxs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `ricf_block_step
              ((icf_build_ctx fn_meta ctx_fns rma fn) with
                 icf_dfg := dfg_build_function (fn with fn_blocks := cur_bbs))
              (c0, cur_bb) h` >>
  drule_all ricf_block_step_compat >> strip_tac >>
  first_x_assum
    (qspecl_then [`fn_meta`, `ctx_fns`, `rma`, `fn`, `cur_bbs`, `b`, `bb0`,
                  `q`, `r`] mp_tac) >>
  simp[]
QED

Theorem ricf_pass_block_eq_foldl:
  !ctx bb.
    ricf_pass_block ctx bb =
    FOLDL (ricf_block_step ctx) (F, bb)
      (COUNT_LIST (LENGTH bb.bb_instructions))
Proof
  rw[ricf_pass_block_def, ricf_block_step_def] >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD, ricf_block_step_def]
QED

Theorem ricf_pass_block_compat:
  !fn_meta ctx_fns rma fn cur_bbs bb0 bb.
    wf_ssa fn /\
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn /\
    LIST_REL icf_mcopy_noped fn.fn_blocks cur_bbs /\
    MEM bb cur_bbs /\
    icf_block_compat fn_meta ctx_fns rma fn bb0 bb ==>
    icf_block_compat fn_meta ctx_fns rma fn bb0
      (SND (ricf_pass_block
              ((icf_build_ctx fn_meta ctx_fns rma fn) with
                 icf_dfg := dfg_build_function (fn with fn_blocks := cur_bbs))
              bb))
Proof
  rpt strip_tac >> simp[ricf_pass_block_eq_foldl] >>
  mp_tac (Q.SPECL [`COUNT_LIST (LENGTH bb.bb_instructions)`,
                   `fn_meta`, `ctx_fns`, `rma`, `fn`, `cur_bbs`, `bb`, `bb0`,
                   `F`, `bb`]
          FOLDL_ricf_block_step_compat) >>
  simp[]
QED

Theorem ricf_function_step_blocks_compat:
  !fn_meta ctx_fns rma fn ctx cur_fn changed new_fn.
    wf_ssa fn /\
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn /\
    ctx = (icf_build_ctx fn_meta ctx_fns rma fn) with
            icf_dfg := dfg_build_function cur_fn /\
    cur_fn = (fn with fn_blocks := cur_fn.fn_blocks) /\
    LIST_REL (icf_block_compat fn_meta ctx_fns rma fn)
      fn.fn_blocks cur_fn.fn_blocks /\
    ricf_function_step ctx cur_fn = (changed, new_fn) ==>
    new_fn = (fn with fn_blocks := new_fn.fn_blocks) /\
    LIST_REL (icf_block_compat fn_meta ctx_fns rma fn)
      fn.fn_blocks new_fn.fn_blocks
Proof
  ntac 8 gen_tac >> strip_tac >>
  fs[ricf_function_step_def] >>
  pairarg_tac >> gvs[] >>
  `new_blocks = MAP (\bb. SND (ricf_pass_block ctx bb)) cur_fn.fn_blocks` by
    (mp_tac (Q.SPECL [`ricf_pass_block ctx`, `cur_fn.fn_blocks`, `F`, `[]`]
               FOLDL_block_pass_SND) >>
     simp[]) >>
  gvs[] >>
  conj_tac
  >- (qpat_x_assum `cur_fn = _` SUBST1_TAC >> simp[])
  >- (`LIST_REL icf_mcopy_noped fn.fn_blocks cur_fn.fn_blocks` by
        (qpat_x_assum `LIST_REL _ _ _`
           (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
         rw[LIST_REL_EL_EQN, icf_block_compat_def]) >>
      qpat_x_assum `LIST_REL (icf_block_compat _ _ _ _) _ _`
        (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
      rw[LIST_REL_EL_EQN, EL_MAP] >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      `MEM (EL n cur_fn.fn_blocks) cur_fn.fn_blocks` by simp[EL_MEM] >>
      mp_tac (Q.SPECL [`fn_meta`, `ctx_fns`, `rma`, `fn`, `cur_fn.fn_blocks`,
                       `EL n fn.fn_blocks`, `EL n cur_fn.fn_blocks`]
              ricf_pass_block_compat) >>
      simp[] >>
      qpat_x_assum `cur_fn = _` (SUBST1_TAC o SYM) >> simp[])
QED

Definition ricf_loop_inv_def:
  ricf_loop_inv (fn_meta : (string, invoke_fn_meta) fmap)
                (ctx_fns : ir_function list)
                (rma : (string, bool list) fmap)
                (fn : ir_function)
                (state : bool # icf_ctx # ir_function) : bool <=>
    let (_, ctx, cur_fn) = state in
    ctx = (icf_build_ctx fn_meta ctx_fns rma fn) with
            icf_dfg := dfg_build_function cur_fn /\
    cur_fn = (fn with fn_blocks := cur_fn.fn_blocks) /\
    LIST_REL (icf_block_compat fn_meta ctx_fns rma fn)
      fn.fn_blocks cur_fn.fn_blocks
End

Theorem ricf_transform_function_fn_compat:
  !fn_meta ctx_fns rma fn.
    wf_ssa fn /\
    ricf_full_alloca_copies fn /\
    ricf_no_derived_mutable_sibling fn ==>
    icf_fn_compat fn_meta ctx_fns rma fn
      (ricf_transform_function fn_meta ctx_fns rma fn)
Proof
  rpt strip_tac >>
  simp[ricf_transform_function_def] >>
  qmatch_goalsub_abbrev_tac `OWHILE G step_fn (T, ctx0, fn)` >>
  Cases_on `OWHILE G step_fn (T, ctx0, fn)` >> simp[] >>
  rename1 `SOME res` >> PairCases_on `res` >> simp[] >>
  mp_tac (WhileTheory.OWHILE_INV_IND
            |> INST_TYPE [alpha |-> ``:bool # icf_ctx # ir_function``]
            |> Q.INST [`P` |-> `ricf_loop_inv fn_meta ctx_fns rma fn`]
            |> Q.SPECL [`G`, `step_fn`, `(T, ctx0, fn)`]) >>
  impl_tac
  >- (conj_tac
      >- (simp[ricf_loop_inv_def, Abbr `ctx0`, icf_build_ctx_def,
               icf_ctx_component_equality] >>
          irule EVERY2_refl >> simp[])
      >- (rpt strip_tac >> PairCases_on `x` >>
          fs[Abbr `step_fn`, ricf_loop_inv_def] >>
          Cases_on `ricf_function_step x1 x2` >> simp[] >>
          drule_all ricf_function_step_blocks_compat >> strip_tac >>
          rw[] >> gvs[])) >>
  disch_then (qspec_then `(res0, res1, res2)` mp_tac) >>
  simp[ricf_loop_inv_def] >> strip_tac >>
  simp[icf_fn_compat_def] >> disj2_tac >>
  qexists_tac `res2.fn_blocks` >> simp[] >>
  qpat_x_assum `res2 = _` (SUBST1_TAC o SYM) >> rw[]
QED

Theorem ricf_transform_function_fn_name:
  !fn_meta ctx_fns rma fn.
    (ricf_transform_function fn_meta ctx_fns rma fn).fn_name = fn.fn_name
Proof
  rpt gen_tac >> simp[ricf_transform_function_def] >>
  qmatch_goalsub_abbrev_tac `OWHILE G step_fn (T, ctx0, fn)` >>
  Cases_on `OWHILE G step_fn (T, ctx0, fn)` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  mp_tac (WhileTheory.OWHILE_INV_IND
            |> INST_TYPE [alpha |-> ``:bool # icf_ctx # ir_function``]
            |> Q.INST [`P` |-> `\(c, ctx, cur_fn). cur_fn.fn_name = fn.fn_name`]
            |> Q.SPECL [`G`, `step_fn`, `(T, ctx0, fn)`]) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> PairCases_on `x` >>
      fs[Abbr `step_fn`, ricf_function_step_def] >>
      pairarg_tac >> gvs[] >> rw[] >> gvs[]) >>
  disch_then (qspec_then `(x0, x1, x2)` mp_tac) >>
  simp[clear_nops_function_def] >> rw[]
QED

(* ==========================================================================
   3. Context-Level Transformation and Correctness (ricf_pass_correct)
   ========================================================================== *)

Definition ricf_transform_ctx_def:
  ricf_transform_ctx (fn_meta : (string, invoke_fn_meta) fmap)
                     (rma : (string, bool list) fmap)
                     (ctx : venom_context) : venom_context =
    ctx with ctx_functions :=
      MAP (ricf_transform_function fn_meta ctx.ctx_functions rma)
          ctx.ctx_functions
End

Theorem ricf_transform_ctx_entry[simp]:
  !ctx fn_meta rma.
    (ricf_transform_ctx fn_meta rma ctx).ctx_entry = ctx.ctx_entry
Proof
  simp[ricf_transform_ctx_def]
QED

Theorem ricf_transform_ctx_fn_compat:
  !ctx fn_meta rma.
    EVERY wf_ssa ctx.ctx_functions /\
    EVERY ricf_full_alloca_copies ctx.ctx_functions /\
    EVERY ricf_no_derived_mutable_sibling ctx.ctx_functions ==>
    LIST_REL (icf_fn_compat fn_meta ctx.ctx_functions rma)
      ctx.ctx_functions
      (ricf_transform_ctx fn_meta rma ctx).ctx_functions
Proof
  rw[ricf_transform_ctx_def, LIST_REL_EL_EQN, EL_MAP] >>
  irule ricf_transform_function_fn_compat >>
  fs[EVERY_EL]
QED

Theorem ricf_pass_correct:
  !D lo ctx fn_meta rma vs.
    o1_ctx_shape ctx /\
    EVERY wf_ssa ctx.ctx_functions /\
    EVERY ricf_full_alloca_copies ctx.ctx_functions /\
    EVERY ricf_no_derived_mutable_sibling ctx.ctx_functions /\
    ptr_discipline lo ctx vs /\
    fn_meta = icf_fn_meta_of ctx /\
    rma = readonly_mem_analyze ctx /\
    rma_sound ctx rma ==>
    ctx_sim D ctx (ricf_transform_ctx fn_meta rma ctx) vs vs
Proof
  rpt strip_tac >>
  irule icf_ctx_sim_from_fn_compat >> simp[] >>
  qexistsl_tac [`lo`, `fn_meta`, `rma`] >>
  simp[ricf_transform_ctx_fn_compat]
QED

(* ==========================================================================
   4. Concrete Non-Vacuity Witness (ricf_witness_ctx)
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

Theorem ricf_witness_callee_run_blocks:
  !fuel ctx args s cs.
    setup_callee ricf_witness_callee args s = SOME cs ==>
    case fuel of
      0 => run_blocks fuel ctx ricf_witness_callee cs = Error "out of fuel"
    | SUC _ =>
        case args of
          [] => run_blocks fuel ctx ricf_witness_callee cs =
                  Error "param: index out of range"
        | v0 :: _ =>
            ?rs.
              run_blocks fuel ctx ricf_witness_callee cs =
                IntRet <| iret_values := [mload (w2n v0) s];
                          iret_adopt_fmp := NONE |> rs /\
              merge_callee_state s rs = s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[Once run_blocks_def] >>
  Cases_on `args` >>
  gvs[setup_callee_def, ricf_witness_callee_def, mk_raw_function_def, mk_inst_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, eval_phis_def,
       phi_prefix_length_def] >>
  ntac 4
    (simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, is_terminator_def, exec_read1_def,
          eval_operands_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, mload_def]) >>
  simp[merge_callee_state_def, venom_state_component_equality]
QED

Definition ricf_witness_bb0_def:
  ricf_witness_bb0 : basic_block =
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
End

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

Theorem ricf_witness_main_fwd_step_eq[local]:
  !bb1 copy_idx bb2.
    icf_mcopy_noped ricf_witness_bb0 bb1 /\
    icf_fwd_step (icf_fn_meta_of ricf_witness_ctx)
      ricf_witness_ctx.ctx_functions
      (readonly_mem_analyze ricf_witness_ctx)
      ricf_witness_main bb1 copy_idx bb2 ==>
    bb1 = ricf_witness_bb0 /\ copy_idx = 3 /\ bb2 = ricf_witness_bb1
Proof
  rpt strip_tac >>
  drule icf_fwd_step_structural >> strip_tac >>
  `3 < LENGTH ricf_witness_bb0.bb_instructions /\
   (EL 3 ricf_witness_bb0.bb_instructions).inst_opcode = MCOPY /\
   (!j. j < LENGTH ricf_witness_bb0.bb_instructions /\ j <> 3 ==>
        (EL j ricf_witness_bb0.bb_instructions).inst_opcode <> MCOPY)` by
    (simp[ricf_witness_bb0_def] >> irule unique_mcopy_7_at_3 >> simp[]) >>
  `bb1 = ricf_witness_bb0 /\ copy_idx = 3` by
    metis_tac[icf_mcopy_noped_unique_mcopy] >>
  gvs[] >>
  qpat_x_assum `icf_fwd_step _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [icf_fwd_step_def])
  >- gvs[ircf_try_forward_def, icf_build_ctx_def, ircf_is_ret_buf_source_def,
         icf_is_assign_output_use_def, ricf_witness_bb0_def]
  >- (`icf_mcopy_noped ricf_witness_bb0 b` by
        (qpat_x_assum `icf_mcopy_noped _ b` mp_tac >>
         simp[GSYM ricf_witness_bb0_def]) >>
      `3 < LENGTH b.bb_instructions /\
       (EL 3 b.bb_instructions).inst_opcode = MCOPY` by
        (irule icf_mcopy_noped_mcopy_back >>
         qexists_tac `ricf_witness_bb0` >> simp[ricf_witness_bb0_def]) >>
      `b = ricf_witness_bb0` by
        metis_tac[icf_mcopy_noped_unique_mcopy] >>
      qpat_x_assum `b = ricf_witness_bb0` SUBST_ALL_TAC >>
      `ricf_witness_main with fn_blocks := [ricf_witness_bb0] =
       ricf_witness_main` by
        simp[ricf_witness_main_def, mk_raw_function_def,
             ricf_witness_bb0_def, ir_function_component_equality] >>
      pop_assum SUBST_ALL_TAC >>
      `(icf_build_ctx (icf_fn_meta_of ricf_witness_ctx)
          ricf_witness_ctx.ctx_functions
          (readonly_mem_analyze ricf_witness_ctx)
          ricf_witness_main) with
          icf_dfg := dfg_build_function ricf_witness_main =
       icf_build_ctx (icf_fn_meta_of ricf_witness_ctx)
         ricf_witness_ctx.ctx_functions
         (readonly_mem_analyze ricf_witness_ctx)
         ricf_witness_main` by
        simp[icf_build_ctx_def, icf_ctx_component_equality] >>
      pop_assum SUBST_ALL_TAC >>
      gvs[ricf_witness_rma, ricf_witness_bb0_def, ricf_witness_bb1_def,
          LET_THM, ricf_apply_forward_def, mk_nop_inst_def])
QED

Theorem ricf_witness_rma_sound:
  rma_sound ricf_witness_ctx (readonly_mem_analyze ricf_witness_ctx)
Proof
  rw[rma_sound_def]
  >- (gvs[ricf_witness_rma] >>
      `callee_fn = ricf_witness_callee` by
        (fs[ricf_witness_ctx_def] >>
         `~has_ret_instruction ricf_witness_main` by EVAL_TAC >>
         gvs[]) >>
      gvs[] >>
      qpat_x_assum `setup_callee ricf_witness_callee args1 s1 = SOME cs1`
        (mp_tac o MATCH_MP ricf_witness_callee_run_blocks) >>
      disch_then (qspecl_then [`fuel`, `ricf_witness_ctx`] mp_tac) >>
      qpat_x_assum `setup_callee ricf_witness_callee args2 s2 = SOME cs2`
        (mp_tac o MATCH_MP ricf_witness_callee_run_blocks) >>
      disch_then (qspecl_then [`fuel`, `ricf_witness_ctx`] mp_tac) >>
      Cases_on `fuel` >- simp[callee_return_rel_def] >>
      `LENGTH args2 = LENGTH args1` by fs[rma_args_ok_def] >>
      Cases_on `args1` >> Cases_on `args2` >> gvs[callee_return_rel_def] >>
      rpt strip_tac >> gvs[callee_return_rel_def] >>
      `rma_arg_pair_ok (FEMPTY |+ ("callee", [T]) |+ ("main", []))
         ricf_witness_callee.fn_name dst_addr src_addr sz 0 h h'` by
        (fs[rma_args_ok_def] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      `ricf_witness_callee.fn_name = "callee" /\
       rma_is_readonly (FEMPTY |+ ("callee", [T]) |+ ("main", [])) "callee" 0 = T` by
        EVAL_TAC >>
      gvs[rma_arg_pair_ok_def]
      >- (irule (GSYM mload_copy_fwd_state_rel_disjoint) >>
          qexistsl_tac [`dst_addr`, `src_addr`, `sz`] >> simp[])
      >- (irule (GSYM mload_copy_fwd_state_rel_cross) >>
          qexists_tac `sz` >> simp[]))
  >- (fs[ricf_witness_ctx_def] >> gvs[]
      >- (`EVERY (\i. i.inst_opcode <> MCOPY) bb0.bb_instructions` by
            (gvs[ricf_witness_callee_def, mk_raw_function_def] >> EVAL_TAC) >>
          `bb1 = bb0` by metis_tac[icf_mcopy_noped_no_mcopy] >>
          metis_tac[icf_fwd_step_has_mcopy])
      >- (`icf_mcopy_noped ricf_witness_bb0 bb1` by
            (qpat_x_assum `icf_mcopy_noped _ bb1` mp_tac >>
             simp[GSYM ricf_witness_bb0_def]) >>
          qpat_x_assum `icf_fwd_step _ _ _ _ _ _ _` mp_tac >>
          simp[GSYM ricf_witness_ctx_def] >> strip_tac >>
          drule_all ricf_witness_main_fwd_step_eq >> strip_tac >> gvs[] >>
          `s_phi = s /\ phi_prefix_length ricf_witness_bb0.bb_instructions = 0` by
            gvs[ricf_witness_bb0_def, eval_phis_def, phi_prefix_length_def,
                mk_inst_def] >>
          gvs[] >>
          drule prefix_steps_3_from_0 >>
          simp[ricf_witness_bb0_def, get_instruction_def] >> strip_tac >>
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
          simp[ricf_witness_bb0_def, eval_operand_def, lookup_var_def] >>
          conj_tac
          >- (rpt strip_tac >>
              `j = 4 \/ j = 5 \/ j = 6` by decide_tac >> gvs[])
          >- (rpt strip_tac >>
              `j = 4 \/ j = 5 \/ j = 6` by decide_tac >> gvs[]
              >- (simp[ricf_witness_bb0_def, ricf_witness_bb1_def,
                       icf_suffix_inst_rel_def, is_terminator_def,
                       icf_invoke_step_rel_def, decode_invoke_def, mk_inst_def,
                       eval_operands_def, eval_operand_def, lookup_var_def,
                       rma_args_ok_def, rma_arg_pair_ok_def,
                       GSYM ricf_witness_ctx_def, ricf_witness_rma] >>
                  conj_tac
                  >- (simp[ricf_witness_ctx_def, lookup_function_def, FIND_thm,
                           ricf_witness_callee_def, mk_raw_function_def] >>
                      EVAL_TAC)
                  >- (`rma_is_readonly
                         (FEMPTY |+ ("callee", [T]) |+ ("main", []))
                         "callee" 0 = T` by EVAL_TAC >>
                      simp[]))
              >- simp[ricf_witness_bb0_def, ricf_witness_bb1_def,
                      icf_suffix_inst_rel_def, is_terminator_def,
                      step_inst_base_sstore_copy_fwd_state_rel]
              >- simp[ricf_witness_bb0_def, ricf_witness_bb1_def,
                      icf_suffix_inst_rel_def, is_terminator_def,
                      step_inst_base_stop_copy_fwd_state_rel])))
QED

Theorem ricf_witness_wf:
  o1_ctx_shape ricf_witness_ctx /\
  EVERY wf_ssa ricf_witness_ctx.ctx_functions /\
  EVERY ricf_full_alloca_copies ricf_witness_ctx.ctx_functions /\
  EVERY ricf_no_derived_mutable_sibling ricf_witness_ctx.ctx_functions /\
  rma_sound ricf_witness_ctx (readonly_mem_analyze ricf_witness_ctx)
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
  >- simp[ricf_witness_rma_sound]
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
