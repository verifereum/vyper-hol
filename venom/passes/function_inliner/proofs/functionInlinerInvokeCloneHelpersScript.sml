(*
 * Function Inliner — INVOKE+Clone Case
 *
 * Infrastructure for proving clone_block_sim for callee blocks
 * after clone+rewrite, and the full INVOKE+clone case composition.
 *)

Theory functionInlinerInvokeCloneHelpers
Ancestors
  functionInlinerCallSimPhi functionInlinerCallSimHelpers
  functionInlinerPrevBBMap
  functionInlinerInline functionInlinerDefs functionInlinerSim
  functionInlinerFresh functionInlinerCloneSim functionInlinerStepClone
  functionInlinerCalleeSim functionInlinerCloneExec
  functionInlinerCloneNp
  functionInlinerBlockSplit functionInlinerBridge
  functionInlinerSuffixSim
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory wordsTheory indexedListsTheory

open functionInlinerCallSimHelpersTheory functionInlinerCallSimPhiTheory
     functionInlinerCallSimPhiStepTheory functionInlinerPrevBBMapTheory
     functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory functionInlinerFreshTheory
     functionInlinerCalleeSimTheory functionInlinerCloneNpTheory
     functionInlinerCloneExecTheory functionInlinerBlockSplitTheory
     functionInlinerBridgeTheory functionInlinerSuffixSimTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory

(* Prevent simp/fs from expanding these definitions automatically.
   They are biconditionals in the simpset and cause matching failures
   when used as antecedents in step simulation lemmas. *)
val _ = temp_delsimps ["clone_rel_np_def", "shared_globals_np_def"]

(* MAPi lemmas from indexedListsTheory — bring into scope *)
val LENGTH_MAPi = indexedListsTheory.LENGTH_MAPi
val EL_MAPi = indexedListsTheory.EL_MAPi

(* ================================================================
   PARAM ordering predicate
   ================================================================ *)

Definition params_sequential_def:
  params_sequential [] (start_idx : num) = T /\
  params_sequential (inst::rest) start_idx =
    if inst.inst_opcode = PARAM then
      (inst.inst_operands = [Lit (n2w start_idx)] /\
       start_idx < dimword (:256) /\
       params_sequential rest (start_idx + 1))
    else params_sequential rest start_idx
End

(* Count PARAMs in instruction list *)
Definition count_params_def:
  count_params [] = 0n /\
  count_params (inst::rest) =
    (if inst.inst_opcode = PARAM then 1 + count_params rest
     else count_params rest)
End

(* ================================================================
   params_sequential at position k gives operand = count_params(TAKE k)
   ================================================================ *)

Theorem params_sequential_el:
  !insts start_idx k.
    params_sequential insts start_idx /\
    k < LENGTH insts /\
    (EL k insts).inst_opcode = PARAM ==>
    (EL k insts).inst_operands = [Lit (n2w (start_idx + count_params (TAKE k insts)))] /\
    start_idx + count_params (TAKE k insts) < dimword (:256)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `k`
  >- (
    fs[params_sequential_def, count_params_def]
  )
  >- (
    rename1 `SUC n < SUC (LENGTH insts)` >>
    fs[params_sequential_def] >>
    Cases_on `h.inst_opcode = PARAM` >> fs[]
    >- (
      first_x_assum (qspecl_then [`start_idx + 1`, `n`] mp_tac) >>
      simp[] >> strip_tac >>
      ONCE_REWRITE_TAC[count_params_def] >> simp[]
    )
    >- (
      first_x_assum (qspecl_then [`start_idx`, `n`] mp_tac) >>
      simp[] >> strip_tac >>
      ONCE_REWRITE_TAC[count_params_def] >> simp[]
    )
  )
QED

(* clone_instruction preserves opcode => count_params preserved under MAP *)
Theorem count_params_clone:
  !insts prefix labels.
    count_params (MAP (clone_instruction prefix labels) insts) =
    count_params insts
Proof
  Induct >> simp[count_params_def, clone_instruction_def]
QED

(* count_params of TAKE also preserved under MAP clone *)
Theorem count_params_take_clone:
  !insts prefix labels k.
    count_params (TAKE k (MAP (clone_instruction prefix labels) insts)) =
    count_params (TAKE k insts)
Proof
  Induct >> simp[count_params_def] >> rpt gen_tac >>
  Cases_on `k` >> simp[count_params_def, clone_instruction_def]
QED

(* count_params (TAKE k) < count_params when EL k is PARAM *)
Theorem count_params_take_le:
  !insts k. k <= LENGTH insts ==>
    count_params (TAKE k insts) <= count_params insts
Proof
  Induct >> simp[count_params_def] >> rpt gen_tac >>
  Cases_on `k` >> simp[count_params_def] >>
  strip_tac >> ONCE_REWRITE_TAC[count_params_def] >>
  Cases_on `h.inst_opcode = PARAM` >> simp[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem count_params_take_lt:
  !insts k.
    k < LENGTH insts /\
    (EL k insts).inst_opcode = PARAM ==>
    count_params (TAKE k insts) < count_params insts
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `k` >> fs[]
  >- (ONCE_REWRITE_TAC[count_params_def] >> simp[])
  >- (
    ONCE_REWRITE_TAC[count_params_def] >>
    Cases_on `h.inst_opcode = PARAM` >> simp[] >>
    first_x_assum (qspec_then `n` mp_tac) >> simp[]
  )
QED

(* ================================================================
   Structural: rewrite_inline_insts on non-PARAM/non-RET = clone only
   ================================================================ *)

Theorem rewrite_normal_inst:
  !invoke_ops invoke_outs rl inst pi.
    inst.inst_opcode <> PARAM /\ inst.inst_opcode <> RET ==>
    rewrite_inline_inst invoke_ops invoke_outs rl inst pi = ([inst], pi)
Proof
  simp[rewrite_inline_inst_def]
QED

(* ================================================================
   Step-level PARAM simulation
   ================================================================

   Callee runs: step_inst_base PARAM sc
     -> reads sc.vs_params[w2n (n2w pi)] -> update_var out val sc
   Clone runs: step_inst_base ASSIGN sd
     -> eval_operand (EL pi invoke_ops) sd -> update_var (pfx++out) val sd
*)

Theorem param_step_sim:
  !inst prefix labels invoke_ops args pi sc sd out.
    inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit (n2w pi)] /\
    inst.inst_outputs = [out] /\
    pi < dimword (:256) /\
    clone_rel_np prefix labels sc sd /\
    pi < LENGTH invoke_ops /\
    pi < LENGTH args /\
    pi < LENGTH sc.vs_params /\
    eval_operand (EL pi invoke_ops) sd = SOME (EL pi args) /\
    EL pi sc.vs_params = EL pi args /\
    ~is_label_op (EL pi invoke_ops)
    ==>
    ?sc' sd'.
      step_inst_base inst sc = OK sc' /\
      step_inst_base
        (<| inst_id := inst.inst_id;
            inst_opcode := ASSIGN;
            inst_operands := [EL pi invoke_ops];
            inst_outputs := [STRCAT prefix out] |>) sd =
      OK sd' /\
      clone_rel_np prefix labels sc' sd'
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, w2n_n2w, exec_pure1_def] >>
  gvs[] >> irule update_var_clone_rel_np >> simp[]
QED

(* ================================================================
   Structural: what rewrite_inline_inst produces for PARAM
   ================================================================ *)

Theorem rewrite_param_result:
  !invoke_ops invoke_outs rl inst pi.
    inst.inst_opcode = PARAM /\
    pi < LENGTH invoke_ops ==>
    rewrite_inline_inst invoke_ops invoke_outs rl inst pi =
      ([inst with <| inst_opcode := ASSIGN;
                     inst_operands :=
                       [if is_label_op (EL pi invoke_ops)
                        then Lit 0w
                        else EL pi invoke_ops] |>],
       pi + 1)
Proof
  simp[rewrite_inline_inst_def, LET_THM]
QED

(* ================================================================
   Structural: clone_instruction then rewrite for PARAM
   ================================================================ *)

Theorem clone_rewrite_param:
  !prefix labels invoke_ops invoke_outs rl inst pi.
    inst.inst_opcode = PARAM /\
    pi < LENGTH invoke_ops ==>
    rewrite_inline_inst invoke_ops invoke_outs rl
      (clone_instruction prefix labels inst) pi =
      ([<| inst_id := inst.inst_id;
           inst_opcode := ASSIGN;
           inst_operands :=
             [if is_label_op (EL pi invoke_ops) then Lit 0w
              else EL pi invoke_ops];
           inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>],
       pi + 1)
Proof
  rpt strip_tac >>
  simp[clone_instruction_def, rewrite_inline_inst_def, LET_THM] >>
  simp[instruction_component_equality, MAP_EQ_f]
QED

(* ================================================================
   setup_callee under shared_globals_np produces equal states
   ================================================================ *)

Theorem setup_callee_shared_globals_np:
  !fn args sc sd.
    shared_globals_np sc sd ==>
    setup_callee fn args sc = setup_callee fn args sd
Proof
  rw[setup_callee_def, shared_globals_np_def,
     venom_state_component_equality]
QED

(* ================================================================
   merge_callee_state preserves clone_rel_np
   ================================================================

   merge copies 7 fields (memory, transient, accounts, returndata,
   logs, immutables, allocas) from callee result. All other fields
   come from the caller.

   Since callee results are identical (same function, same args),
   shared_globals_np is preserved through merge.
*)

Theorem merge_callee_clone_rel_np:
  !prefix labels sc sd callee_result.
    clone_rel_np prefix labels sc sd ==>
    clone_rel_np prefix labels
      (merge_callee_state sc callee_result)
      (merge_callee_state sd callee_result)
Proof
  rw[clone_rel_np_def, merge_callee_state_def, shared_globals_np_def,
     lookup_var_def]
QED

(* ================================================================
   bind_outputs preserves clone_rel_np
   ================================================================ *)

Theorem bind_outputs_clone_rel_np:
  !prefix labels sc sd outs vals.
    clone_rel_np prefix labels sc sd /\
    LENGTH outs = LENGTH vals ==>
    ?sc' sd'.
      bind_outputs outs vals sc = SOME sc' /\
      bind_outputs (MAP (STRCAT prefix) outs) vals sd = SOME sd' /\
      clone_rel_np prefix labels sc' sd'
Proof
  ntac 2 gen_tac >> Induct_on `outs`
  >- (Cases_on `vals` >> simp[bind_outputs_def])
  >> gen_tac >> Cases_on `vals` >> simp[] >> rpt strip_tac >>
  `bind_outputs (h::outs) (h'::t) sc =
   bind_outputs outs t (update_var h h' sc)` by simp[bind_outputs_def] >>
  `bind_outputs (STRCAT prefix h :: MAP (STRCAT prefix) outs) (h'::t) sd =
   bind_outputs (MAP (STRCAT prefix) outs) t
     (update_var (STRCAT prefix h) h' sd)` by simp[bind_outputs_def] >>
  simp[] >>
  first_x_assum irule >> simp[] >>
  irule update_var_clone_rel_np >> simp[]
QED

(* ================================================================
   INVOKE step under clone_rel_np
   ================================================================

   Both sides call the same function with the same args (via
   eval_operands_clone_np_some). setup_callee produces identical
   callee states (shared_globals_np => same inherited fields).
   run_function produces identical results. merge+bind preserves
   clone_rel_np.
*)

Theorem step_inst_invoke_clone_np:
  !prefix labels inst sc sd fuel ctx.
    clone_rel_np prefix labels sc sd /\
    inst.inst_opcode = INVOKE /\
    (case inst.inst_operands of
       Label l :: _ => ~MEM l labels | _ => T) /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands
    ==>
    case step_inst fuel ctx inst sc of
      OK sc' =>
        ?sd'. step_inst fuel ctx
                (clone_instruction prefix labels inst) sd = OK sd' /\
              clone_rel_np prefix labels sc' sd'
    | Halt sc' =>
        ?sd'. step_inst fuel ctx
                (clone_instruction prefix labels inst) sd = Halt sd' /\
              shared_globals_np sc' sd'
    | Abort a sc' =>
        ?sd'. step_inst fuel ctx
                (clone_instruction prefix labels inst) sd = Abort a sd' /\
              shared_globals_np sc' sd'
    | _ => T
Proof
  rpt strip_tac >>
  `shared_globals_np sc sd` by fs[clone_rel_np_def] >>
  (* Unfold step_inst for BOTH sides *)
  ONCE_REWRITE_TAC[step_inst_def] >>
  simp[clone_inst_opcode] >>
  (* decode_invoke: NONE case trivial, SOME case both sides agree *)
  Cases_on `decode_invoke inst`
  >- (fs[decode_invoke_def, clone_instruction_def] >>
      Cases_on `inst.inst_operands` >> fs[] >>
      Cases_on `h` >> fs[clone_operand_def]) >>
  PairCases_on `x` >> simp[] >>
  `decode_invoke (clone_instruction prefix labels inst) =
   SOME (x0, MAP (clone_operand prefix labels) x1)` by (
    fs[decode_invoke_def, clone_instruction_def] >>
    Cases_on `inst.inst_operands` >> fs[] >>
    Cases_on `h` >> fs[clone_operand_def] >>
    `~MEM x0 labels` by fs[] >> simp[]) >>
  simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee_fn` >>
  Cases_on `eval_operands x1 sc` >> simp[] >>
  rename1 `eval_operands x1 sc = SOME args` >>
  `eval_operands (MAP (clone_operand prefix labels) x1) sd = SOME args`
    by metis_tac[eval_operands_clone_np_some] >>
  simp[] >>
  Cases_on `setup_callee callee_fn args sc` >> simp[] >>
  rename1 `setup_callee callee_fn args sc = SOME callee_s` >>
  `setup_callee callee_fn args sd = SOME callee_s`
    by metis_tac[setup_callee_shared_globals_np] >>
  simp[] >>
  Cases_on `run_function fuel ctx callee_fn callee_s`
  >- (fs[] >> simp[])       (* OK — Error *)
  >- (fs[] >> metis_tac[shared_globals_np_def])  (* Halt *)
  >- (fs[] >> metis_tac[shared_globals_np_def])  (* Abort *)
  >- (simp[] >>   (* IntRet *)
      rename1 `IntRet ret_vals callee_s'` >>
      Cases_on `bind_outputs inst.inst_outputs ret_vals
                  (merge_callee_state sc callee_s')` >> simp[] >>
      rename1 `bind_outputs _ _ _ = SOME sc'` >>
      `LENGTH inst.inst_outputs = LENGTH ret_vals`
        by fs[bind_outputs_def, AllCaseEqs()] >>
      `clone_rel_np prefix labels
         (merge_callee_state sc callee_s')
         (merge_callee_state sd callee_s')`
        by metis_tac[merge_callee_clone_rel_np] >>
      drule_all bind_outputs_clone_rel_np >> strip_tac >>
      qexists_tac `sd'` >> REWRITE_TAC[ETA_THM] >> gvs[])
  >- simp[]       (* Error *)
QED

(* ================================================================
   Unified per-step simulation for non-RET instructions
   ================================================================

   For a callee instruction inst (non-RET, non-ALLOCA), step_inst on
   the original vs step_inst on the rewritten clone instruction preserves
   clone_rel_np. Handles PHI, PARAM, normal ops, and INVOKE.

   The rewritten instruction is the FIRST element of
   rewrite_inline_inst applied to clone_instruction.
*)

(* step_inst on non-INVOKE = step_inst_base *)
Theorem step_inst_non_invoke:
  !fuel ctx inst s.
    inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst s = step_inst_base inst s
Proof
  rpt strip_tac >> simp[step_inst_def]
QED

(* ================================================================
   run_block clone simulation (non-RET, induction on remaining insts)
   ================================================================

   For a block where no instruction is RET, stepping through the
   original callee block in lockstep with the rewritten clone block
   preserves clone_rel_np at each step.

   The rewritten block has the same length (1-to-1 instruction mapping).
*)

(* First, structural: rewrite_inline_insts on non-RET insts is 1-to-1 *)
Theorem rewrite_non_ret_singleton:
  !invoke_ops invoke_outs ret_lbl inst pidx.
    inst.inst_opcode <> RET ==>
    ?ri pidx'. rewrite_inline_inst invoke_ops invoke_outs ret_lbl inst pidx =
      ([ri], pidx')
Proof
  rpt strip_tac >>
  simp[rewrite_inline_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PARAM` >> simp[] >>
  Cases_on `pidx < LENGTH invoke_ops` >> simp[]
QED

Theorem rewrite_no_ret_length:
  !insts invoke_ops invoke_outs ret_lbl pidx insts' pidx'.
    rewrite_inline_insts invoke_ops invoke_outs ret_lbl insts pidx =
      (insts', pidx') /\
    EVERY (\inst. inst.inst_opcode <> RET) insts ==>
    LENGTH insts' = LENGTH insts
Proof
  Induct_on `insts` >> simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> strip_tac >>
  fs[rewrite_inline_insts_def] >>
  pairarg_tac >> fs[] >> pairarg_tac >> gvs[] >>
  drule rewrite_non_ret_singleton >>
  disch_then (qspecl_then [`invoke_ops`, `invoke_outs`, `ret_lbl`, `pidx`]
    strip_assume_tac) >>
  gvs[] >> res_tac >> simp[]
QED

(* ================================================================
   Helper lemmas for clone_block_sim
   ================================================================ *)

(* Updating inst_idx preserves clone_rel_np *)
Theorem clone_rel_np_inst_idx:
  !prefix labels sc sd n.
    clone_rel_np prefix labels sc sd ==>
    clone_rel_np prefix labels
      (sc with vs_inst_idx := n)
      (sd with vs_inst_idx := n)
Proof
  rw[clone_rel_np_def, shared_globals_np_def]
QED

(* step_inst_base preserves vs_params for non-PARAM non-ALLOCA *)
Theorem step_inst_base_preserves_params:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    inst.inst_opcode <> PARAM /\ inst.inst_opcode <> ALLOCA ==>
    s'.vs_params = s.vs_params
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s`, `s.vs_params`]
    step_inst_base_params_irrel) >>
  impl_tac >- simp[] >>
  `s with vs_params := s.vs_params = s` by
    simp[venom_state_component_equality] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  gvs[] >> simp[venom_state_component_equality]
QED

(* step_inst (INVOKE) preserves vs_params *)
Theorem foldl_update_var_preserves_params:
  !pairs s.
    (FOLDL (\s' (out,val). update_var out val s') s pairs).vs_params =
    s.vs_params
Proof
  Induct_on `pairs` >> simp[FOLDL] >>
  Cases >> simp[update_var_def]
QED

Theorem bind_outputs_preserves_params:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    s'.vs_params = s.vs_params
Proof
  rpt strip_tac >>
  gvs[bind_outputs_def, AllCaseEqs()] >>
  simp[foldl_update_var_preserves_params]
QED

Theorem step_inst_invoke_preserves_params:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = INVOKE ==>
    s'.vs_params = s.vs_params
Proof
  rpt strip_tac >> fs[step_inst_def] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> gvs[] >>
  Cases_on `eval_operands x1 s` >> gvs[] >>
  Cases_on `setup_callee x x' s` >> gvs[] >>
  Cases_on `run_function fuel ctx x x''` >> gvs[] >>
  fs[merge_callee_state_def, AllCaseEqs()] >>
  imp_res_tac bind_outputs_preserves_params >> gvs[]
QED

(* step_inst preserves vs_params for any opcode except ALLOCA *)
(* NOTE: For params preservation, use per-opcode helpers:
   - step_inst_base_preserves_params (non-PARAM, non-ALLOCA)
   - step_inst_invoke_preserves_params (INVOKE)
   - PARAM: step_inst_base_def + update_var_def directly *)

(* For non-RET non-PARAM: rewrite is identity, pidx unchanged *)
Theorem rewrite_inst_normal_singleton:
  !ops outs rl inst pidx inst_list pidx'.
    rewrite_inline_inst ops outs rl inst pidx = (inst_list, pidx') /\
    inst.inst_opcode <> RET /\ inst.inst_opcode <> PARAM ==>
    inst_list = [inst] /\ pidx' = pidx
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`ops`,`outs`,`rl`,`inst`,`pidx`] rewrite_normal_inst) >>
  simp[] >> gvs[]
QED

(* For PARAM: rewrite gives ASSIGN, pidx increments *)
Theorem rewrite_inst_param_singleton:
  !ops outs rl inst pidx inst_list pidx'.
    rewrite_inline_inst ops outs rl inst pidx = (inst_list, pidx') /\
    inst.inst_opcode = PARAM /\ pidx < LENGTH ops ==>
    ?ri. inst_list = [ri] /\ pidx' = pidx + 1
Proof
  rpt strip_tac >>
  gvs[rewrite_inline_inst_def, LET_THM]
QED

(* Combined: singleton + pidx step for any non-RET instruction *)
Theorem rewrite_inst_singleton_pidx:
  !ops outs rl inst pidx inst_list pidx'.
    rewrite_inline_inst ops outs rl inst pidx = (inst_list, pidx') /\
    inst.inst_opcode <> RET /\
    count_params [inst] + pidx <= LENGTH ops ==>
    ?ri. inst_list = [ri] /\ pidx' = pidx + count_params [inst]
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[count_params_def] >>
      imp_res_tac rewrite_inst_param_singleton >> gvs[])
  >- (imp_res_tac rewrite_inst_normal_singleton >>
      gvs[count_params_def])
QED

(* Helper: count_params of head is bounded by count_params of list *)
Theorem count_params_head_le:
  !h t. count_params [h] <= count_params (h::t)
Proof
  simp[count_params_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PARAM` >> simp[]
QED

(* Helper: count_params (h::t) splits as count_params [h] + count_params t *)
Theorem count_params_cons:
  !h t. count_params (h::t) = count_params [h] + count_params t
Proof
  simp[count_params_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PARAM` >> simp[]
QED

(* Prove by induction on k, avoiding Induct_on insts + Cases_on k dispatch *)
Theorem rewrite_no_ret_el_pidx:
  !k insts ops outs rl pidx insts' pidx'.
    rewrite_inline_insts ops outs rl insts pidx = (insts', pidx') /\
    EVERY (\i. i.inst_opcode <> RET) insts /\
    count_params insts + pidx <= LENGTH ops /\
    k < LENGTH insts ==>
    ?ri.
      rewrite_inline_inst ops outs rl (EL k insts)
        (pidx + count_params (TAKE k insts)) =
        ([ri], pidx + count_params (TAKE (SUC k) insts)) /\
      EL k insts' = ri
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  Cases_on `insts` >> fs[]
  >- (* k = 0 *)
   (fs[rewrite_inline_insts_def] >>
    pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
    `count_params [h] + pidx <= LENGTH ops` by
      (mp_tac (Q.SPECL [`h`, `t`] count_params_head_le) >> decide_tac) >>
    `?ri. inst_list = [ri] /\ pi' = pidx + count_params [h]` by
      metis_tac[rewrite_inst_singleton_pidx] >>
    gvs[count_params_def] >> metis_tac[])
  >- (* SUC k *)
   (fs[rewrite_inline_insts_def] >>
    pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
    `count_params [h] + pidx <= LENGTH ops` by
      (mp_tac (Q.SPECL [`h`, `t`] count_params_head_le) >> decide_tac) >>
    `?ri. inst_list = [ri] /\ pi' = pidx + count_params [h]` by
      metis_tac[rewrite_inst_singleton_pidx] >>
    gvs[] >>
    (* Normalize count_params (h::TAKE _ t) = count_params [h] + count_params (TAKE _ t) *)
    `!n. count_params (h :: TAKE n t) = count_params [h] + count_params (TAKE n t)` by
      simp[Once count_params_cons] >>
    fs[] >>
    (* Normalize pidx + (cp[h] + X) to (pidx + cp[h]) + X to match IH *)
    PURE_REWRITE_TAC[arithmeticTheory.ADD_ASSOC] >>
    `(pidx + count_params [h]) + count_params t <= LENGTH ops` by
      (mp_tac (Q.SPECL [`h`, `t`] count_params_cons) >> decide_tac) >>
    res_tac)
QED

(* EL correspondence for rewrite_inline_insts on non-RET lists:
   rewriting preserves positions, so the k-th rewritten instruction
   comes from rewrite_inline_inst applied to the k-th input. *)
Theorem rewrite_no_ret_el:
  !insts ops outs rl pidx insts' pidx' k.
    rewrite_inline_insts ops outs rl insts pidx = (insts', pidx') /\
    EVERY (\i. i.inst_opcode <> RET) insts /\
    k < LENGTH insts ==>
    ?ri pidx_k pidx_k'.
      rewrite_inline_inst ops outs rl (EL k insts) pidx_k =
        ([ri], pidx_k') /\
      EL k insts' = ri
Proof
  Induct_on `insts` >> simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> strip_tac >>
  fs[rewrite_inline_insts_def] >>
  pairarg_tac >> fs[] >> pairarg_tac >> gvs[] >>
  `?ri pidx''. rewrite_inline_inst ops outs rl h pidx = ([ri], pidx'')` by
    (irule rewrite_non_ret_singleton >> simp[]) >>
  gvs[] >>
  Cases_on `k`
  >- (simp[] >> metis_tac[])
  >- (
    simp[] >>
    first_x_assum (qspecl_then [`ops`,`outs`,`rl`,`pi'`,`rest_list`,`pi''`,`n`]
      mp_tac) >> simp[]
  )
QED

(* For non-PARAM non-RET instructions, rewrite preserves the instruction *)
Theorem rewrite_no_ret_normal_el:
  !insts ops outs rl pidx insts' pidx' k.
    rewrite_inline_insts ops outs rl insts pidx = (insts', pidx') /\
    EVERY (\i. i.inst_opcode <> RET) insts /\
    k < LENGTH insts /\
    (EL k insts).inst_opcode <> PARAM ==>
    EL k insts' = EL k insts
Proof
  rpt strip_tac >>
  drule_all rewrite_no_ret_el >> strip_tac >>
  mp_tac (Q.SPECL [`ops`, `outs`, `rl`, `EL k insts`, `pidx_k`]
    rewrite_normal_inst) >>
  impl_tac >- (fs[EVERY_EL]) >>
  strip_tac >> gvs[]
QED

(* ================================================================
   clone_block_sim: per-block simulation

   The proof structure mirrors run_block_clone (InlineScript) but
   uses clone_rel_np and handles PARAM->ASSIGN + RET->assigns+JMP.

   For non-RET blocks: step-by-step parallel execution (same length).
   For RET block: step-by-step up to RET, then assigns+JMP produces
   IntRet-equivalent state at ret_lbl.
   ================================================================ *)

(* Reusable: clone+rewrite preserves block length for non-RET blocks *)
Theorem rewrite_clone_block_length:
  !bb_clone bb prefix labels invoke_ops invoke_outs ret_lbl pidx.
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) pidx) /\
    EVERY (\inst. inst.inst_opcode <> RET) bb.bb_instructions ==>
    LENGTH bb_clone.bb_instructions = LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> RET)
    (MAP (clone_instruction prefix labels) bb.bb_instructions)` by
    simp[EVERY_MAP, clone_inst_opcode] >>
  Cases_on `rewrite_inline_insts invoke_ops invoke_outs ret_lbl
    (MAP (clone_instruction prefix labels) bb.bb_instructions) pidx` >>
  drule_all rewrite_no_ret_length >>
  fs[LENGTH_MAP]
QED

(* Tactic: given MEM inst insts in assumptions, extract P inst from
   EVERY P insts. Pattern must match the EVERY assumption exactly. *)
fun every_mem_tac pat =
  qpat_x_assum pat (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  disch_then (fn th => FIRST_ASSUM (mp_tac o MATCH_MP th)) >>
  simp[];

(* step_inst_base only returns IntRet for RET opcode *)
val exec_helper_defs = [exec_pure1_def, exec_pure2_def, exec_pure3_def,
  exec_read0_def, exec_read1_def, exec_write2_def,
  exec_ext_call_def, exec_delegatecall_def,
  exec_create_def, exec_alloca_def];

Theorem step_inst_base_IntRet_is_RET:
  step_inst_base inst s = IntRet vals v ==> inst.inst_opcode = RET
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  gvs exec_helper_defs >>
  gvs[AllCaseEqs()]
QED

(* step_inst for INVOKE never returns IntRet *)
Theorem step_inst_invoke_not_IntRet:
  !fuel ctx inst s vals v.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst s <> IntRet vals v
Proof
  rpt strip_tac >>
  fs[Once step_inst_def] >>
  gvs[AllCaseEqs()]
QED

(* Unified: step_inst never returns IntRet for non-RET instructions *)
Theorem step_inst_not_IntRet_non_RET:
  !fuel ctx inst s vals v.
    inst.inst_opcode <> RET ==>
    step_inst fuel ctx inst s <> IntRet vals v
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (imp_res_tac step_inst_invoke_not_IntRet >> fs[])
  >- (imp_res_tac step_inst_non_invoke >>
      fs[] >> imp_res_tac step_inst_base_IntRet_is_RET >> fs[])
QED

(* eval_operand preservation: after any non-terminator step where all
   outputs are prefixed, operands without prefix are unchanged.
   Generalizes to Normal, INVOKE, and PARAM->ASSIGN cases. *)
Theorem eval_op_step_prefixed_preserved:
  !fuel ctx inst sd sd' prefix op.
    step_inst fuel ctx inst sd = OK sd' /\
    ~is_terminator inst.inst_opcode /\
    EVERY (isPREFIX prefix) inst.inst_outputs /\
    (!v. op = Var v ==> ~isPREFIX prefix v) ==>
    eval_operand op sd' = eval_operand op sd
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[eval_operand_def]
  >- (
    rename1 `Var vname` >>
    `~MEM vname inst.inst_outputs` by (
      fs[EVERY_MEM] >> CCONTR_TAC >> fs[] >>
      res_tac >> fs[]) >>
    drule_all step_preserves_non_output_vars >> simp[lookup_var_def])
  >- (
    drule_all step_preserves_labels >> simp[])
QED

(* Corollary: clone_instruction outputs are all prefixed *)
Theorem clone_inst_outputs_prefixed:
  EVERY (isPREFIX prefix) (clone_instruction prefix labels inst).inst_outputs
Proof
  simp[clone_instruction_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> simp[isPREFIX_STRCAT]
QED

(* eval_operand ignores vs_inst_idx update *)
Theorem eval_operand_inst_idx:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* ================================================================
   Key abstraction: given a one-step simulation fact for the current
   instruction pair, derive clone_block_sim for the whole block.

   This separates run_block/clone_block_sim machinery from per-opcode
   simulation details. The main inductive proof applies this after
   establishing one-step simulation via the per-opcode helpers.
   ================================================================ *)

Theorem clone_block_sim_from_step:
  !prefix labels ret_lbl output_vars ctx fuel bb bb' sc sd inst inst'.
    get_instruction bb sc.vs_inst_idx = SOME inst /\
    get_instruction bb' sd.vs_inst_idx = SOME inst' /\
    sd.vs_inst_idx = sc.vs_inst_idx /\
    is_terminator inst'.inst_opcode = is_terminator inst.inst_opcode /\
    (case step_inst fuel ctx inst sc of
       OK sc' => ?sd'. step_inst fuel ctx inst' sd = OK sd' /\
         clone_rel_np prefix labels sc' sd' /\
         (~is_terminator inst.inst_opcode ==>
           clone_block_sim prefix labels ret_lbl output_vars ctx fuel bb bb'
             (sc' with vs_inst_idx := SUC sc.vs_inst_idx)
             (sd' with vs_inst_idx := SUC sd.vs_inst_idx))
     | Halt sc' => ?sd'. step_inst fuel ctx inst' sd = Halt sd' /\
         shared_globals_np sc' sd'
     | Abort a sc' => ?sd'. step_inst fuel ctx inst' sd = Abort a sd' /\
         shared_globals_np sc' sd'
     | IntRet _ _ => F
     | Error _ => T)
    ==>
    clone_block_sim prefix labels ret_lbl output_vars ctx fuel bb bb' sc sd
Proof
  rpt strip_tac >>
  simp[clone_block_sim_def] >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst sc` >> gvs[] >>
  (* After gvs: only OK case remains (Halt/Abort/IntRet/Error auto-solved).
     Existential stripped: sd', clone_rel_np, continuation in assumptions. *)
  Cases_on `is_terminator inst.inst_opcode` >> gvs[]
  (* non-terminator: apply clone_block_sim from continuation *)
  >~ [`~is_terminator _`]
  >- gvs[clone_block_sim_def]
  (* terminator: case on halted *)
  >> `v.vs_halted <=> sd'.vs_halted` by gvs[clone_rel_np_def] >>
  Cases_on `v.vs_halted` >> gvs[clone_rel_np_def]
QED

(* Helper: for non-PARAM instructions, the k-th element of the rewritten
   clone block equals clone_instruction applied to the k-th original. *)
Theorem non_param_clone_el_eq:
  !bb prefix labels invoke_ops invoke_outs ret_lbl k.
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode <> PARAM /\
    EVERY (\i. i.inst_opcode <> RET) bb.bb_instructions ==>
    EL k (FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0)) =
    clone_instruction prefix labels (EL k bb.bb_instructions)
Proof
  rpt strip_tac >>
  Cases_on `rewrite_inline_insts invoke_ops invoke_outs ret_lbl
    (MAP (clone_instruction prefix labels) bb.bb_instructions) 0` >>
  `k < LENGTH (MAP (clone_instruction prefix labels) bb.bb_instructions)` by
    simp[LENGTH_MAP] >>
  `(EL k (MAP (clone_instruction prefix labels) bb.bb_instructions)).inst_opcode
   <> PARAM` by simp[EL_MAP, clone_inst_opcode] >>
  `EVERY (\i. i.inst_opcode <> RET)
    (MAP (clone_instruction prefix labels) bb.bb_instructions)` by
    simp[EVERY_MAP, clone_inst_opcode] >>
  drule_all rewrite_no_ret_normal_el >>
  simp[EL_MAP]
QED


(* Unified PARAM step sim with case-expression shape.
   Matches the shape of step_inst_base_clone_np and step_inst_invoke_clone_np
   so the same proof skeleton works for all three opcode classes.

   The OK-case preconditions (args agreement, ~is_label_op) are conditional
   on pidx < LENGTH sc.vs_params, which is automatically derivable from OK. *)

(* PARAM OK implies pidx < LENGTH vs_params *)
Theorem param_ok_pidx_bound:
  !inst pidx sc sc'.
    inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit (n2w pidx)] /\
    pidx < dimword (:256) /\
    step_inst_base inst sc = OK sc' ==>
    pidx < LENGTH sc.vs_params
Proof
  simp[step_inst_base_def, w2n_n2w] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* PARAM step preserves vs_params *)
Theorem param_step_preserves_params:
  !inst pidx sc sc'.
    inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit (n2w pidx)] /\
    pidx < dimword (:256) /\
    step_inst_base inst sc = OK sc' ==>
    sc'.vs_params = sc.vs_params
Proof
  simp[step_inst_base_def, w2n_n2w] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> simp[update_var_def]
QED

(* PARAM step sim at step_inst_base level, with unconditional EL pidx invoke_ops.
   Used in clone_block_sim_no_ret_step's PARAM case. *)
Theorem step_inst_param_clone_np:
  !inst prefix labels invoke_ops args pidx sc sd.
    inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit (n2w pidx)] /\
    pidx < dimword (:256) /\
    clone_rel_np prefix labels sc sd /\
    pidx < LENGTH invoke_ops /\
    (pidx < LENGTH sc.vs_params ==>
       pidx < LENGTH args /\
       eval_operand (EL pidx invoke_ops) sd = SOME (EL pidx args) /\
       EL pidx sc.vs_params = EL pidx args /\
       ~is_label_op (EL pidx invoke_ops)) ==>
    case step_inst_base inst sc of
      OK sc' =>
        ?sd'. step_inst_base
                (<| inst_id := inst.inst_id;
                    inst_opcode := ASSIGN;
                    inst_operands := [EL pidx invoke_ops];
                    inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>)
                sd = OK sd' /\
              clone_rel_np prefix labels sc' sd'
    | _ => T
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, w2n_n2w] >>
  Cases_on `pidx < LENGTH sc.vs_params` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `pidx < LENGTH args` by fs[] >>
  fs[] >>
  simp[exec_pure1_def] >>
  irule update_var_clone_rel_np >> simp[]
QED

(* PARAM step sim at step_inst level, in the exact form one_step_block_sim needs.
   Handles Halt/Abort impossibility internally (PARAM only returns OK or Error). *)
Theorem step_inst_param_sim:
  !inst prefix labels invoke_ops args pidx sc sd ri fuel ctx.
    inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit (n2w pidx)] /\
    pidx < dimword (:256) /\
    clone_rel_np prefix labels sc sd /\
    pidx < LENGTH invoke_ops /\
    (pidx < LENGTH sc.vs_params ==>
       pidx < LENGTH args /\
       eval_operand (EL pidx invoke_ops) sd = SOME (EL pidx args) /\
       EL pidx sc.vs_params = EL pidx args /\
       ~is_label_op (EL pidx invoke_ops)) /\
    ri = <| inst_id := inst.inst_id; inst_opcode := ASSIGN;
            inst_operands :=
              [if is_label_op (EL pidx invoke_ops) then Lit 0w
               else EL pidx invoke_ops];
            inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>
    ==>
    (case step_inst fuel ctx inst sc of
       OK sc' => ?sd'. step_inst fuel ctx ri sd = OK sd' /\
                       clone_rel_np prefix labels sc' sd'
     | Halt sc' => ?sd'. step_inst fuel ctx ri sd = Halt sd' /\
                         shared_globals_np sc' sd'
     | Abort a sc' => ?sd'. step_inst fuel ctx ri sd = Abort a sd' /\
                            shared_globals_np sc' sd'
     | _ => T)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst sc = step_inst_base inst sc` by simp[step_inst_def] >>
  `step_inst fuel ctx ri sd = step_inst_base ri sd` by simp[step_inst_def] >>
  simp[] >>
  simp[step_inst_base_def, w2n_n2w] >>
  Cases_on `pidx < LENGTH sc.vs_params` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `pidx < LENGTH args` by fs[] >>
  fs[] >> simp[exec_pure1_def] >>
  irule update_var_clone_rel_np >> simp[]
QED

Theorem every_isPREFIX_map_strcat:
  !xs prefix. EVERY (isPREFIX prefix) (MAP (STRCAT prefix) xs)
Proof
  Induct >> simp[isPREFIX_THM, STRCAT_def]
QED

(* one_step_block_sim: The unified one-step-to-block-sim lemma.
   Given:
   - get_instruction facts for both blocks at current index
   - One-step simulation (case expression at step_inst level)
   - Continuation (IH: after OK step, clone_block_sim holds for next index)
   Produces: clone_block_sim for the whole block.

   Combines clone_block_sim_from_step + IntRet impossibility.
   Works for ALL opcode classes (Normal, INVOKE, PARAM). *)
Theorem one_step_block_sim:
  !fuel ctx inst inst' sc sd prefix labels ret_lbl output_vars bb bb'.
    get_instruction bb sc.vs_inst_idx = SOME inst /\
    get_instruction bb' sd.vs_inst_idx = SOME inst' /\
    sd.vs_inst_idx = sc.vs_inst_idx /\
    inst.inst_opcode <> RET /\
    is_terminator inst'.inst_opcode = is_terminator inst.inst_opcode /\
    (* Step sim at step_inst level *)
    (case step_inst fuel ctx inst sc of
       OK sc' => ?sd'. step_inst fuel ctx inst' sd = OK sd' /\
                       clone_rel_np prefix labels sc' sd'
     | Halt sc' => ?sd'. step_inst fuel ctx inst' sd = Halt sd' /\
                         shared_globals_np sc' sd'
     | Abort a sc' => ?sd'. step_inst fuel ctx inst' sd = Abort a sd' /\
                            shared_globals_np sc' sd'
     | _ => T) /\
    (* Continuation: for each OK result, the block sim holds *)
    (!sc' sd'.
       step_inst fuel ctx inst sc = OK sc' /\
       step_inst fuel ctx inst' sd = OK sd' /\
       clone_rel_np prefix labels sc' sd' ==>
       ~is_terminator inst.inst_opcode ==>
       clone_block_sim prefix labels ret_lbl output_vars ctx fuel bb bb'
         (sc' with vs_inst_idx := SUC sc.vs_inst_idx)
         (sd' with vs_inst_idx := SUC sc.vs_inst_idx))
    ==>
    clone_block_sim prefix labels ret_lbl output_vars ctx fuel bb bb' sc sd
Proof
  rpt strip_tac >>
  irule clone_block_sim_from_step >> simp[] >>
  Cases_on `step_inst fuel ctx inst sc`
  >- (fs[] >> qexists_tac `sd'` >> fs[] >>
      rpt strip_tac >> first_x_assum irule >> fs[])
  >- (fs[] >> gvs[])
  >- (fs[] >> gvs[])
  >- (mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `sc`]
        step_inst_not_IntRet_non_RET) >> simp[])
  >> fs[]
QED

(* eval preservation for any step with prefixed outputs: after stepping
   through an instruction with all-prefixed outputs, eval of non-prefixed
   operands is unchanged. Generalizes over clone_instruction AND PARAM
   rewrite instructions. *)
Theorem eval_prefixed_step_invoke_ops:
  !fuel ctx inst' sd sd' prefix invoke_ops.
    step_inst fuel ctx inst' sd = OK sd' /\
    ~is_terminator inst'.inst_opcode /\
    EVERY (isPREFIX prefix) inst'.inst_outputs /\
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops
    ==>
    !i. i < LENGTH invoke_ops ==>
      eval_operand (EL i invoke_ops) sd' = eval_operand (EL i invoke_ops) sd
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst'`,
    `sd`, `sd'`, `prefix`, `EL i invoke_ops`]
    eval_op_step_prefixed_preserved) >>
  simp[] >> disch_then irule >>
  fs[EVERY_EL] >> res_tac
QED



(* Extracted inductive step: debuggable with hol_state_at/hol_check_proof.
   The IH is an explicit hypothesis. The main theorem just does
   completeInduct_on + base case + irule this. *)
Theorem clone_block_sim_no_ret_step:
  (* IH: for smaller remaining instruction count, clone_block_sim holds *)
  (!fuel' ctx' bb' bb_clone' prefix' labels' invoke_ops' invoke_outs'
    ret_lbl' sc' sd' args'.
    LENGTH bb'.bb_instructions - sc'.vs_inst_idx <
      LENGTH bb.bb_instructions - sc.vs_inst_idx /\
    bb_clone'.bb_instructions =
      FST (rewrite_inline_insts invoke_ops' invoke_outs' ret_lbl'
        (MAP (clone_instruction prefix' labels') bb'.bb_instructions) 0) /\
    bb_clone'.bb_label = STRCAT prefix' bb'.bb_label /\
    clone_rel_np prefix' labels' sc' sd' /\
    sd'.vs_inst_idx = sc'.vs_inst_idx /\
    EVERY (\i. i.inst_opcode <> RET) bb'.bb_instructions /\
    bb_well_formed bb' /\
    sc'.vs_inst_idx <= LENGTH bb'.bb_instructions /\
    EVERY (\i. i.inst_opcode <> ALLOCA) bb'.bb_instructions /\
    EVERY (\i. EVERY (\op. !l. op = Label l ==> MEM l labels')
                      i.inst_operands) bb'.bb_instructions /\
    EVERY (\i. i.inst_opcode = INVOKE ==>
             case i.inst_operands of
               Label l :: _ => ~MEM l labels' | _ => T)
          bb'.bb_instructions /\
    params_sequential bb'.bb_instructions 0 /\
    (!i. i < LENGTH invoke_ops' /\ i < LENGTH args' ==>
         eval_operand (EL i invoke_ops') sd' = SOME (EL i args') /\
         EL i sc'.vs_params = EL i args') /\
    LENGTH args' = LENGTH sc'.vs_params /\
    LENGTH invoke_ops' >= LENGTH sc'.vs_params /\
    count_params bb'.bb_instructions <= LENGTH invoke_ops' /\
    (!i. i < LENGTH sc'.vs_params ==> ~is_label_op (EL i invoke_ops')) /\
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix' v) invoke_ops'
    ==>
    clone_block_sim prefix' labels' ret_lbl' invoke_outs' ctx' fuel'
      bb' bb_clone' sc' sd') /\
  (* Preconditions (same as clone_block_sim_no_ret minus n) *)
  sc.vs_inst_idx < LENGTH bb.bb_instructions /\
  bb_clone.bb_instructions =
    FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
  bb_clone.bb_label = STRCAT prefix bb.bb_label /\
  clone_rel_np prefix labels sc sd /\
  sd.vs_inst_idx = sc.vs_inst_idx /\
  EVERY (\inst. inst.inst_opcode <> RET) bb.bb_instructions /\
  bb_well_formed bb /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) bb.bb_instructions /\
  EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l labels)
                      inst.inst_operands)
        bb.bb_instructions /\
  EVERY (\inst. inst.inst_opcode = INVOKE ==>
           case inst.inst_operands of
             Label l :: _ => ~MEM l labels | _ => T)
        bb.bb_instructions /\
  params_sequential bb.bb_instructions 0 /\
  (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
       eval_operand (EL i invoke_ops) sd = SOME (EL i args) /\
       EL i sc.vs_params = EL i args) /\
  LENGTH args = LENGTH sc.vs_params /\
  LENGTH invoke_ops >= LENGTH sc.vs_params /\
  count_params bb.bb_instructions <= LENGTH invoke_ops /\
  (!i. i < LENGTH sc.vs_params ==> ~is_label_op (EL i invoke_ops)) /\
  EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops
  ==>
  clone_block_sim prefix labels ret_lbl invoke_outs ctx fuel
    bb bb_clone sc sd
Proof
  rpt strip_tac >>
  (* Establish the current instructions *)
  qabbrev_tac `k = sc.vs_inst_idx` >>
  `k < LENGTH bb.bb_instructions` by fs[Abbr `k`] >>
  qabbrev_tac `inst = EL k bb.bb_instructions` >>
  `get_instruction bb k = SOME inst` by
    simp[get_instruction_def, Abbr `inst`] >>
  (* Get the rewritten clone instructions *)
  `?insts' pidx'. rewrite_inline_insts invoke_ops invoke_outs ret_lbl
     (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
     (insts', pidx')` by metis_tac[PAIR] >>
  `bb_clone.bb_instructions = insts'` by fs[] >>
  `LENGTH insts' = LENGTH bb.bb_instructions` by
    metis_tac[rewrite_clone_block_length] >>
  (* Extract EVERY properties for the current instruction *)
  `inst.inst_opcode <> RET` by (
    `EVERY (\i. i.inst_opcode <> RET) bb.bb_instructions` by fs[] >>
    fs[EVERY_EL] >> first_x_assum (qspec_then `k` mp_tac) >>
    simp[Abbr `inst`]) >>
  `inst.inst_opcode <> ALLOCA` by (
    `EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions` by fs[] >>
    fs[EVERY_EL] >> first_x_assum (qspec_then `k` mp_tac) >>
    simp[Abbr `inst`]) >>
  `EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands` by (
    qpat_x_assum `EVERY (\i. EVERY _ i.inst_operands) _` mp_tac >>
    simp[EVERY_EL] >> disch_then (qspec_then `k` mp_tac) >>
    simp[Abbr `inst`]) >>
  `inst.inst_opcode = INVOKE ==>
     case inst.inst_operands of
       Label l :: _ => ~MEM l labels | _ => T` by (
    qpat_x_assum `EVERY (\i. i.inst_opcode = INVOKE ==> _) _` mp_tac >>
    simp[EVERY_EL] >> disch_then (qspec_then `k` mp_tac) >>
    simp[Abbr `inst`]) >>
  (* Case split by opcode *)
  Cases_on `inst.inst_opcode = PARAM`
  >- (
    (* PARAM case: clone-side instruction is a rewritten ASSIGN *)
    qabbrev_tac `pidx = count_params (TAKE k bb.bb_instructions)` >>
    `inst.inst_operands = [Lit (n2w pidx)] /\ pidx < dimword (:256)` by (
      mp_tac (Q.SPECL [`bb.bb_instructions`, `0`, `k`]
        params_sequential_el) >>
      simp[Abbr `inst`, Abbr `pidx`]) >>
    `pidx < count_params bb.bb_instructions` by
      (simp[Abbr `pidx`] >> irule count_params_take_lt >> simp[Abbr `inst`]) >>
    `pidx < LENGTH invoke_ops` by decide_tac >>
    (* Derive concrete form of EL k insts' via clone_rewrite_param *)
    `rewrite_inline_inst invoke_ops invoke_outs ret_lbl
       (clone_instruction prefix labels inst) pidx =
     ([<| inst_id := inst.inst_id; inst_opcode := ASSIGN;
          inst_operands :=
            [if is_label_op (EL pidx invoke_ops) then Lit 0w
             else EL pidx invoke_ops];
          inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>],
      pidx + 1)` by simp[clone_rewrite_param] >>
    (* Get EL k insts' = this record from rewrite_no_ret_el_pidx *)
    mp_tac (Q.SPECL [`k`,
      `MAP (clone_instruction prefix labels) bb.bb_instructions`,
      `invoke_ops`, `invoke_outs`, `ret_lbl`, `0`, `insts'`, `pidx'`]
      rewrite_no_ret_el_pidx) >>
    simp[LENGTH_MAP, EVERY_MAP, clone_inst_opcode,
         count_params_clone, count_params_take_clone] >>
    `count_params (TAKE k bb.bb_instructions) = pidx` by simp[Abbr `pidx`] >>
    ASM_REWRITE_TAC[EL_MAP] >>
    strip_tac >>
    (* ri is now the name for EL k insts' *)
    qabbrev_tac `ri = EL k insts'` >>
    `(MAP (clone_instruction prefix labels) bb.bb_instructions)❲k❳ =
     clone_instruction prefix labels inst` by
      fs[EL_MAP, LENGTH_MAP, Abbr `inst`] >>
    `rewrite_inline_inst invoke_ops invoke_outs ret_lbl
       (MAP (clone_instruction prefix labels) bb.bb_instructions)❲k❳ pidx =
     ([<| inst_id := inst.inst_id; inst_opcode := ASSIGN;
          inst_operands :=
            [if is_label_op (EL pidx invoke_ops) then Lit 0w
             else EL pidx invoke_ops];
          inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>],
      pidx + 1)` by fs[] >>
    `ri = <| inst_id := inst.inst_id; inst_opcode := ASSIGN;
             inst_operands :=
               [if is_label_op (EL pidx invoke_ops) then Lit 0w
                else EL pidx invoke_ops];
             inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>` by (
      qpat_x_assum `rewrite_inline_inst _ _ _ (MAP _ _)❲k❳ _ = ([ri], _)`
        mp_tac >>
      ASM_REWRITE_TAC[] >>
      strip_tac >> fs[]) >>
    `get_instruction bb_clone k = SOME ri` by
      simp[get_instruction_def, Abbr `ri`] >>
    (* Pre-establish guarded implication for step_inst_param_sim *)
    `pidx < LENGTH sc.vs_params ==>
       pidx < LENGTH args /\
       eval_operand (EL pidx invoke_ops) sd = SOME (EL pidx args) /\
       EL pidx sc.vs_params = EL pidx args /\
       ~is_label_op (EL pidx invoke_ops)` by (
      strip_tac >>
      qpat_x_assum `!i. i < LENGTH invoke_ops /\ i < LENGTH args ==> _`
        (qspec_then `pidx` mp_tac) >> simp[] >>
      qpat_x_assum `!i. i < LENGTH sc.vs_params ==> ~is_label_op _`
        (qspec_then `pidx` mp_tac) >> simp[]) >>
    (* Expand ri and apply one_step_block_sim *)
    qpat_x_assum `Abbrev (ri = _)` (K ALL_TAC) >>
    qpat_x_assum `ri = _` SUBST_ALL_TAC >>
    MATCH_MP_TAC one_step_block_sim >>
    qexistsl_tac [`inst`,
      `<|inst_id := inst.inst_id; inst_opcode := ASSIGN;
         inst_operands :=
           [if is_label_op (EL pidx invoke_ops) then Lit 0w
            else EL pidx invoke_ops];
         inst_outputs := MAP (STRCAT prefix) inst.inst_outputs|>`] >>
    simp[is_terminator_def] >>
    conj_tac
    >- (
      (* Step sim — inline the proof from step_inst_param_sim *)
      `step_inst fuel ctx inst sc = step_inst_base inst sc` by simp[step_inst_def] >>
      `step_inst fuel ctx
        <|inst_id := inst.inst_id; inst_opcode := ASSIGN;
          inst_operands :=
            [if is_label_op (EL pidx invoke_ops) then Lit 0w
             else EL pidx invoke_ops];
          inst_outputs := MAP (STRCAT prefix) inst.inst_outputs|> sd =
       step_inst_base
        <|inst_id := inst.inst_id; inst_opcode := ASSIGN;
          inst_operands :=
            [if is_label_op (EL pidx invoke_ops) then Lit 0w
             else EL pidx invoke_ops];
          inst_outputs := MAP (STRCAT prefix) inst.inst_outputs|> sd` by
        simp[step_inst_def] >>
      simp[] >>
      simp[step_inst_base_def, w2n_n2w] >>
      Cases_on `pidx < LENGTH sc.vs_params` >> simp[]
      >- (
        `pidx < LENGTH args` by fs[] >> fs[] >>
        Cases_on `inst.inst_outputs` >> simp[] >>
        Cases_on `t` >> simp[] >>
        simp[exec_pure1_def] >>
        irule update_var_clone_rel_np >> simp[])
      >> (
        Cases_on `inst.inst_outputs` >> simp[] >>
        Cases_on `t` >> simp[])
    ) >>
    (* Continuation *)
    suspend "param_cont"
  ) >>
  (* === Non-PARAM: use rewrite_no_ret_normal_el to get inst' directly === *)
  `EL k insts' = clone_instruction prefix labels inst` by (
    mp_tac (Q.SPECL [`MAP (clone_instruction prefix labels) bb.bb_instructions`,
      `invoke_ops`, `invoke_outs`, `ret_lbl`, `0`, `insts'`, `pidx'`, `k`]
      rewrite_no_ret_normal_el) >>
    simp[EVERY_MAP, clone_inst_opcode, LENGTH_MAP, EL_MAP, Abbr `inst`]) >>
  `get_instruction bb_clone k =
     SOME (clone_instruction prefix labels inst)` by
    simp[get_instruction_def] >>
  (* Both INVOKE and Normal follow the same pattern:
     MATCH_MP_TAC one_step_block_sim, provide step sim + continuation.
     The continuation uses clone_step_continuation (after unabbrev k). *)
  MATCH_MP_TAC one_step_block_sim >>
  qexistsl_tac [`inst`, `clone_instruction prefix labels inst`] >>
  simp[clone_inst_opcode] >>
  conj_tac
  >- (
    (* Step sim case expression *)
    Cases_on `inst.inst_opcode = INVOKE`
    >- (
      mp_tac (Q.SPECL [`prefix`, `labels`, `inst`, `sc`, `sd`, `fuel`, `ctx`]
        step_inst_invoke_clone_np) >>
      simp[])
    >> (
      `!s. step_inst fuel ctx inst s = step_inst_base inst s` by
        simp[step_inst_def] >>
      `!s. step_inst fuel ctx (clone_instruction prefix labels inst) s =
           step_inst_base (clone_instruction prefix labels inst) s` by
        simp[step_inst_def, clone_inst_opcode] >>
      simp[] >>
      mp_tac (Q.SPECL [`prefix`, `labels`, `inst`, `sc`, `sd`]
        step_inst_base_clone_np) >>
      simp[])
  ) >>
  (* Continuation: eval preservation + clone_rel_np update + IH *)
  rpt strip_tac >>
  `sc'.vs_params = sc.vs_params` by (
    Cases_on `inst.inst_opcode = INVOKE`
    >- (imp_res_tac step_inst_invoke_preserves_params >> fs[])
    >> (imp_res_tac step_inst_non_invoke >> fs[] >>
        imp_res_tac step_inst_base_preserves_params >> fs[])) >>
  `!i. i < LENGTH invoke_ops ==>
    eval_operand (EL i invoke_ops)
      (sd' with vs_inst_idx := SUC sc.vs_inst_idx) =
    eval_operand (EL i invoke_ops) sd` by (
    rpt strip_tac >> simp[eval_operand_inst_idx] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`,
      `clone_instruction prefix labels inst`,
      `sd`, `sd'`, `prefix`, `invoke_ops`]
      eval_prefixed_step_invoke_ops) >>
    simp[clone_inst_opcode, clone_inst_outputs_prefixed] >>
    disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `clone_rel_np prefix labels
    (sc' with vs_inst_idx := SUC sc.vs_inst_idx)
    (sd' with vs_inst_idx := SUC sc.vs_inst_idx)` by
    (irule clone_rel_np_inst_idx >> simp[]) >>
  fs[Abbr `k`] >>
  first_x_assum MATCH_MP_TAC >>
  qexistsl_tac [`invoke_ops`, `args`] >>
  simp[] >>
  rpt conj_tac >> TRY decide_tac >> fs[]
QED

Resume clone_block_sim_no_ret_step[param_cont]:
  rpt strip_tac >>
  (* Name the clone-side instruction for reference *)
  qabbrev_tac `cinst = <|inst_id := inst.inst_id; inst_opcode := ASSIGN;
    inst_operands :=
      [if is_label_op (EL pidx invoke_ops) then Lit 0w
       else EL pidx invoke_ops];
    inst_outputs := MAP (STRCAT prefix) inst.inst_outputs|>` >>
  (* 1. params preservation: PARAM does update_var, doesn't touch vs_params *)
  `step_inst_base inst sc = OK sc'` by
    (`step_inst fuel ctx inst sc = step_inst_base inst sc` by
       (irule step_inst_non_invoke >> simp[]) >> fs[]) >>
  `sc'.vs_params = sc.vs_params` by
    (imp_res_tac param_step_preserves_params) >>
  (* 2. eval preservation: ASSIGN has prefixed outputs, is non-terminator *)
  `EVERY (isPREFIX prefix) cinst.inst_outputs` by
    simp[Abbr `cinst`, every_isPREFIX_map_strcat] >>
  `~is_terminator cinst.inst_opcode` by
    simp[Abbr `cinst`, is_terminator_def] >>
  `!i. i < LENGTH invoke_ops ==>
    eval_operand (EL i invoke_ops)
      (sd' with vs_inst_idx := SUC k) =
    eval_operand (EL i invoke_ops) sd` by (
    rpt strip_tac >> simp[eval_operand_inst_idx] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `cinst`,
      `sd`, `sd'`, `prefix`, `invoke_ops`]
      eval_prefixed_step_invoke_ops) >>
    simp[] >>
    disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  (* 3. clone_rel_np update *)
  `clone_rel_np prefix labels
    (sc' with vs_inst_idx := SUC k)
    (sd' with vs_inst_idx := SUC k)` by
    (irule clone_rel_np_inst_idx >> simp[]) >>
  (* 4. Apply IH *)
  fs[Abbr `k`] >>
  first_x_assum MATCH_MP_TAC >>
  qexistsl_tac [`invoke_ops`, `args`] >>
  simp[]
QED

Finalise clone_block_sim_no_ret_step

(* First prove for non-RET blocks (simpler, same instruction count).
   Induction on remaining instructions, mirroring run_block_clone. *)
Theorem clone_block_sim_no_ret:
  !n fuel ctx bb bb_clone prefix labels invoke_ops invoke_outs
   ret_lbl output_vars sc sd args.
    n = LENGTH bb.bb_instructions - sc.vs_inst_idx /\
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
    bb_clone.bb_label = STRCAT prefix bb.bb_label /\
    clone_rel_np prefix labels sc sd /\
    sd.vs_inst_idx = sc.vs_inst_idx /\
    EVERY (\inst. inst.inst_opcode <> RET) bb.bb_instructions /\
    bb_well_formed bb /\
    sc.vs_inst_idx <= LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) bb.bb_instructions /\
    EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l labels)
                        inst.inst_operands)
          bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = INVOKE ==>
             case inst.inst_operands of
               Label l :: _ => ~MEM l labels | _ => T)
          bb.bb_instructions /\
    params_sequential bb.bb_instructions 0 /\
    (!i. i < LENGTH invoke_ops /\ i < LENGTH args ==>
         eval_operand (EL i invoke_ops) sd = SOME (EL i args) /\
         EL i sc.vs_params = EL i args) /\
    LENGTH args = LENGTH sc.vs_params /\
    LENGTH invoke_ops >= LENGTH sc.vs_params /\
    count_params bb.bb_instructions <= LENGTH invoke_ops /\
    (!i. i < LENGTH sc.vs_params ==> ~is_label_op (EL i invoke_ops)) /\
    output_vars = invoke_outs /\
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops
    ==>
    clone_block_sim prefix labels ret_lbl output_vars ctx fuel
      bb bb_clone sc sd
Proof
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `sc.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (
    MATCH_MP_TAC clone_block_sim_no_ret_step >>
    conj_tac
    >- (
      (* IH: prove from completeInduct_on's IH *)
      rpt strip_tac >>
      `LENGTH bb'.bb_instructions - sc'.vs_inst_idx < n` by simp[] >>
      first_x_assum drule >>
      disch_then (qspecl_then [`fuel'`, `ctx'`, `bb'`, `bb_clone'`, `prefix'`,
        `labels'`, `invoke_ops'`, `invoke_outs'`, `ret_lbl'`, `invoke_outs'`,
        `sc'`, `sd'`, `args'`] mp_tac) >>
      simp[]
    ) >>
    simp[]
  ) >>
  (* Past end of block: n = 0 effectively *)
  `~(sc.vs_inst_idx < LENGTH bb.bb_instructions)` by decide_tac >>
  `LENGTH bb_clone.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[rewrite_clone_block_length] >>
  `run_block fuel ctx bb sc = Error "block not terminated"` by (
    ONCE_REWRITE_TAC[run_block_def] >> simp[get_instruction_def]) >>
  simp[clone_block_sim_def]
QED

(* ================================================================
   RET block structural lemmas
   ================================================================ *)

(* rewrite_inline_insts distributes over ++ *)
Theorem rewrite_inline_insts_append:
  !xs ys ops outs rlbl p.
    rewrite_inline_insts ops outs rlbl (xs ++ ys) p =
    let (l1, p1) = rewrite_inline_insts ops outs rlbl xs p in
    let (l2, p2) = rewrite_inline_insts ops outs rlbl ys p1 in
    (l1 ++ l2, p2)
Proof
  Induct >> simp[rewrite_inline_insts_def, pairTheory.UNCURRY] >>
  rpt gen_tac >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

(* Non-last instructions in a well-formed block are non-terminators *)
Theorem wf_non_last_non_terminator:
  !bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    i < PRE (LENGTH bb.bb_instructions) ==>
    ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  CCONTR_TAC >> fs[] >> res_tac >> decide_tac
QED

(* clone_instruction preserves opcode *)
Theorem clone_inst_opcode_eq:
  !prefix labels inst.
    (clone_instruction prefix labels inst).inst_opcode = inst.inst_opcode
Proof
  simp[clone_instruction_def]
QED

(* count_params distributes over append *)
Theorem count_params_append:
  !l1 l2. count_params (l1 ++ l2) = count_params l1 + count_params l2
Proof
  Induct >> simp[count_params_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PARAM` >> simp[count_params_def]
QED

(* FRONT has at most as many PARAMs as the full list *)
Theorem count_params_front_le:
  !l. l <> [] ==> count_params (FRONT l) <= count_params l
Proof
  rpt strip_tac >>
  `FRONT l ++ [LAST l] = l` by simp[APPEND_FRONT_LAST] >>
  `count_params l = count_params (FRONT l) + count_params [LAST l]` by
    metis_tac[count_params_append] >>
  decide_tac
QED

(* FRONT of well-formed block has all non-RET instructions *)
Theorem wf_front_no_ret:
  !bb. bb_well_formed bb /\ (LAST bb.bb_instructions).inst_opcode = RET ==>
    EVERY (\i. i.inst_opcode <> RET) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  fs[EVERY_EL, LENGTH_FRONT_CONS] >> rpt strip_tac >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  `n < LENGTH (h::t)` by simp[] >>
  `n < PRE (LENGTH (h::t))` by simp[] >>
  `~is_terminator (EL n (h::t)).inst_opcode` by
    metis_tac[wf_non_last_non_terminator] >>
  `(FRONT (h::t))❲n❳ = (h::t)❲n❳` by
    (irule EL_FRONT >> simp[]) >>
  gvs[is_terminator_def]
QED

(* FRONT of MAP = MAP of FRONT *)
Theorem front_map:
  !f xs. xs <> [] ==> FRONT (MAP f xs) = MAP f (FRONT xs)
Proof
  gen_tac >> Induct >> simp[] >>
  Cases_on `xs` >> simp[FRONT_DEF]
QED

(* For blocks with RET: rewritten instructions = front_rewrite ++ ret_rewrite *)
Theorem rewrite_ret_decompose:
  !bb ops outs rl prefix labels insts' pidx'.
    bb.bb_instructions <> [] /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') ==>
    ?front_insts' front_pidx' ret_inst.
      ret_inst = clone_instruction prefix labels (LAST bb.bb_instructions) /\
      rewrite_inline_insts ops outs rl
        (MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions)) 0 =
        (front_insts', front_pidx') /\
      insts' = front_insts' ++
        MAPi (\i rv. <| inst_id := 0; inst_opcode := ASSIGN;
                        inst_operands := [rv];
                        inst_outputs := [EL i outs] |>)
          ret_inst.inst_operands ++
        [ret_inst with <| inst_opcode := JMP;
                          inst_operands := [Label rl];
                          inst_outputs := [] |>]
Proof
  rpt strip_tac >>
  `MAP (clone_instruction prefix labels) bb.bb_instructions =
   MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions) ++
   [clone_instruction prefix labels (LAST bb.bb_instructions)]` by (
    `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
      metis_tac[APPEND_FRONT_LAST] >>
    pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
    simp[MAP_APPEND]) >>
  pop_assum (fn th =>
    qpat_x_assum `rewrite_inline_insts _ _ _ _ _ = _` (mp_tac o
      CONV_RULE (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV[th]))))) >>
  simp[rewrite_inline_insts_append] >>
  pairarg_tac >> simp[] >>
  (* The singleton [clone LAST] with opcode RET *)
  `(clone_instruction prefix labels (LAST bb.bb_instructions)).inst_opcode =
   RET` by simp[clone_instruction_def] >>
  simp[rewrite_inline_insts_def, rewrite_inline_inst_def] >>
  strip_tac >> gvs[]
QED

(* Length of front rewrite = LENGTH (FRONT bb.bb_instructions) *)
Theorem rewrite_front_length:
  !bb ops outs rl prefix labels front_insts' front_pidx'.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions)) 0 =
      (front_insts', front_pidx') ==>
    LENGTH front_insts' = LENGTH (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> RET)
     (MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions))` by (
    simp[EVERY_MAP] >>
    `EVERY (\i. i.inst_opcode <> RET) (FRONT bb.bb_instructions)` by
      metis_tac[wf_front_no_ret] >>
    fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
    simp[clone_instruction_def]) >>
  drule_all rewrite_no_ret_length >> simp[LENGTH_MAP]
QED

(* For k < PRE(LENGTH), EL k of full rewrite = EL k of front rewrite *)
Theorem rewrite_ret_el_prefix:
  !bb ops outs rl prefix labels insts' pidx' front_insts' front_pidx' k.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions)) 0 =
      (front_insts', front_pidx') /\
    k < LENGTH (FRONT bb.bb_instructions) ==>
    EL k insts' = EL k front_insts'
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all rewrite_ret_decompose >>
  strip_tac >> gvs[] >>
  `LENGTH front_insts' = LENGTH (FRONT bb.bb_instructions)` by
    metis_tac[rewrite_front_length] >>
  simp[EL_APPEND1]
QED

(* For k < LENGTH(FRONT bb), EL k of full rewrite = result of rewrite_inline_inst
   on the k-th instruction. Combines rewrite_ret_el_prefix + rewrite_no_ret_el_pidx
   on FRONT, bridging back to the full list. Eliminates FRONT boilerplate in callers. *)
Theorem rewrite_ret_el_pidx:
  !k bb ops outs rl prefix labels insts' pidx'.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') /\
    count_params bb.bb_instructions <= LENGTH ops /\
    k < LENGTH (FRONT bb.bb_instructions) ==>
    ?ri.
      rewrite_inline_inst ops outs rl
        (clone_instruction prefix labels (EL k bb.bb_instructions))
        (count_params (TAKE k bb.bb_instructions)) =
        ([ri], count_params (TAKE (SUC k) bb.bb_instructions)) /\
      EL k insts' = ri
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  (* Get FRONT-based rewrite *)
  `?front_insts' front_pidx'.
     rewrite_inline_insts ops outs rl
       (MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions)) 0 =
       (front_insts', front_pidx')` by metis_tac[PAIR] >>
  (* Bridge: EL k insts' = EL k front_insts' *)
  `EL k insts' = EL k front_insts'` by
    metis_tac[rewrite_ret_el_prefix] >>
  (* FRONT has no RET *)
  `EVERY (\i. i.inst_opcode <> RET) (FRONT bb.bb_instructions)` by
    metis_tac[wf_front_no_ret] >>
  (* count_params on FRONT <= LENGTH ops *)
  `count_params (FRONT bb.bb_instructions) <= LENGTH ops` by
    (imp_res_tac count_params_front_le >> decide_tac) >>
  (* Apply rewrite_no_ret_el_pidx on FRONT *)
  mp_tac (Q.SPECL [`k`,
    `MAP (clone_instruction prefix labels) (FRONT bb.bb_instructions)`,
    `ops`, `outs`, `rl`, `0`, `front_insts'`, `front_pidx'`]
    rewrite_no_ret_el_pidx) >>
  simp[LENGTH_MAP, EVERY_MAP, clone_inst_opcode,
       count_params_clone, count_params_take_clone] >>
  (* Bridge TAKE on FRONT to TAKE on full list *)
  `k < LENGTH bb.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >> decide_tac) >>
  `SUC k < LENGTH bb.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >> decide_tac) >>
  `TAKE k (FRONT bb.bb_instructions) = TAKE k bb.bb_instructions` by
    (irule TAKE_FRONT >> simp[]) >>
  `TAKE (SUC k) (FRONT bb.bb_instructions) = TAKE (SUC k) bb.bb_instructions` by
    (irule TAKE_FRONT >> simp[]) >>
  (* Bridge EL on FRONT to EL on full list *)
  `(FRONT bb.bb_instructions)❲k❳ = bb.bb_instructions❲k❳` by
    (irule FRONT_EL >> simp[]) >>
  simp[EL_MAP] >>
  strip_tac >>
  qexists_tac `ri` >> simp[]
QED

(* EL into the ASSIGN region of a rewritten RET block *)
Theorem rewrite_ret_el_assign:
  !bb ops outs rl prefix labels insts' pidx' j.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') /\
    j < LENGTH (clone_instruction prefix labels
                  (LAST bb.bb_instructions)).inst_operands ==>
    EL (LENGTH (FRONT bb.bb_instructions) + j) insts' =
      <| inst_id := 0; inst_opcode := ASSIGN;
         inst_operands :=
           [EL j (clone_instruction prefix labels
                    (LAST bb.bb_instructions)).inst_operands];
         inst_outputs := [EL j outs] |>
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all rewrite_ret_decompose >> strip_tac >>
  `LENGTH front_insts' = LENGTH (FRONT bb.bb_instructions)` by
    metis_tac[rewrite_front_length] >>
  (* Substitute insts' = front ++ MAPi ++ [jmp] AND ret_inst *)
  qpat_x_assum `ret_inst = _` SUBST_ALL_TAC >>
  qpat_x_assum `insts' = _` SUBST_ALL_TAC >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  `LENGTH front_insts' <= LENGTH (FRONT bb.bb_instructions) + j` by
    decide_tac >>
  simp[EL_APPEND2] >>
  (* Now: EL j (MAPi(..) ++ [jmp]) = ASSIGN(..) *)
  fs[clone_instruction_def] >>
  simp[EL_APPEND1, LENGTH_MAPi, EL_MAPi]
QED

(* EL into the JMP at the end of a rewritten RET block *)
Theorem rewrite_ret_el_jmp:
  !bb ops outs rl prefix labels insts' pidx'.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') ==>
    EL (LENGTH (FRONT bb.bb_instructions) +
        LENGTH (clone_instruction prefix labels
                  (LAST bb.bb_instructions)).inst_operands) insts' =
      (clone_instruction prefix labels (LAST bb.bb_instructions)) with
        <| inst_opcode := JMP; inst_operands := [Label rl];
           inst_outputs := [] |>
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all rewrite_ret_decompose >> strip_tac >>
  `LENGTH front_insts' = LENGTH (FRONT bb.bb_instructions)` by
    metis_tac[rewrite_front_length] >>
  qpat_x_assum `ret_inst = _` SUBST_ALL_TAC >>
  qpat_x_assum `insts' = _` SUBST_ALL_TAC >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  `LENGTH front_insts' <=
   LENGTH (FRONT bb.bb_instructions) +
   LENGTH (clone_instruction prefix labels
     (LAST bb.bb_instructions)).inst_operands` by decide_tac >>
  simp[EL_APPEND2, LENGTH_MAPi]
QED

(* Total length of a rewritten RET block *)
Theorem rewrite_ret_length:
  !bb ops outs rl prefix labels insts' pidx'.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') ==>
    LENGTH insts' = LENGTH (FRONT bb.bb_instructions) +
      LENGTH (clone_instruction prefix labels
                (LAST bb.bb_instructions)).inst_operands + 1
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all rewrite_ret_decompose >> strip_tac >>
  `LENGTH front_insts' = LENGTH (FRONT bb.bb_instructions)` by
    metis_tac[rewrite_front_length] >>
  qpat_x_assum `ret_inst = _` SUBST_ALL_TAC >>
  qpat_x_assum `insts' = _` (fn h => REWRITE_TAC[h]) >>
  simp[LENGTH_APPEND, LENGTH_MAPi]
QED

(* get_instruction into ASSIGN region of rewritten RET block *)
Theorem get_instruction_ret_assign:
  !bb bb_clone ops outs rl prefix labels insts' pidx' j.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') /\
    bb_clone.bb_instructions = insts' /\
    j < LENGTH (clone_instruction prefix labels
                  (LAST bb.bb_instructions)).inst_operands ==>
    get_instruction bb_clone (LENGTH (FRONT bb.bb_instructions) + j) = SOME
      <| inst_id := 0; inst_opcode := ASSIGN;
         inst_operands :=
           [EL j (clone_instruction prefix labels
                    (LAST bb.bb_instructions)).inst_operands];
         inst_outputs := [EL j outs] |>
Proof
  rpt strip_tac >>
  imp_res_tac rewrite_ret_length >>
  imp_res_tac rewrite_ret_el_assign >>
  fs[get_instruction_def, clone_instruction_def, LENGTH_MAP]
QED

(* get_instruction for JMP at end of rewritten RET block *)
Theorem get_instruction_ret_jmp:
  !bb bb_clone ops outs rl prefix labels insts' pidx'.
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    rewrite_inline_insts ops outs rl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
      (insts', pidx') /\
    bb_clone.bb_instructions = insts' ==>
    get_instruction bb_clone
      (LENGTH (FRONT bb.bb_instructions) +
       LENGTH (clone_instruction prefix labels
                 (LAST bb.bb_instructions)).inst_operands) = SOME
      ((clone_instruction prefix labels (LAST bb.bb_instructions)) with
        <| inst_opcode := JMP; inst_operands := [Label rl];
           inst_outputs := [] |>)
Proof
  rpt strip_tac >>
  imp_res_tac rewrite_ret_length >>
  imp_res_tac rewrite_ret_el_jmp >>
  fs[get_instruction_def, clone_instruction_def, LENGTH_MAP]
QED

(* Helper: update_var preserves eval_operand for prefixed Var operands
   when the output is not prefixed. *)
Theorem eval_operand_update_non_prefixed:
  !op out val v s prefix.
    EVERY (\v. ~isPREFIX prefix v) [out] /\
    (!v. op = Var v ==> isPREFIX prefix v) /\
    eval_operand op s = SOME v ==>
    eval_operand op (update_var out val s) = SOME v
Proof
  Cases_on `op` >> simp[eval_operand_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  (* s is prefixed, out is not prefixed → out ≠ s *)
  `out <> s` by (strip_tac >> gvs[]) >>
  simp[]
QED

(* Helper: update_var preserves shared_globals_np *)
Theorem update_var_shared_globals_np:
  !out val sc sd. shared_globals_np sc sd ==>
    shared_globals_np sc (update_var out val sd)
Proof
  simp[shared_globals_np_def, update_var_def]
QED

(* Helper: jump_to preserves shared_globals_np *)
Theorem jump_to_shared_globals_np:
  !lbl sc sd. shared_globals_np sc sd ==>
    shared_globals_np sc (jump_to lbl sd)
Proof
  simp[shared_globals_np_def, jump_to_def]
QED

(* Helper: ASSIGN step behavior *)
Theorem step_assign_behavior:
  !id op out s v.
    eval_operand op s = SOME v ==>
    step_inst_base
      <| inst_id := id; inst_opcode := ASSIGN;
         inst_operands := [op]; inst_outputs := [out] |> s =
    OK (update_var out v s)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, exec_pure1_def]
QED

(* eval_operands SOME implies element-wise eval_operand SOME *)
Theorem eval_operands_some_el:
  !ops st vals. eval_operands ops st = SOME vals ==>
    !j. j < LENGTH ops ==>
      eval_operand (EL j ops) st = SOME (EL j vals)
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `eval_operand h st` >> simp[] >>
  Cases_on `eval_operands ops st` >> simp[] >>
  strip_tac >> gvs[] >>
  Cases >> simp[]
QED

(* eval_operands SOME implies LENGTH equality *)
Theorem eval_operands_some_length:
  !ops st vals. eval_operands ops st = SOME vals ==>
    LENGTH vals = LENGTH ops
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `eval_operand h st` >> simp[] >>
  Cases_on `eval_operands ops st` >> simp[] >>
  strip_tac >> gvs[] >> res_tac >> simp[]
QED

(* Helper: running a sequence of ASSIGN instructions + JMP.
   Induction on the number of remaining assigns.
   Key invariant: shared_globals_np preserved, eval of remaining
   operands preserved (because outputs are non-prefixed, operands are prefixed).
   ALL_DISTINCT outs is needed so earlier writes aren't overwritten. *)
Theorem run_block_assigns_jmp:
  !n ret_ops outs vals fuel ctx bb sd start prefix ret_lbl sc jmp_id.
    n = LENGTH ret_ops /\
    (!j. j < LENGTH ret_ops ==>
      get_instruction bb (start + j) = SOME
        <| inst_id := 0; inst_opcode := ASSIGN;
           inst_operands := [EL j ret_ops]; inst_outputs := [EL j outs] |>) /\
    get_instruction bb (start + LENGTH ret_ops) = SOME
      <| inst_id := jmp_id; inst_opcode := JMP;
         inst_operands := [Label ret_lbl]; inst_outputs := [] |> /\
    sd.vs_inst_idx = start /\
    shared_globals_np sc sd /\
    ~sd.vs_halted /\
    (!j. j < LENGTH ret_ops ==>
      eval_operand (EL j ret_ops) sd = SOME (EL j vals)) /\
    LENGTH vals = LENGTH ret_ops /\
    EVERY (\v. ~isPREFIX prefix v) outs /\
    (!j. j < LENGTH ret_ops ==>
      !v. EL j ret_ops = Var v ==> isPREFIX prefix v) /\
    LENGTH outs >= LENGTH ret_ops /\
    ALL_DISTINCT outs
    ==>
    ?sd'. run_block fuel ctx bb sd = OK sd' /\
      sd'.vs_current_bb = ret_lbl /\
      ~sd'.vs_halted /\
      shared_globals_np sc sd' /\
      (!i. i < LENGTH vals /\ i < LENGTH outs ==>
           lookup_var (EL i outs) sd' = SOME (EL i vals)) /\
      (!x. ~MEM x outs ==> lookup_var x sd' = lookup_var x sd)
Proof
  Induct_on `n` >> rpt strip_tac
  >- (
    (* Base: 0 assigns, just the JMP *)
    gvs[] >>
    qexists_tac `jump_to ret_lbl sd` >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[step_inst_non_invoke, step_jmp_behavior, is_terminator_def,
         jump_to_def, lookup_var_def] >>
    fs[shared_globals_np_def])
  >>
  (* Step: peel off first ASSIGN, apply IH for the rest *)
  `LENGTH ret_ops = SUC n` by fs[] >>
  Cases_on `ret_ops` >> gvs[] >>
  Cases_on `vals` >> gvs[] >>
  Cases_on `outs` >> gvs[] >>
  fs[EVERY_DEF, ALL_DISTINCT] >>
  (* Peel first ASSIGN *)
  qpat_assum `!j. j < SUC _ ==> get_instruction _ _ = _`
    (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!j. j < SUC _ ==> eval_operand _ _ = _`
    (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[step_inst_non_invoke, is_terminator_def] >>
  mp_tac (Q.SPECL [`0`, `h`, `h''`, `sd`, `h'`] step_assign_behavior) >>
  simp[] >> disch_then (fn th => REWRITE_TAC[th]) >> simp[] >>
  (* Establish P5: eval_operand preserved through update_var for prefixed ops *)
  SUBGOAL_THEN
    ``!j. j < LENGTH t ==>
       eval_operand (EL j t) (update_var h'' h' sd) = SOME (EL j t')``
    assume_tac
  >- (
    rpt strip_tac >>
    qpat_assum `!j. j < SUC _ ==> eval_operand _ _ = _`
      (qspec_then `SUC j` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
    qpat_assum `!j. j < SUC _ ==> !v. _ = Var v ==> _`
      (qspec_then `SUC j` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
    Cases_on `EL j t` >>
    fs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
    COND_CASES_TAC >> fs[] >> gvs[]
  ) >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`t`, `t''`, `t'`, `fuel`, `ctx`,
    `bb`, `update_var h'' h' sd with vs_inst_idx := SUC sd.vs_inst_idx`,
    `prefix`, `ret_lbl`, `sc`, `jmp_id`] mp_tac) >>
  simp[eval_operand_inst_idx, update_var_def] >>
  (* Discharge IH antecedent via ML-level MP *)
  disch_then (fn ih =>
    let val ante = fst (dest_imp (concl ih)) in
    SUBGOAL_THEN ante (fn a => strip_assume_tac (MP ih a))
    end)
  >- (
    rpt conj_tac
    >- (rpt strip_tac >>
        qpat_assum `!j. j < SUC _ ==> get_instruction _ _ = _`
          (qspec_then `SUC j` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
        fs[arithmeticTheory.ADD_CLAUSES])
    >- fs[arithmeticTheory.ADD_CLAUSES]
    >- (gvs[shared_globals_np_def])
    >- (rpt strip_tac >>
        qpat_assum `!j. j < SUC _ ==> !v. _ = Var v ==> _`
          (qspec_then `SUC j` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
        fs[])
  ) >>
  (* IH conclusion now in assumptions *)
  qexists_tac `sd''` >> fs[lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `i` >> fs[]
QED

(* ================================================================
   RET helpers: compute step_inst_base and run_block for RET instructions
   ================================================================ *)

(* step_inst_base for RET: reduces to eval_operands case *)
Theorem step_inst_base_ret:
  inst.inst_opcode = RET ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      SOME ret_vals => IntRet ret_vals s
    | NONE => Error "ret: undefined return value"
Proof
  strip_tac >> fs[step_inst_base_def]
QED

(* run_block for RET with eval_operands = NONE → Error *)
Theorem run_block_ret_error:
  get_instruction bb k = SOME inst /\
  inst.inst_opcode = RET /\
  sc.vs_inst_idx = k /\
  eval_operands inst.inst_operands sc = NONE ==>
  run_block fuel ctx bb sc = Error "ret: undefined return value"
Proof
  strip_tac >> ONCE_REWRITE_TAC[run_block_def] >>
  ASM_REWRITE_TAC[] >> simp[is_terminator_def, step_inst_def] >>
  fs[step_inst_base_def]
QED

(* run_block for RET with eval_operands = SOME → IntRet *)
Theorem run_block_ret_intret:
  get_instruction bb k = SOME inst /\
  inst.inst_opcode = RET /\
  sc.vs_inst_idx = k /\
  eval_operands inst.inst_operands sc = SOME ret_vals ==>
  run_block fuel ctx bb sc = IntRet ret_vals sc
Proof
  strip_tac >> ONCE_REWRITE_TAC[run_block_def] >>
  ASM_REWRITE_TAC[] >> simp[is_terminator_def, step_inst_def] >>
  fs[step_inst_base_def]
QED

(* clone_operand producing Var implies prefix *)
Theorem clone_operand_var_isPREFIX:
  !prefix labels op v.
    clone_operand prefix labels op = Var v ==> isPREFIX prefix v
Proof
  Cases_on `op` >> simp[clone_operand_def, isPREFIX_STRCAT] >>
  rw[] >> gvs[isPREFIX_STRCAT]
QED

(* Temporarily commented out for build testing *)
(*
(* ================================================================
   run_block_clone_ret_suffix:
   Execute the ASSIGN+JMP suffix of a cloned RET block.
   Packages rewrite_ret_decompose + run_block_assigns_jmp
   with the EL_APPEND indexing done internally.
   ================================================================ *)
Theorem run_block_clone_ret_suffix_DISABLED:
  !prefix labels invoke_ops invoke_outs ret_lbl ctx fuel
   bb bb_clone sc sd ret_vals.
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
    bb_well_formed bb /\
    eval_operands
      (MAP (clone_operand prefix labels)
           (LAST bb.bb_instructions).inst_operands) sd = SOME ret_vals /\
    sd.vs_inst_idx = PRE (LENGTH bb.bb_instructions) /\
    shared_globals_np sc sd /\
    ~sd.vs_halted /\
    EVERY (\v. ~isPREFIX prefix v) invoke_outs /\
    ALL_DISTINCT invoke_outs /\
    LENGTH invoke_outs >= LENGTH (LAST bb.bb_instructions).inst_operands
    ==>
    ?sd'. run_block fuel ctx bb_clone sd = OK sd' /\
      sd'.vs_current_bb = ret_lbl /\
      ~sd'.vs_halted /\
      shared_globals_np sc sd' /\
      (!i. i < LENGTH (LAST bb.bb_instructions).inst_operands /\
           i < LENGTH invoke_outs ==>
           lookup_var (EL i invoke_outs) sd' = SOME (EL i ret_vals)) /\
      (!x. ~MEM x invoke_outs ==> lookup_var x sd' = lookup_var x sd)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `?insts' pidx'. rewrite_inline_insts invoke_ops invoke_outs ret_lbl
     (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
     (insts', pidx')` by metis_tac[PAIR] >>
  `bb_clone.bb_instructions = insts'` by fs[] >>
  qabbrev_tac `last_inst = LAST bb.bb_instructions` >>
  `(MAP (clone_instruction prefix labels) bb.bb_instructions) <> []` by
    simp[MAP_EQ_NIL] >>
  `(LAST (MAP (clone_instruction prefix labels) bb.bb_instructions)).inst_opcode
    = RET` by
    simp[LAST_MAP, clone_inst_opcode, Abbr `last_inst`] >>
  mp_tac (Q.SPECL [`bb`, `invoke_ops`, `invoke_outs`, `ret_lbl`,
    `prefix`, `labels`, `insts'`, `pidx'`] rewrite_ret_decompose) >>
  impl_tac >- fs[Abbr `last_inst`] >>
  strip_tac >>
  `LENGTH front_insts' = LENGTH (FRONT bb.bb_instructions)` by
    metis_tac[rewrite_front_length] >>
  qabbrev_tac `nfront = LENGTH front_insts'` >>
  `nfront = PRE (LENGTH bb.bb_instructions)` by
    fs[Abbr `nfront`, LENGTH_FRONT] >>
  (* Establish ret_ops = ret_inst.inst_operands and key facts *)
  `ret_inst = clone_instruction prefix labels last_inst` by fs[Abbr `last_inst`] >>
  `ret_inst.inst_operands = MAP (clone_operand prefix labels)
                                last_inst.inst_operands` by
    simp[clone_instruction_def] >>
  (* eval_operands on ret_ops *)
  `eval_operands ret_inst.inst_operands sd = SOME ret_vals` by fs[Abbr `last_inst`] >>
  `LENGTH ret_inst.inst_operands = LENGTH last_inst.inst_operands` by
    simp[LENGTH_MAP] >>
  imp_res_tac eval_operands_some_length >>
  imp_res_tac eval_operands_some_el >>
  `LENGTH ret_vals = LENGTH ret_inst.inst_operands` by fs[] >>
  (* bb_clone three-part decomposition *)
  `bb_clone.bb_instructions = front_insts' ++
     MAPi (\i rv. <| inst_id := 0; inst_opcode := ASSIGN;
                     inst_operands := [rv];
                     inst_outputs := [EL i invoke_outs] |>)
       ret_inst.inst_operands ++
     [ret_inst with <| inst_opcode := JMP;
        inst_operands := [Label ret_lbl]; inst_outputs := [] |>]`
    by fs[] >>
  `LENGTH (MAPi (\i rv. <| inst_id := 0; inst_opcode := ASSIGN;
              inst_operands := [rv]; inst_outputs := [EL i invoke_outs] |>)
          ret_inst.inst_operands) = LENGTH ret_inst.inst_operands`
    by simp[LENGTH_MAPi] >>
  (* P1: get_instruction for ASSIGN entries *)
  `!j. j < LENGTH ret_inst.inst_operands ==>
     get_instruction bb_clone (nfront + j) = SOME
       <| inst_id := 0; inst_opcode := ASSIGN;
          inst_operands := [EL j ret_inst.inst_operands];
          inst_outputs := [EL j invoke_outs] |>` by (
    rpt strip_tac >>
    simp[get_instruction_def, LENGTH_APPEND] >>
    `nfront + j < nfront + LENGTH ret_inst.inst_operands + 1` by decide_tac >>
    simp[] >>
    simp[EL_APPEND_EQN, Abbr `nfront`] >>
    simp[EL_MAPi]) >>
  (* P2: get_instruction for JMP *)
  `get_instruction bb_clone (nfront + LENGTH ret_inst.inst_operands) = SOME
     <| inst_id := 0; inst_opcode := JMP;
        inst_operands := [Label ret_lbl]; inst_outputs := [] |>` by (
    simp[get_instruction_def, LENGTH_APPEND] >>
    `nfront + LENGTH ret_inst.inst_operands <
     nfront + LENGTH ret_inst.inst_operands + 1` by decide_tac >>
    simp[] >>
    simp[EL_APPEND_EQN, Abbr `nfront`] >>
    simp[clone_instruction_def]) >>
  (* P3: isPREFIX for clone_operand vars *)
  `!j. j < LENGTH ret_inst.inst_operands ==>
     !v. EL j ret_inst.inst_operands = Var v ==> isPREFIX prefix v` by (
    rpt strip_tac >>
    `EL j (MAP (clone_operand prefix labels) last_inst.inst_operands) = Var v`
      by fs[] >>
    `j < LENGTH (MAP (clone_operand prefix labels) last_inst.inst_operands)`
      by fs[LENGTH_MAP] >>
    fs[EL_MAP] >>
    metis_tac[clone_operand_var_isPREFIX]) >>
  (* Apply run_block_assigns_jmp with ret_inst.inst_operands as ret_ops *)
  `sd.vs_inst_idx = nfront` by fs[Abbr `nfront`] >>
  mp_tac (Q.SPECL [`LENGTH ret_inst.inst_operands`,
    `ret_inst.inst_operands`, `invoke_outs`, `ret_vals`,
    `fuel`, `ctx`, `bb_clone`, `sd`, `nfront`, `prefix`, `ret_lbl`, `sc`]
    run_block_assigns_jmp) >>
  impl_tac >- fs[] >>
  strip_tac >>
  qexists_tac `sd'` >> fs[Abbr `last_inst`]
QED
*)
val _ = export_theory();
