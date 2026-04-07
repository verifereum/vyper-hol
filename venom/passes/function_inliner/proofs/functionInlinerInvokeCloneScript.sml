(*
 * Function Inliner — INVOKE+Clone Case (main theorems)
 *
 * clone_block_sim_ret (RET block case) and clone_block_sim_thm (combined).
 * Helpers are in functionInlinerInvokeCloneHelpersScript.sml.
 *)

Theory functionInlinerInvokeClone
Ancestors
  functionInlinerInvokeCloneHelpers
  functionInlinerRetSuffix

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory wordsTheory indexedListsTheory

open functionInlinerInvokeCloneHelpersTheory
     functionInlinerRetSuffixTheory
     functionInlinerCallSimHelpersTheory
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

(* Prevent simp/fs from expanding these definitions automatically. *)
val _ = temp_delsimps ["clone_rel_np_def", "shared_globals_np_def"]

(* MAPi lemmas from indexedListsTheory — bring into scope *)
val LENGTH_MAPi = indexedListsTheory.LENGTH_MAPi
val EL_MAPi = indexedListsTheory.EL_MAPi

(* ================================================================
   clone_block_sim_ret_step: One step of the RET block case.
   The IH is an EXPLICIT hypothesis, not from completeInduct_on.
   This mirrors clone_block_sim_no_ret_step for the RET case.
   ================================================================ *)
Theorem clone_block_sim_ret_step:
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
    ~sc'.vs_halted /\
    (LAST bb'.bb_instructions).inst_opcode = RET /\
    bb_well_formed bb' /\
    sc'.vs_inst_idx <= LENGTH bb'.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) bb'.bb_instructions /\
    EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l labels')
                        inst.inst_operands)
          bb'.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = INVOKE ==>
             case inst.inst_operands of
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
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix' v) invoke_ops' /\
    EVERY (\v. ~isPREFIX prefix' v) invoke_outs' /\
    ALL_DISTINCT invoke_outs' /\
    LENGTH invoke_outs' >= LENGTH (LAST bb'.bb_instructions).inst_operands
    ==>
    clone_block_sim prefix' labels' ret_lbl' invoke_outs' ctx' fuel'
      bb' bb_clone' sc' sd') /\
  (* Preconditions for the step case *)
  sc.vs_inst_idx < LENGTH bb.bb_instructions /\
  sc.vs_inst_idx <> PRE (LENGTH bb.bb_instructions) /\
  bb_clone.bb_instructions =
    FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
      (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
  bb_clone.bb_label = STRCAT prefix bb.bb_label /\
  clone_rel_np prefix labels sc sd /\
  sd.vs_inst_idx = sc.vs_inst_idx /\
  ~sc.vs_halted /\
  (LAST bb.bb_instructions).inst_opcode = RET /\
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
  EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops /\
  EVERY (\v. ~isPREFIX prefix v) invoke_outs /\
  ALL_DISTINCT invoke_outs /\
  LENGTH invoke_outs >= LENGTH (LAST bb.bb_instructions).inst_operands
  ==>
  clone_block_sim prefix labels ret_lbl invoke_outs ctx fuel
    bb bb_clone sc sd
Proof
  rpt strip_tac >>
  (* Establish the current instruction *)
  qabbrev_tac `k = sc.vs_inst_idx` >>
  `k < LENGTH bb.bb_instructions` by fs[Abbr `k`] >>
  qabbrev_tac `inst = EL k bb.bb_instructions` >>
  `get_instruction bb k = SOME inst` by
    simp[get_instruction_def, Abbr `inst`] >>
  (* Derive inst.inst_opcode <> RET from well-formedness *)
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `k < PRE (LENGTH bb.bb_instructions)` by decide_tac >>
  `k < LENGTH (FRONT bb.bb_instructions)` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >> decide_tac) >>
  `~is_terminator inst.inst_opcode` by (
    simp[Abbr `inst`] >> irule wf_non_last_non_terminator >> simp[]) >>
  `inst.inst_opcode <> RET` by
    (CCONTR_TAC >> gvs[is_terminator_def]) >>
  `inst.inst_opcode <> ALLOCA` by (
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
  (* Get rewrite data and apply rewrite_ret_el_pidx *)
  `?insts' pidx'. rewrite_inline_insts invoke_ops invoke_outs ret_lbl
     (MAP (clone_instruction prefix labels) bb.bb_instructions) 0 =
     (insts', pidx')` by metis_tac[PAIR] >>
  `bb_clone.bb_instructions = insts'` by fs[] >>
  `k < LENGTH insts'` by (
    mp_tac (Q.SPECL [`bb`, `invoke_ops`, `invoke_outs`, `ret_lbl`,
      `prefix`, `labels`, `insts'`, `pidx'`] rewrite_ret_length) >>
    simp[]) >>
  (* Use rewrite_ret_el_pidx to get the rewrite form *)
  mp_tac (Q.SPECL [`k`, `bb`, `invoke_ops`, `invoke_outs`, `ret_lbl`,
    `prefix`, `labels`, `insts'`, `pidx'`] rewrite_ret_el_pidx) >>
  simp[] >> strip_tac >>
  (* Case split PARAM vs non-PARAM *)
  Cases_on `inst.inst_opcode = PARAM`
  >- (
    (* PARAM case *)
    qabbrev_tac `pidx = count_params (TAKE k bb.bb_instructions)` >>
    `inst.inst_operands = [Lit (n2w pidx)] /\ pidx < dimword (:256)` by (
      mp_tac (Q.SPECL [`bb.bb_instructions`, `0`, `k`]
        params_sequential_el) >>
      simp[Abbr `inst`, Abbr `pidx`]) >>
    `pidx < count_params bb.bb_instructions` by
      (simp[Abbr `pidx`] >> irule count_params_take_lt >> simp[Abbr `inst`]) >>
    `pidx < LENGTH invoke_ops` by decide_tac >>
    (* Unify rewrite_ret_el_pidx with clone_rewrite_param *)
    `count_params (TAKE (SUC k) bb.bb_instructions) = pidx + 1` by (
      `TAKE (SUC k) bb.bb_instructions =
       SNOC (EL k bb.bb_instructions) (TAKE k bb.bb_instructions)` by
        (irule (GSYM SNOC_EL_TAKE) >> simp[]) >>
      pop_assum (fn th => REWRITE_TAC[th]) >>
      simp[SNOC_APPEND, count_params_append, Abbr `pidx`] >>
      simp[count_params_def, Abbr `inst`]) >>
    mp_tac (Q.SPECL [`prefix`, `labels`, `invoke_ops`, `invoke_outs`,
      `ret_lbl`, `inst`, `pidx`] clone_rewrite_param) >>
    simp[] >> strip_tac >>
    `EL k insts' = <| inst_id := inst.inst_id; inst_opcode := ASSIGN;
             inst_operands :=
               [if is_label_op (EL pidx invoke_ops) then Lit 0w
                else EL pidx invoke_ops];
             inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>` by
      fs[Abbr `pidx`] >>
    `get_instruction bb_clone k =
     SOME <| inst_id := inst.inst_id; inst_opcode := ASSIGN;
             inst_operands :=
               [if is_label_op (EL pidx invoke_ops) then Lit 0w
                else EL pidx invoke_ops];
             inst_outputs := MAP (STRCAT prefix) inst.inst_outputs |>` by
      simp[get_instruction_def] >>
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
    (* Apply one_step_block_sim *)
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
      (* Step sim *)
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
    (* PARAM continuation: eval preservation + clone_rel_np + IH *)
    suspend "param_cont"
  ) >>
  (* Non-PARAM case *)
  `insts'❲k❳ = clone_instruction prefix labels inst` by (
    qpat_x_assum `rewrite_inline_inst _ _ _ (clone_instruction _ _ _) _ = _` mp_tac >>
    simp[rewrite_inline_inst_def, clone_inst_opcode]) >>
  `get_instruction bb_clone k =
     SOME (clone_instruction prefix labels inst)` by
    simp[get_instruction_def] >>
  MATCH_MP_TAC one_step_block_sim >>
  qexistsl_tac [`inst`, `clone_instruction prefix labels inst`] >>
  simp[clone_inst_opcode] >>
  conj_tac
  >- (
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
  (* Non-PARAM continuation *)
  suspend "non_param_case"
QED

(* PARAM continuation: after PARAM step, derive eval preservation + IH *)
Resume clone_block_sim_ret_step[param_cont]:
  rpt strip_tac >>
  qabbrev_tac `cinst = <|inst_id := inst.inst_id; inst_opcode := ASSIGN;
    inst_operands :=
      [if is_label_op (EL pidx invoke_ops) then Lit 0w
       else EL pidx invoke_ops];
    inst_outputs := MAP (STRCAT prefix) inst.inst_outputs|>` >>
  `step_inst_base inst sc = OK sc'` by
    (`step_inst fuel ctx inst sc = step_inst_base inst sc` by
       (irule step_inst_non_invoke >> simp[]) >> fs[]) >>
  `sc'.vs_params = sc.vs_params` by
    (imp_res_tac param_step_preserves_params) >>
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
  `clone_rel_np prefix labels
    (sc' with vs_inst_idx := SUC k)
    (sd' with vs_inst_idx := SUC k)` by
    (irule clone_rel_np_inst_idx >> simp[]) >>
  (* Derive halted preservation for IH *)
  `~sc'.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  (* Apply IH — explicit hypothesis, so first_x_assum finds it *)
  fs[Abbr `k`] >>
  first_x_assum MATCH_MP_TAC >>
  qexistsl_tac [`invoke_ops`, `args`] >>
  simp[] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY decide_tac >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* Non-PARAM continuation *)
Resume clone_block_sim_ret_step[non_param_case]:
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
  (* Derive halted preservation for IH *)
  `~sc'.vs_halted` by metis_tac[step_preserves_halted] >>
  (* Apply IH — explicit hypothesis, so first_x_assum finds it *)
  fs[Abbr `k`] >>
  first_x_assum MATCH_MP_TAC >>
  qexistsl_tac [`invoke_ops`, `args`] >>
  simp[] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY decide_tac >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Finalise clone_block_sim_ret_step;

(* ================================================================
   clone_block_sim_ret: RET block case
   Proved by complete induction on remaining instructions.
   - Past end: Error (trivial)
   - At RET: base case (ret_base + ret_close)
   - Before RET: delegates to clone_block_sim_ret_step
   ================================================================ *)
Theorem clone_block_sim_ret:
  !n fuel ctx bb bb_clone prefix labels invoke_ops invoke_outs
   ret_lbl output_vars sc sd args.
    n = LENGTH bb.bb_instructions - sc.vs_inst_idx /\
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
    bb_clone.bb_label = STRCAT prefix bb.bb_label /\
    clone_rel_np prefix labels sc sd /\
    sd.vs_inst_idx = sc.vs_inst_idx /\
    ~sc.vs_halted /\
    (LAST bb.bb_instructions).inst_opcode = RET /\
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
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops /\
    EVERY (\v. ~isPREFIX prefix v) invoke_outs /\
    ALL_DISTINCT invoke_outs /\
    LENGTH invoke_outs >= LENGTH (LAST bb.bb_instructions).inst_operands
    ==>
    clone_block_sim prefix labels ret_lbl output_vars ctx fuel
      bb bb_clone sc sd
Proof
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `sc.vs_inst_idx >= LENGTH bb.bb_instructions`
  >- (
    (* Past end: Error *)
    `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
    `LENGTH bb.bb_instructions > 0` by (Cases_on `bb.bb_instructions` >> fs[]) >>
    `sc.vs_inst_idx = LENGTH bb.bb_instructions` by decide_tac >>
    `run_block fuel ctx bb sc = Error "block not terminated"` by (
      ONCE_REWRITE_TAC[run_block_def] >> simp[get_instruction_def]) >>
    simp[clone_block_sim_def]
  ) >>
  `sc.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  Cases_on `sc.vs_inst_idx = PRE (LENGTH bb.bb_instructions)`
  >- (
    (* At RET instruction — base case *)
    qabbrev_tac `k = sc.vs_inst_idx` >>
    qabbrev_tac `inst = EL k bb.bb_instructions` >>
    `get_instruction bb k = SOME inst` by
      simp[get_instruction_def, Abbr `inst`] >>
    `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
    `inst = LAST bb.bb_instructions` by (
      fs[Abbr `inst`, Abbr `k`] >> metis_tac[LAST_EL]) >>
    `inst.inst_opcode = RET` by fs[] >>
    `get_instruction bb sc.vs_inst_idx = SOME inst` by fs[Abbr `k`] >>
    Cases_on `eval_operands inst.inst_operands sc`
    >- (
      mp_tac run_block_ret_error >>
      fs[Abbr `k`] >> simp[clone_block_sim_def]
    ) >>
    rename1 `eval_operands inst.inst_operands sc = SOME ret_vals` >>
    `run_block fuel ctx bb sc = IntRet ret_vals sc` by
      (mp_tac run_block_ret_intret >> fs[Abbr `k`]) >>
    simp[clone_block_sim_def] >>
    `shared_globals_np sc sd` by fs[clone_rel_np_def] >>
    `~sd.vs_halted` by fs[clone_rel_np_def] >>
    `eval_operands
        (MAP (clone_operand prefix labels) inst.inst_operands) sd =
        SOME ret_vals` by
      metis_tac[eval_operands_clone_np_some] >>
    fs[Abbr `k`] >>
    imp_res_tac eval_operands_some_length >>
    (* Canonicalize: substitute inst → LAST bb.bb_instructions *)
    qpat_x_assum `inst = LAST _` (SUBST_ALL_TAC) >>
    mp_tac (Q.SPECL [`prefix`, `labels`, `invoke_ops`, `invoke_outs`,
      `ret_lbl`, `ctx`, `fuel`, `bb`, `bb_clone`, `sc`, `sd`, `ret_vals`]
      run_block_clone_ret_suffix) >>
    impl_tac >- (rpt strip_tac >> fs[]) >>
    strip_tac >>
    qexists_tac `sd'` >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> first_x_assum irule >> fs[]
  ) >>
  (* Step case — delegate to clone_block_sim_ret_step *)
  MATCH_MP_TAC clone_block_sim_ret_step >>
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
QED


(* Well-formed block + LAST not RET → all instructions are non-RET.
   Complement of wf_front_no_ret (which handles LAST = RET). *)
Theorem wf_every_non_ret[local]:
  !bb. bb_well_formed bb /\
       (LAST bb.bb_instructions).inst_opcode <> RET
       ==>
       EVERY (\inst. inst.inst_opcode <> RET) bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  Cases_on `n = PRE (LENGTH bb.bb_instructions)`
  >- (
    `EL n bb.bb_instructions = LAST bb.bb_instructions` by
      simp[LAST_EL] >>
    metis_tac[])
  >> (
    `n < PRE (LENGTH bb.bb_instructions)` by decide_tac >>
    `~is_terminator (EL n bb.bb_instructions).inst_opcode` by
      metis_tac[wf_non_last_non_terminator] >>
    pop_assum mp_tac >> simp[is_terminator_def])
QED

(* ================================================================
   clone_block_sim_thm: Combined RET + non-RET
   ================================================================ *)
Theorem clone_block_sim_thm:
  !prefix labels invoke_ops invoke_outs ret_lbl output_vars ctx fuel
   bb bb_clone sc sd args.
    bb_clone.bb_instructions =
      FST (rewrite_inline_insts invoke_ops invoke_outs ret_lbl
        (MAP (clone_instruction prefix labels) bb.bb_instructions) 0) /\
    bb_clone.bb_label = STRCAT prefix bb.bb_label /\
    clone_rel_np prefix labels sc sd /\
    sc.vs_inst_idx = 0 /\ sd.vs_inst_idx = 0 /\
    ~sc.vs_halted /\
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
    output_vars = invoke_outs /\
    EVERY (\op. !v. op = Var v ==> ~isPREFIX prefix v) invoke_ops /\
    EVERY (\v. ~isPREFIX prefix v) invoke_outs /\
    ALL_DISTINCT invoke_outs /\
    LENGTH invoke_outs >= LENGTH (LAST bb.bb_instructions).inst_operands
    ==>
    clone_block_sim prefix labels ret_lbl output_vars ctx fuel bb bb_clone sc sd
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode = RET`
  >- (
    mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
      `fuel`, `ctx`, `bb`, `bb_clone`, `prefix`, `labels`,
      `invoke_ops`, `invoke_outs`, `ret_lbl`, `invoke_outs`,
      `sc`, `sd`, `args`] clone_block_sim_ret) >>
    simp[]
  ) >>
  (* Non-RET case *)
  `EVERY (\inst. inst.inst_opcode <> RET) bb.bb_instructions` by
    metis_tac[wf_every_non_ret] >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
    `fuel`, `ctx`, `bb`, `bb_clone`, `prefix`, `labels`,
    `invoke_ops`, `invoke_outs`, `ret_lbl`, `invoke_outs`,
    `sc`, `sd`, `args`] clone_block_sim_no_ret) >>
  simp[]
QED

val _ = export_theory();
