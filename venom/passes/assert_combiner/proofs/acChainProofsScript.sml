(*
 * Assert Combiner Pass — general lemmas for the correctness proof
 *
 *   - ac_dfg_inv / ac_dfg_inv_local: the DFG's ISZERO and ASSIGN
 *     definitions hold of the runtime values, which bridges an ASSERT on
 *     an iszero chain to its source predicate;
 *   - run_insts and step lemmas for ASSERT, ISZERO, ASSIGN and OR;
 *   - the shape of ac_scan_block's merge candidates.
 *)

Theory acChainProofs
Ancestors
  acAbortRelProofs acBaseProofs assertCombinerDefs passSimulationDefs passSimulationProps
  stateEquiv stateEquivProps execEquivParamProps venomInstProps venomExecProps
  dfgAnalysisProps venomState venomWf venomExecSemantics venomExecProofs
  analysisSimDefs analysisSimProofsBase
  passTransform
Libs
  pred_setTheory arithmeticTheory listTheory rich_listTheory alistTheory

(* Normalize record constructor to record literal form.
   HOL4 treats instruction n o l l0 and <|inst_id:=n;...|> as
   syntactically different terms. This bridges them. *)
Theorem instruction_to_literal[simp]:
  instruction n op ops outs =
    <|inst_id := n; inst_opcode := op;
      inst_operands := ops; inst_outputs := outs|>
Proof
  simp[venomInstTheory.instruction_component_equality]
QED

(* ===== Rewrite as function_map_transform ===== *)

(* ===== Runtime Invariant ===== *)

Definition ac_dfg_inv_def:
  ac_dfg_inv dfg s <=>
    (!v inst input_op.
       dfg_get_def dfg v = SOME inst /\
       inst.inst_opcode = ISZERO /\
       inst.inst_operands = [input_op] /\
       IS_SOME (lookup_var v s) ==>
       ?input_val.
         eval_operand input_op s = SOME input_val /\
         lookup_var v s = SOME (bool_to_word (input_val = 0w))) /\
    (!v inst src_op.
       dfg_get_def dfg v = SOME inst /\
       inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [src_op] /\
       IS_SOME (lookup_var v s) ==>
       lookup_var v s = eval_operand src_op s)
End

(* Bridge: ac_get_iszero_operand + ac_dfg_inv ==> lookup_var relates to pred value.
   Traces through ASSIGN chains in the DFG to find the ISZERO source, using
   ac_dfg_inv to maintain the relationship at each step. *)
Theorem ac_dfg_iszero_bridge:
  !dfg visited op s pred.
    ac_dfg_inv dfg s /\
    ac_get_iszero_operand dfg visited op = SOME pred /\
    IS_SOME (eval_operand op s) ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\
               eval_operand op s = SOME (bool_to_word (pred_val = 0w))
Proof
  recInduct ac_get_iszero_operand_ind >> rpt strip_tac >>
  qpat_x_assum `ac_get_iszero_operand _ _ _ = _` mp_tac >>
  simp[Once ac_get_iszero_operand_def] >>
  Cases_on `op` >> simp[] >>
  Cases_on `dfg_get_def dfg s'` >> simp[] >>
  strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  Cases_on `x.inst_opcode = ISZERO` >> simp[] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac
  >- (
    (* ISZERO case: x is ISZERO [pred], use ac_dfg_inv directly *)
    fs[ac_dfg_inv_def, eval_operand_def] >> metis_tac[]
  )
  >- (
    (* ASSIGN case: x is ASSIGN [h], ac_get_iszero_operand recurses on h *)
    fs[ac_dfg_inv_def] >>
    (* Use ASSIGN clause: lookup_var s' s = eval_operand h s *)
    `lookup_var s' s = eval_operand h s` by (
      first_x_assum match_mp_tac >> simp[] >>
      fs[eval_operand_def]) >>
    (* Apply IH: ac_dfg_inv + IS_SOME(eval h s) ==> bridge for h *)
    first_x_assum (qspec_then `s` mp_tac) >> impl_tac
    >- (simp[ac_dfg_inv_def] >> fs[eval_operand_def] >> gvs[])
    >- (strip_tac >> fs[eval_operand_def] >> gvs[])
  )
QED

(* Corollary: when ASSERT passes (nonzero), the underlying pred is 0w *)
Theorem ac_assert_pass_pred_zero:
  !dfg s v pred val.
    ac_dfg_inv dfg s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME val /\ val <> 0w ==>
    eval_operand pred s = SOME 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge >> strip_tac >> gvs[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* Dual: when ASSERT aborts (operand is 0w), the underlying pred is nonzero *)
Theorem ac_assert_abort_pred_nonzero:
  !dfg s v pred.
    ac_dfg_inv dfg s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME 0w ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\ pred_val <> 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge >> strip_tac >>
  qexists_tac `pred_val` >> simp[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* ===== Local (prefix-restricted) DFG invariant =====
   Same as ac_dfg_inv but restricted to DFG entries whose defining instruction
   satisfies predicate P. Used to handle loops where cross-block DFG entries
   may temporarily violate ac_dfg_inv. *)

Definition ac_dfg_inv_local_def:
  ac_dfg_inv_local dfg P s <=>
    (!v inst input_op.
       dfg_get_def dfg v = SOME inst /\
       P inst /\
       inst.inst_opcode = ISZERO /\
       inst.inst_operands = [input_op] /\
       IS_SOME (lookup_var v s) ==>
       ?input_val.
         eval_operand input_op s = SOME input_val /\
         lookup_var v s = SOME (bool_to_word (input_val = 0w))) /\
    (!v inst src_op.
       dfg_get_def dfg v = SOME inst /\
       P inst /\
       inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [src_op] /\
       IS_SOME (lookup_var v s) ==>
       lookup_var v s = eval_operand src_op s)
End

(* ac_dfg_inv implies ac_dfg_inv_local for any P *)
Theorem ac_dfg_inv_implies_local:
  !dfg P s. ac_dfg_inv dfg s ==> ac_dfg_inv_local dfg P s
Proof
  simp[ac_dfg_inv_def, ac_dfg_inv_local_def] >> metis_tac[]
QED

(* ac_dfg_inv_local with P = \i. T is equivalent to ac_dfg_inv *)
Theorem ac_dfg_inv_local_T:
  !dfg s. ac_dfg_inv_local dfg (\i. T) s <=> ac_dfg_inv dfg s
Proof
  simp[ac_dfg_inv_def, ac_dfg_inv_local_def]
QED

(* Antitonicity: restricting P preserves the invariant *)
Theorem ac_dfg_inv_local_restrict:
  !dfg P Q s. ac_dfg_inv_local dfg P s /\ (!i. Q i ==> P i) ==>
    ac_dfg_inv_local dfg Q s
Proof
  rw[ac_dfg_inv_local_def] >> res_tac >> metis_tac[]
QED

(* Bridge for local invariant: same as ac_dfg_iszero_bridge but uses
   ac_dfg_inv_local. Requires that all DFG entries with defined outputs
   satisfy P. *)
Theorem ac_dfg_iszero_bridge_local:
  !dfg visited op s pred P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg visited op = SOME pred /\
    IS_SOME (eval_operand op s) /\
    (!v inst. dfg_get_def dfg v = SOME inst /\ IS_SOME (lookup_var v s) ==>
       P inst) ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\
               eval_operand op s = SOME (bool_to_word (pred_val = 0w))
Proof
  recInduct ac_get_iszero_operand_ind >> rpt strip_tac >>
  qpat_x_assum `ac_get_iszero_operand _ _ _ = _` mp_tac >>
  simp[Once ac_get_iszero_operand_def] >>
  Cases_on `op` >> simp[] >>
  Cases_on `dfg_get_def dfg s'` >> simp[] >>
  strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  Cases_on `x.inst_opcode = ISZERO` >> simp[] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac >>
  Cases_on `x.inst_opcode = ASSIGN` >> gvs[]
  >- (
    (* ISZERO case: use ISZERO clause of ac_dfg_inv_local *)
    qpat_x_assum `ac_dfg_inv_local _ _ _` mp_tac >>
    simp[ac_dfg_inv_local_def] >> strip_tac >>
    qpat_x_assum `!v inst input_op. _ /\ _ /\ _.inst_opcode = ISZERO /\ _ ==> _`
      (qspecl_then [`s'`, `x`, `h`] mp_tac) >>
    simp[] >> (impl_tac >- (fs[eval_operand_def] >> res_tac)) >>
    strip_tac >> simp[eval_operand_def] >> metis_tac[]
  )
  (* ASSIGN case: derive eval h from inv, then apply IH *)
  >>
  (Q.SUBGOAL_THEN `IS_SOME (lookup_var s' s)` ASSUME_TAC >-
    fs[eval_operand_def])
  >>
  (Q.SUBGOAL_THEN `P (x:instruction)` ASSUME_TAC >- res_tac)
  >>
  (Q.SUBGOAL_THEN `lookup_var s' s = eval_operand h s` ASSUME_TAC >- (
    qpat_x_assum `ac_dfg_inv_local _ _ _` mp_tac >>
    simp[ac_dfg_inv_local_def] >> strip_tac >>
    qpat_x_assum `!v inst src_op. _ /\ _ /\ _.inst_opcode = ASSIGN /\ _ ==> _`
      (qspecl_then [`s'`, `x`, `h`] mp_tac) >> simp[]))
  >>
  (Q.SUBGOAL_THEN `IS_SOME (eval_operand h s)` ASSUME_TAC >- gvs[]) >>
  qpat_x_assum `!s'' P'. _` (qspecl_then [`s`, `P`] mp_tac) >>
  strip_tac >> first_x_assum mp_tac >> (impl_tac >- metis_tac[]) >> strip_tac >> gvs[eval_operand_def]
QED

(* Corollary: ASSERT passes => pred = 0w (local version) *)
Theorem ac_assert_pass_pred_zero_local:
  !dfg s v pred val P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME val /\ val <> 0w /\
    (!v' inst. dfg_get_def dfg v' = SOME inst /\ IS_SOME (lookup_var v' s) ==>
       P inst) ==>
    eval_operand pred s = SOME 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge_local >> strip_tac >> gvs[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* Corollary: ASSERT aborts => pred nonzero (local version) *)
Theorem ac_assert_abort_pred_nonzero_local:
  !dfg s v pred P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME 0w /\
    (!v' inst. dfg_get_def dfg v' = SOME inst /\ IS_SOME (lookup_var v' s) ==>
       P inst) ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\ pred_val <> 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge_local >> strip_tac >>
  qexists_tac `pred_val` >> simp[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* ===== valid_state_rel for state_equiv/execution_equiv UNIV ===== *)

Theorem valid_state_rel_UNIV:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv UNIV)
Proof
  simp[execEquivParamDefsTheory.valid_state_rel_def,
       stateEquivTheory.state_equiv_def,
       stateEquivTheory.execution_equiv_def,
       venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def,
       venomStateTheory.eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `op` >> fs[venomStateTheory.eval_operand_def,
                       venomStateTheory.lookup_var_def]
QED

(* ===== Lift result helpers ===== *)

Theorem execution_equiv_weaken_UNIV[local]:
  !vars s1 s2. execution_equiv vars s1 s2 ==> execution_equiv UNIV s1 s2
Proof
  rw[stateEquivTheory.execution_equiv_def]
QED

Theorem lift_result_weaken_UNIV:
  !R vars r1 r2.
    lift_result R (execution_equiv vars) (execution_equiv vars) r1 r2 ==>
    lift_result R (execution_equiv UNIV) (execution_equiv UNIV) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  fs[lift_result_def, execution_equiv_weaken_UNIV] >>
  metis_tac[execution_equiv_weaken_UNIV]
QED

(* ===== run_insts infrastructure ===== *)

Theorem run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
    case run_insts fuel ctx xs s of
      OK s' => run_insts fuel ctx ys s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | IntRet v s' => IntRet v s'
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED

(* Appending a NOP instruction to a successful run_insts is still OK *)
Theorem run_insts_snoc_nop[local]:
  !insts nop fuel ctx s s'.
    run_insts fuel ctx insts s = OK s' /\
    nop.inst_opcode = NOP ==>
    run_insts fuel ctx (insts ++ [nop]) s = OK s'
Proof
  rw[run_insts_append, run_insts_singleton, step_nop_identity]
QED

(* Specialized: appending NOP to a 2-element run_insts *)
Theorem run_insts_two_snoc_nop:
  !a b nop fuel ctx s s'.
    run_insts fuel ctx [a; b] s = OK s' /\
    nop.inst_opcode = NOP ==>
    run_insts fuel ctx [a; b; nop] s = OK s'
Proof
  rpt strip_tac >>
  `[a; b; nop] = [a; b] ++ [nop]` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  irule run_insts_snoc_nop >> simp[]
QED

(* General: composing [a;b] with [c] when both succeed *)
Theorem run_insts_two_snoc:
  !a b c fuel ctx s s' s''.
    run_insts fuel ctx [a; b] s = OK s' /\
    step_inst fuel ctx c s' = OK s'' ==>
    run_insts fuel ctx [a; b; c] s = OK s''
Proof
  rpt strip_tac >>
  `[a; b; c] = [a; b] ++ [c]` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[run_insts_append, run_insts_def]
QED

(* Rewrite [a;b;c] as [a;b] ++ [c] for run_insts decomposition *)
Theorem run_insts_three:
  !a b c fuel ctx s.
    run_insts fuel ctx [a; b; c] s =
    case run_insts fuel ctx [a; b] s of
      OK s' => run_insts fuel ctx [c] s'
    | Halt s' => Halt s'
    | Abort a' s' => Abort a' s'
    | IntRet v' s' => IntRet v' s'
    | Error e => Error e
Proof
  rpt gen_tac >>
  `[a; b; c] = [a; b] ++ [c]` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[run_insts_append]
QED

(* ===== Per-Block Simulation helpers ===== *)

Theorem step_eval_operand_preserved:
  !fuel ctx inst s s' op.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
    eval_operand op s' = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def] >>
  metis_tac[step_preserves_non_output_vars, step_preserves_labels]
QED

(* word_or a b = 0w iff both zero *)
Theorem word_or_eq_0w:
  !(a:'a word) b. (word_or a b = 0w) <=> (a = 0w /\ b = 0w)
Proof
  rw[wordsTheory.word_or_def, wordsTheory.word_0,
     fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >> metis_tac[]
QED

(* revert/set_returndata preserves execution_equiv UNIV *)
Theorem revert_returndata_exec_equiv_UNIV:
  !s s'. execution_equiv UNIV s s' ==>
    execution_equiv UNIV
      (revert_state (set_returndata [] s))
      (revert_state (set_returndata [] s'))
Proof
  rw[execution_equiv_def, revert_state_def, set_returndata_def]
QED

(* ===== Toolkit: ac_dfg_inv preservation ===== *)

(* Constructor-form step lemmas (avoiding literal form requirement) *)
Triviality step_iszero_con[local]:
  !s input_op out iid v.
    eval_operand input_op s = SOME v ==>
    step_inst_base (instruction iid ISZERO [input_op] [out]) s =
    OK (update_var out (bool_to_word (v = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure1_def, update_var_def]
QED

Triviality step_assign_con[local]:
  !s src_op out iid v.
    eval_operand src_op s = SOME v ==>
    step_inst_base (instruction iid ASSIGN [src_op] [out]) s =
    OK (update_var out v s)
Proof
  rw[step_inst_base_def, exec_pure1_def, update_var_def]
QED

(* Shared tactic for establishing eval_operand preservation *)
val eval_op_preserved_tac =
  `!op. (!x. op = Var x ==> ~MEM x h.inst_outputs) ==>
        eval_operand op s' = eval_operand op s` by (
    rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
    metis_tac[step_preserves_non_output_vars, step_preserves_labels]);

(* Shared helper tactic for the non-output cases of ac_dfg_inv_step_ssa. *)
fun ac_ssa_case2_tac op_name =
  (Q.SUBGOAL_THEN `lookup_var v s' = lookup_var v s` ASSUME_TAC >-
    metis_tac[step_preserves_non_output_vars]) >>
  (Q.SUBGOAL_THEN `IS_SOME (lookup_var v s)` ASSUME_TAC >- gvs[]) >>
  (Q.SUBGOAL_THEN `!op'. MEM op' inst.inst_operands ==>
     eval_operand op' s' = eval_operand op' s` ASSUME_TAC >-
    (rpt strip_tac >>
     first_x_assum (qspecl_then [`v`, `inst`, `op'`] mp_tac) >>
     simp[])) >>
  qpat_x_assum `ac_dfg_inv dfg s` mp_tac >>
  simp[ac_dfg_inv_def] >> strip_tac >>
  first_x_assum (qspecl_then [`v`, `inst`, op_name] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [op_name] mp_tac) >>
  simp[MEM] >> strip_tac >> gvs[];

Theorem ac_dfg_inv_step_ssa:
  !fuel ctx h s s' dfg.
    step_inst fuel ctx h s = OK s' /\
    ~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE /\
    inst_wf h /\
    ac_dfg_inv dfg s /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)) /\
    (!v. MEM v h.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME h) /\
    (!op x. MEM op h.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs) /\
    (* Weaker than no-redefine: for DFG entries whose output is defined
       and not overwritten by h, operand variables are not in h's outputs *)
    (!v di op x.
       dfg_get_def dfg v = SOME di /\ IS_SOME (lookup_var v s) /\
       ~MEM v h.inst_outputs /\
       MEM op di.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs)
  ==>
    ac_dfg_inv dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  (* Establish a helper: for DFG entries not overwritten by h,
     their operand evals are preserved *)
  (Q.SUBGOAL_THEN
    `!v di op. dfg_get_def dfg v = SOME di /\
       IS_SOME (lookup_var v s) /\ ~MEM v h.inst_outputs /\
       MEM op di.inst_operands ==>
       eval_operand op s' = eval_operand op s`
    ASSUME_TAC >- (
      rpt strip_tac >>
      Cases_on `op` >> gvs[eval_operand_def]
      >- metis_tac[step_preserves_non_output_vars]
      >- metis_tac[step_preserves_labels, ac_is_safe_between_def,
                   venomInstPropsTheory.step_preserves_labels])) >>
  simp[ac_dfg_inv_def] >> rpt conj_tac
  >- (
    (* ISZERO conjunct *)
    rpt gen_tac >> strip_tac >>
    Cases_on `MEM v h.inst_outputs`
    >- (
      (Q.SUBGOAL_THEN `dfg_get_def dfg v = SOME h` ASSUME_TAC >-
        (res_tac >> simp[])) >>
      gvs[] >>
      fs[optionTheory.IS_SOME_EXISTS] >>
      eval_op_preserved_tac >>
      (Q.SUBGOAL_THEN `eval_operand input_op s' = eval_operand input_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> metis_tac[MEM])) >>
      Cases_on `h` >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_non_invoke] >>
      imp_res_tac step_iszero_con >>
      gvs[update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE])
    >- ac_ssa_case2_tac `input_op`)
  >- (
    (* ASSIGN conjunct *)
    rpt gen_tac >> strip_tac >>
    Cases_on `MEM v h.inst_outputs`
    >- (
      (Q.SUBGOAL_THEN `dfg_get_def dfg v = SOME h` ASSUME_TAC >-
        (res_tac >> simp[])) >>
      gvs[] >>
      fs[optionTheory.IS_SOME_EXISTS] >>
      eval_op_preserved_tac >>
      (Q.SUBGOAL_THEN `eval_operand src_op s' = eval_operand src_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> metis_tac[MEM])) >>
      Cases_on `h` >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_non_invoke] >>
      imp_res_tac step_assign_con >>
      gvs[update_var_def, lookup_var_def, eval_operand_def,
          finite_mapTheory.FLOOKUP_UPDATE])
    >- ac_ssa_case2_tac `src_op`)
QED

(* ac_dfg_inv preserved through update_var on a fresh variable.
   Fresh means: not in the DFG (neither as a definition nor as an operand). *)
Theorem ac_dfg_inv_update_fresh:
  !dfg s v val.
    ac_dfg_inv dfg s /\
    dfg_get_def dfg v = NONE /\
    (!di x. dfg_get_def dfg x = SOME di ==> ~MEM (Var v) di.inst_operands)
  ==>
    ac_dfg_inv dfg (update_var v val s)
Proof
  rpt strip_tac >> simp[ac_dfg_inv_def] >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >>
  Cases_on `v' = v` >> gvs[] (* v'=v contradicts dfg_get_def v = NONE *)
  (* Remaining: ISZERO and ASSIGN with v' <> v.
     Key: operand op of dfg entry inst can't be Var v (from hyp), so
     eval_operand op (update_var v val s) = eval_operand op s *)
  >- (
    `~MEM (Var v) inst.inst_operands` by res_tac >>
    `eval_operand input_op (update_var v val s) = eval_operand input_op s` by (
      Cases_on `input_op` >>
      gvs[eval_operand_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
    gvs[ac_dfg_inv_def, update_var_def, lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE]
  )
  >- (
    `~MEM (Var v) inst.inst_operands` by res_tac >>
    `eval_operand src_op (update_var v val s) = eval_operand src_op s` by (
      Cases_on `src_op` >>
      gvs[eval_operand_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
    gvs[ac_dfg_inv_def, update_var_def, lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE]
  )
QED

(* eval_operand preserved through update_var when operand doesn't reference v *)
Theorem eval_operand_update_var_neq:
  !op v val s.
    (!x. op = Var x ==> x <> v) ==>
    eval_operand op (update_var v val s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, update_var_def, lookup_var_def,
                finite_mapTheory.FLOOKUP_UPDATE]
QED

(* IS_SOME(eval_operand) is preserved by safe_between steps *)
Theorem safe_between_step_eval_is_some:
  !inst s s' fuel ctx op.
    ac_is_safe_between inst /\ inst_wf inst /\
    step_inst fuel ctx inst s = OK s' /\
    (!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)) /\
    IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand op s')
Proof
  rpt strip_tac >> Cases_on `op` >- simp[eval_operand_def]
  >- (
    rename1 `Var v` >>
    fs[eval_operand_def] >>
    irule safe_between_step_is_some_mono >>
    metis_tac[])
  >- (fs[eval_operand_def] >>
      `s'.vs_labels = s.vs_labels` by
        metis_tac[step_preserves_labels, ac_is_safe_between_def] >>
      gvs[])
QED

(* ===== ASSERT steps ===== *)

(* ASSERT succeeds iff its condition is nonzero, state unchanged *)
Theorem step_assert_ok:
  !fuel ctx inst s cond_op cond.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [cond_op] /\
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst fuel ctx inst s = OK s
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `inst` >> gvs[step_inst_non_invoke, step_inst_base_def]
QED

Theorem step_assert_abort:
  !fuel ctx inst s cond_op.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [cond_op] /\
    eval_operand cond_op s = SOME 0w ==>
    step_inst fuel ctx inst s =
      Abort Revert_abort (revert_state (set_returndata [] s))
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `inst` >> gvs[step_inst_non_invoke, step_inst_base_def]
QED

(* ===== Merge candidates ===== *)

(* ac_scan_block only produces candidates whose ids come from ASSERT instructions *)
Theorem ac_scan_second_is_assert:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    ?inst. MEM inst insts /\ inst.inst_opcode = ASSERT /\
           inst.inst_id = mc.mc_second_id
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_scan_first_is_assert:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    (?inst. MEM inst insts /\ inst.inst_opcode = ASSERT /\
            inst.inst_id = mc.mc_first_id) \/
    (?prev_pred. pending = SOME (mc.mc_first_id, prev_pred))
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED

(* IH application tactic for ac_scan_block_ordered_gen *)
fun scan_ordered_ih pend =
  first_x_assum (qspecl_then [`prefix ++ [h]`, pend, `mc`] mp_tac) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  simp[ADD1, LENGTH_APPEND] >>
  disch_then match_mp_tac >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP] >>
  ASM_REWRITE_TAC[];

Triviality ac_scan_block_ordered_gen[local]:
  !dfg rest prefix pending mc.
    MEM mc (ac_scan_block dfg rest pending) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ rest)) /\
    (!prev_id prev_pred. pending = SOME (prev_id, prev_pred) ==>
       ?idx. idx < LENGTH prefix /\
             (EL idx (prefix ++ rest)).inst_id = prev_id) ==>
    ?idx_f idx_s.
      idx_f < idx_s /\ idx_s < LENGTH (prefix ++ rest) /\
      (EL idx_f (prefix ++ rest)).inst_id = mc.mc_first_id /\
      (EL idx_s (prefix ++ rest)).inst_id = mc.mc_second_id
Proof
  gen_tac >> Induct >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ASSERT` >> fs[]
  >- (
    Cases_on `h.inst_operands` >> fs[]
    >- scan_ordered_ih `NONE`
    >- (
      Cases_on `ac_get_iszero_operand dfg {} h'` >> fs[]
      >- scan_ordered_ih `NONE`
      >- (
        Cases_on `t` >> fs[]
        >- (
          Cases_on `pending` >> fs[LET_THM]
          >- (
            scan_ordered_ih `SOME (h.inst_id, x)` >>
            rpt strip_tac >> gvs[] >>
            qexists_tac `LENGTH prefix` >> simp[EL_APPEND_EQN]
          )
          >- (
            Cases_on `x'` >> fs[MEM]
            >- (
              (* emit case: mc is the record, witnesses are idx and LENGTH prefix *)
              qexists_tac `idx` >> qexists_tac `LENGTH prefix` >>
              simp[EL_APPEND_EQN]
            )
            >- (
              (* tail recursive case *)
              scan_ordered_ih `SOME (h.inst_id, x)` >>
              rpt strip_tac >> gvs[] >>
              qexists_tac `LENGTH prefix` >> simp[EL_APPEND_EQN]
            )
          )
        )
        >- scan_ordered_ih `NONE`
      )
    )
  )
  >- (
    Cases_on `ac_is_safe_between h` >> fs[]
    >- (
      scan_ordered_ih `pending` >>
      rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      qexists_tac `idx` >> simp[]
    )
    >- scan_ordered_ih `NONE`
  )
QED

(* Specialization: ac_scan_block with NONE gives ordered indices *)
Theorem ac_scan_block_ordered_indices:
  !dfg insts mc.
    MEM mc (ac_scan_block dfg insts NONE) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ?idx_f idx_s.
      idx_f < idx_s /\ idx_s < LENGTH insts /\
      (EL idx_f insts).inst_id = mc.mc_first_id /\
      (EL idx_s insts).inst_id = mc.mc_second_id
Proof
  rpt strip_tac >>
  qspecl_then [`dfg`, `insts`, `[]`, `NONE`, `mc`] mp_tac
    ac_scan_block_ordered_gen >>
  simp[]
QED

(* Candidates are well-formed w.r.t. insts: for any candidate whose first
   appears in insts, both first and second appear with second after first.
   This property passes to tails (unlike the stronger version). *)
Definition ac_cands_ordered_def:
  ac_cands_ordered cands insts <=>
    (!mc. MEM mc cands /\
       (?i. MEM i insts /\ i.inst_id = mc.mc_first_id) ==>
       ?idx_f idx_s.
         idx_f < idx_s /\ idx_s < LENGTH insts /\
         (EL idx_f insts).inst_id = mc.mc_first_id /\
         (EL idx_s insts).inst_id = mc.mc_second_id) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts)
End

(* Stronger version: every candidate has both endpoints in insts *)
Theorem ac_cands_ordered_full:
  !cands insts.
    (!mc. MEM mc cands ==>
       ?idx_f idx_s.
         idx_f < idx_s /\ idx_s < LENGTH insts /\
         (EL idx_f insts).inst_id = mc.mc_first_id /\
         (EL idx_s insts).inst_id = mc.mc_second_id) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts)
  ==>
    ac_cands_ordered cands insts
Proof
  rw[ac_cands_ordered_def] >> metis_tac[]
QED

(* From ac_cands_ordered, if h is the first of mc, mc's second is in rest *)

(* When mc.mc_second_id = h.inst_id (head), mc.mc_first_id is not in rest.
   Proof: if first_id were in (h::rest), cands_ordered gives idx_f < idx_s.
   Since second_id = h.inst_id, ALL_DISTINCT forces idx_s = 0 (only h has that id).
   But idx_f < 0 is impossible. So first_id is not in (h::rest), hence not in rest. *)
Theorem ac_cands_second_at_head:
  !cands h rest mc.
    ac_cands_ordered cands (h :: rest) /\ MEM mc cands /\
    mc.mc_second_id = h.inst_id ==>
    !i. MEM i rest ==> i.inst_id <> mc.mc_first_id
Proof
  rw[ac_cands_ordered_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `mc` mp_tac) >>
  impl_tac >- (simp[] >> qexists_tac `i` >> simp[]) >>
  strip_tac >>
  (* idx_s must be 0 since (EL idx_s (h::rest)).inst_id = mc.mc_second_id = h.inst_id *)
  `idx_s = 0` by (
    spose_not_then assume_tac >>
    `0 < LENGTH (h::rest)` by simp[] >>
    `EL idx_s (MAP (\i'. i'.inst_id) (h::rest)) = mc.mc_second_id` by
      simp[EL_MAP] >>
    `EL 0 (MAP (\i'. i'.inst_id) (h::rest)) = h.inst_id` by
      simp[EL_MAP] >>
    `idx_s < LENGTH (MAP (\i'. i'.inst_id) (h::rest))` by simp[] >>
    `0 < LENGTH (MAP (\i'. i'.inst_id) (h::rest))` by simp[] >>
    `ALL_DISTINCT (MAP (\i'. i'.inst_id) (h::rest))` by
      simp[ALL_DISTINCT] >>
    metis_tac[ALL_DISTINCT_EL_IMP]) >>
  gvs[]
QED

(* ac_cands_ordered passes to tail unconditionally *)
Theorem ac_cands_ordered_tail:
  !cands h rest.
    ac_cands_ordered cands (h :: rest) ==>
    ac_cands_ordered cands rest
Proof
  rw[ac_cands_ordered_def] >>
  first_x_assum (qspec_then `mc` mp_tac) >> simp[] >>
  impl_tac >- (qexists_tac `i` >> simp[]) >>
  strip_tac >>
  `mc.mc_first_id <> h.inst_id` by (
    spose_not_then assume_tac >> gvs[ALL_DISTINCT, MEM_MAP] >>
    metis_tac[]) >>
  `idx_f <> 0` by (spose_not_then strip_assume_tac >> gvs[]) >>
  `idx_s <> 0` by (Cases_on `idx_s` >> gvs[]) >>
  MAP_EVERY qexists_tac [`idx_f - 1`, `idx_s - 1`] >>
  Cases_on `idx_f` >> Cases_on `idx_s` >> gvs[]
QED

(*
 * ac_deferred_chain_abort: When a nonzero pred enters the chain,
 * the FOLDL-transformed code eventually aborts.
 *
 * Proof by complete induction on LENGTH insts.
 * At each step, the head instruction's FOLDL contribution either:
 *   (a) aborts directly (done)
 *   (b) succeeds, preserving pred_op nonzero — apply IH to rest
 *)
(*
 * Helper: safe_between step succeeds and preserves eval_operand + exec_equiv.
 *)

Triviality INDEX_FIND_P[local]:
  !l i P n x. INDEX_FIND i P l = SOME (n, x) ==> P x
Proof
  Induct >> simp[INDEX_FIND_def] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[] >> metis_tac[]
QED

Theorem FIND_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  rpt strip_tac >>
  fs[FIND_def] >>
  Cases_on `INDEX_FIND 0 P l` >> gvs[] >>
  Cases_on `x'` >> gvs[] >> metis_tac[INDEX_FIND_P]
QED

Triviality INDEX_FIND_MEM[local]:
  !l i P n x. INDEX_FIND i P l = SOME (n, x) ==> MEM x l
Proof
  Induct >> simp[INDEX_FIND_def] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[] >> metis_tac[]
QED

Theorem FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  rpt strip_tac >> fs[FIND_def] >>
  Cases_on `INDEX_FIND 0 P l` >> gvs[] >>
  Cases_on `x'` >> gvs[] >> metis_tac[INDEX_FIND_MEM]
QED

(* If P holds for some member of l, then FIND P l returns SOME *)

(* mc_second_id values in scan result come from instruction IDs *)
Theorem ac_scan_second_id_mem:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    ?i. MEM i insts /\ mc.mc_second_id = i.inst_id
Proof
  Induct_on `insts` >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ASSERT` >> fs[]
  >- (Cases_on `h.inst_operands` >> fs[]
      >- (res_tac >> qexists_tac `i` >> simp[])
      >- (Cases_on `t` >> fs[]
          >- (Cases_on `ac_get_iszero_operand dfg {} h'` >> fs[]
              >- (res_tac >> qexists_tac `i` >> simp[])
              >- (Cases_on `pending` >> fs[]
                  >- (res_tac >> qexists_tac `i` >> simp[])
                  >- (Cases_on `x'` >> fs[LET_THM] >>
                      gvs[MEM] >> res_tac >>
                      metis_tac[])))
          >- (Cases_on `ac_get_iszero_operand dfg {} h'` >> fs[]
              >- (res_tac >> qexists_tac `i` >> simp[])
              >- (res_tac >> qexists_tac `i` >> simp[]))))
  >- (Cases_on `ac_is_safe_between h` >> fs[] >>
      res_tac >> qexists_tac `i` >> simp[])
QED

(* mc_second_id values are unique when instruction IDs are distinct *)
Theorem ac_scan_unique_second_id:
  !dfg insts pending.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) (ac_scan_block dfg insts pending))
Proof
  Induct_on `insts` >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  `!dfg' p'. ALL_DISTINCT (MAP (\mc. mc.mc_second_id)
     (ac_scan_block dfg' insts p'))` by metis_tac[] >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP] >>
  spose_not_then strip_assume_tac >>
  drule ac_scan_second_id_mem >> strip_tac >>
  gvs[ALL_DISTINCT, MEM_MAP]
QED

(*
 * Chain invariant: packages all preconditions for the deferred abort proof.
 * This keeps the induction goal manageable.
 *)

(* A scanner edge consists of two recognized assertions and a safe gap.
   The first disjunct accounts precisely for the incoming pending origin. *)
Theorem ac_scan_edge_decompose:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    (?gap second suffix op.
       insts = gap ++ second :: suffix /\ EVERY ac_is_safe_between gap /\
       pending = SOME (mc.mc_first_id, mc.mc_first_pred) /\
       second.inst_id = mc.mc_second_id /\ second.inst_opcode = ASSERT /\
       second.inst_operands = [op] /\
       ac_get_iszero_operand dfg {} op = SOME mc.mc_second_pred) \/
    (?prefix first gap second suffix op1 op2.
       insts = prefix ++ first :: gap ++ second :: suffix /\
       EVERY ac_is_safe_between gap /\
       first.inst_id = mc.mc_first_id /\ first.inst_opcode = ASSERT /\
       first.inst_operands = [op1] /\
       ac_get_iszero_operand dfg {} op1 = SOME mc.mc_first_pred /\
       second.inst_id = mc.mc_second_id /\ second.inst_opcode = ASSERT /\
       second.inst_operands = [op2] /\
       ac_get_iszero_operand dfg {} op2 = SOME mc.mc_second_pred)
Proof
  gen_tac >> Induct >> simp[ac_scan_block_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = ASSERT` >> simp[]
  >- (Cases_on `h.inst_operands` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
          disj2_tac >> qexists_tac `h::prefix` >> simp[] >> metis_tac[]) >>
      Cases_on `t` >> simp[]
      >- (Cases_on `ac_get_iszero_operand dfg {} h'` >> simp[]
          >- (strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
              disj2_tac >> qexists_tac `h::prefix` >> simp[] >> metis_tac[]) >>
          Cases_on `pending` >> simp[]
          >- (strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
              >- (qexistsl_tac [`[]`, `h`] >> simp[] >> metis_tac[]) >>
              qexists_tac `h::prefix` >> simp[] >> metis_tac[]) >>
          Cases_on `x'` >> simp[] >> strip_tac
          >- (gvs[] >> disj1_tac >> qexists_tac `[]` >> simp[] >> metis_tac[]) >>
          first_x_assum drule >> strip_tac >> gvs[] >> disj2_tac
          >- (qexistsl_tac [`[]`, `h`] >> simp[] >> metis_tac[]) >>
          qexists_tac `h::prefix` >> simp[] >> metis_tac[]) >>
      Cases_on `ac_get_iszero_operand dfg {} h'` >> simp[] >>
      strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
      disj2_tac >> qexists_tac `h::prefix` >> simp[] >> metis_tac[]) >>
  Cases_on `ac_is_safe_between h` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac
      >- (disj1_tac >> qexists_tac `h::gap` >> simp[] >> metis_tac[]) >>
      disj2_tac >> qexists_tac `h::prefix` >> simp[] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  disj2_tac >> qexists_tac `h::prefix` >> simp[] >> metis_tac[]
QED

Theorem ac_scan_pair_decompose:
  !dfg insts mc.
    MEM mc (ac_scan_block dfg insts NONE) ==>
    ?prefix first gap second suffix op1 op2.
      insts = prefix ++ first :: gap ++ second :: suffix /\
      EVERY ac_is_safe_between gap /\
      first.inst_id = mc.mc_first_id /\ first.inst_opcode = ASSERT /\
      first.inst_operands = [op1] /\
      ac_get_iszero_operand dfg {} op1 = SOME mc.mc_first_pred /\
      second.inst_id = mc.mc_second_id /\ second.inst_opcode = ASSERT /\
      second.inst_operands = [op2] /\
      ac_get_iszero_operand dfg {} op2 = SOME mc.mc_second_pred
Proof
  rpt strip_tac >> drule ac_scan_edge_decompose >> simp[]
QED

Theorem ac_scan_unique_first_id_pending:
  !dfg insts pending.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!id p. pending = SOME (id,p) ==> ~MEM id (MAP (\i. i.inst_id) insts)) ==>
    ALL_DISTINCT (MAP (\mc. mc.mc_first_id) (ac_scan_block dfg insts pending))
Proof
  gen_tac >> Induct >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ASSERT` >> simp[]
  >- (Cases_on `h.inst_operands` >> simp[] >>
      Cases_on `ac_get_iszero_operand dfg {} h'` >> simp[] >>
      Cases_on `t` >> simp[]
      >- (Cases_on `pending` >> simp[] >>
          Cases_on `x'` >> simp[MEM_MAP] >> conj_tac
          >- (rpt strip_tac >> drule ac_scan_first_is_assert >>
              strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
          first_x_assum irule >> gvs[]) >>
      first_x_assum irule >> simp[] >> gvs[]) >>
  Cases_on `ac_is_safe_between h` >> simp[] >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

Theorem ac_scan_unique_first_id:
  !dfg insts.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ALL_DISTINCT (MAP (\mc. mc.mc_first_id) (ac_scan_block dfg insts NONE))
Proof
  rpt strip_tac >> irule ac_scan_unique_first_id_pending >> simp[]
QED

(* Ordered edges cannot leave the last assertion in a finite chain.
   This also covers overlapping pairs, not just isolated merges. *)
Theorem ac_cands_terminal_endpoint:
  !insts cands i.
    ac_cands_ordered cands insts /\ MEM i insts ==>
    ?j. MEM j insts /\
        RTC (\a b. ?mc. MEM mc cands /\ mc.mc_first_id = a /\
                         mc.mc_second_id = b) i.inst_id j.inst_id /\
        ~EXISTS (\mc. mc.mc_first_id = j.inst_id) cands
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `ac_cands_ordered cands insts` by metis_tac[ac_cands_ordered_tail] >>
  Cases_on `i = h`
  >- (gvs[] >>
      Cases_on `EXISTS (\mc. mc.mc_first_id = h.inst_id) cands`
      >- (gvs[EXISTS_MEM] >>
          `?k. MEM k insts /\ k.inst_id = mc.mc_second_id` by
            (qpat_x_assum `ac_cands_ordered cands (h::insts)` mp_tac >>
             simp[ac_cands_ordered_def] >> strip_tac >>
             first_x_assum (qspec_then `mc` mp_tac) >>
             (impl_tac >- metis_tac[MEM]) >> strip_tac >>
             Cases_on `idx_s` >> gvs[] >>
             qexists_tac `EL n insts` >> simp[EL_MEM]) >>
          first_x_assum drule >> disch_then drule >> strip_tac >>
          qexists_tac `j` >> simp[] >>
          irule (cj 2 relationTheory.RTC_RULES) >>
          qexists_tac `k.inst_id` >> simp[] >>
          qexists_tac `mc` >> simp[]) >>
      qexists_tac `h` >> gvs[relationTheory.RTC_REFL, EXISTS_MEM, EVERY_MEM]) >>
  `MEM i insts` by gvs[] >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists_tac `j` >> gvs[EXISTS_MEM, EVERY_MEM]
QED

Theorem ac_scan_cands_ordered:
  !dfg insts.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ac_cands_ordered (ac_scan_block dfg insts NONE) insts
Proof
  rpt strip_tac >> irule ac_cands_ordered_full >>
  simp[] >> metis_tac[ac_scan_block_ordered_indices]
QED

Theorem ac_scan_terminal_endpoint:
  !dfg insts mc.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    MEM mc (ac_scan_block dfg insts NONE) ==>
    ?last. MEM last insts /\
      RTC (\a b. ?edge. MEM edge (ac_scan_block dfg insts NONE) /\
                       edge.mc_first_id = a /\ edge.mc_second_id = b)
          mc.mc_second_id last.inst_id /\
      RTC (\a b. ?edge. MEM edge (ac_scan_block dfg insts NONE) /\
                       edge.mc_first_id = a /\ edge.mc_second_id = b)
          mc.mc_first_id last.inst_id /\
      ~EXISTS (\edge. edge.mc_first_id = last.inst_id)
              (ac_scan_block dfg insts NONE)
Proof
  rpt strip_tac >>
  drule ac_scan_cands_ordered >> disch_then (qspec_then `dfg` assume_tac) >>
  drule ac_scan_second_id_mem >> strip_tac >>
  drule_all ac_cands_terminal_endpoint >> strip_tac >>
  qexists_tac `j` >> gvs[EXISTS_MEM, EVERY_MEM] >>
  irule (cj 2 relationTheory.RTC_RULES) >>
  qexists_tac `i.inst_id` >> simp[] >>
  qexists_tac `mc` >> simp[]
QED
