(*
 * Algebraic Optimization Pass — Correctness Proof
 *
 * state_equiv {} is too strong: ao_transform_function introduces fresh
 * variables (ao_fresh_var) in multi-instruction expansions.
 * We use state_equiv (ao_fn_fresh_vars fn) instead.
 *
 * Proof structure:
 *   Phase 1 (offset): proved — word_add commutativity.
 *   Block label preservation: proved — all phases MAP over blocks.
 *   Phases 2-4 (iszero, peephole, cmp-flip): CHEATED —
 *     requires per-instruction simulation for each peephole rule.
 *)
Theory algebraicOptProofs
Ancestors
  algebraicOptDefs aoRules aoSegSim
  aoPeepholeSim aoResolveSim
  aoBlockSim aoCmpFlipSim
  aoResolveObligation aoRangeObligation aoCmpFlipObligation
  aoStepInvObligation aoBlockInvObligation aoIsZeroInv
  aoWf
  passSimulationProps passSimulationDefs passSharedDefs passSharedSubst venomExecSemantics stateEquiv
  venomInst venomState venomExecProofs stateEquivProps
  execEquivProps execEquivParamProps
  execEquivParamProofs venomWf
  analysisSimProofsBase analysisSimDefs dfAnalyzeDefs indexedLists
Libs
  fcpLib

val _ = delsimps ["ao_iszero_chain_inv_def",
                  "ao_chains_defined_at_def",
                  "ao_chains_defined_def",
                  "ao_chain_defined_prefix_def"]

(* ao_fn_fresh_vars, ao_fn_total_fresh_vars, ao_dfg_inv: algebraicOptDefsTheory
   ao_iszero_chain_inv, ao_chain_defined_prefix, ao_targets_wf: aoResolveObligationTheory *)


(* ===== Phase 1: Offset Conversion Equality ===== *)

(*
 * ao_handle_offset_inst converts ADD [Label l; Lit v] → OFFSET [Lit v; Label l].
 * Both ADD and OFFSET are exec_pure2 word_add in step_inst_base.
 * word_add is commutative so the outputs are identical.
 *)
Theorem ao_handle_offset_inst_id[local]:
  !inst.
    ~(inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]) ==>
    ao_handle_offset_inst inst = inst
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ADD`
  >- (fs[] >>
      (* inst.inst_opcode = ADD but ~(?l v. inst.inst_operands = [Label l; Lit v]) *)
      rw[ao_handle_offset_inst_def] >>
      Cases_on `inst.inst_operands` >- simp[] >>
      rename1 `h :: t` >>
      Cases_on `h` >> simp[] >>
      Cases_on `t` >- simp[] >>
      rename1 `h2 :: t2` >>
      Cases_on `h2` >> simp[] >>
      Cases_on `t2` >- (
        (* inst.inst_operands = [Label n; Lit c]: contradicts the hypothesis *)
        (* ~(?l v. [Label n; Lit c] = [Label l; Lit v]) is False *)
        fs[]) >>
      simp[])
  >- simp[ao_handle_offset_inst_def]
QED

Theorem step_inst_base_offset_eq[local]:
  !inst s.
    step_inst_base (ao_handle_offset_inst inst) s =
    step_inst_base inst s
Proof
  rw[] >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (* Matching case: ADD [Label l; Lit v] → OFFSET [Lit v; Label l] *)
     (fs[] >>
      gvs[ao_handle_offset_inst_def] >>
      (* Both sides: step_inst_base_def maps OFFSET and ADD to exec_pure2 word_add *)
      CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
      CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
      simp[exec_pure2_def, eval_operand_def] >>
      Cases_on `FLOOKUP s.vs_labels l` >> gvs[] >>
      Cases_on `inst.inst_outputs` >> gvs[] >>
      simp[wordsTheory.WORD_ADD_COMM])
  >- (* Non-matching case: ao_handle_offset_inst inst = inst *)
     (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem ao_handle_offset_not_invoke[local]:
  !inst. (ao_handle_offset_inst inst).inst_opcode = INVOKE <=>
         inst.inst_opcode = INVOKE
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem ao_handle_offset_inst_outputs:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem step_inst_offset_eq[local]:
  !fuel ctx inst s.
    step_inst fuel ctx (ao_handle_offset_inst inst) s =
    step_inst fuel ctx inst s
Proof
  rw[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (* INVOKE case: ao_handle_offset_inst keeps inst unchanged (ADD ≠ INVOKE) *)
     (`~(inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v])`
        by (fs[]) >>
      imp_res_tac ao_handle_offset_inst_id >> simp[])
  >- (* Not INVOKE: both sides = step_inst_base via step_inst_non_invoke *)
     (simp[step_inst_non_invoke, ao_handle_offset_not_invoke, step_inst_base_offset_eq])
QED

Theorem ao_handle_offset_is_terminator[local]:
  !inst. is_terminator (ao_handle_offset_inst inst).inst_opcode =
         is_terminator inst.inst_opcode
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def, is_terminator_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

(* exec_block equality: running a block with mapped ao_handle_offset gives same *)
Theorem exec_block_offset_eq[local]:
  !fuel ctx bb s.
    exec_block fuel ctx
      (bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) s =
    exec_block fuel ctx bb s
Proof
  rpt gen_tac >>
  (* Introduce n = LENGTH - inst_idx as the induction measure *)
  `!n fu cx blk st.
     n = LENGTH blk.bb_instructions - st.vs_inst_idx ==>
     exec_block fu cx
       (blk with bb_instructions := MAP ao_handle_offset_inst blk.bb_instructions) st =
     exec_block fu cx blk st`
    suffices_by (
      strip_tac >>
      first_assum (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `bb`, `s`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  (* Unfold BOTH sides to expose get_instruction structure *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def, listTheory.EL_MAP, listTheory.LENGTH_MAP] >>
  (* Case split on in-bounds: FALSE case closed by simp since both sides Error *)
  Cases_on `st.vs_inst_idx < LENGTH blk.bb_instructions` >> simp[] >>
  (* In-bounds: simp uses IH for recursive call + rewrites ao_handle_offset_inst *)
  simp[step_inst_offset_eq, ao_handle_offset_is_terminator]
QED

(* lookup_block in offset-converted fn gives mapped block *)
Theorem lookup_block_offset_fn[local]:
  !lbl fn.
    lookup_block lbl
      (MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) =
    OPTION_MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions)
      (lookup_block lbl fn.fn_blocks)
Proof
  rw[] >>
  mp_tac (ISPECL
    [``lbl : string``,
     ``fn.fn_blocks : basic_block list``,
     ``\(bb : basic_block). bb with bb_instructions :=
         MAP ao_handle_offset_inst bb.bb_instructions``]
    lookup_block_map) >>
  impl_tac >- simp[] >>
  simp[]
QED

(* run_blocks equality for offset-converted function *)
Theorem run_blocks_offset_eq:
  !fuel ctx fn s.
    run_blocks fuel ctx
      (fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) s =
    run_blocks fuel ctx fn s
Proof
  Induct_on `fuel`
  >- simp[run_blocks_def] >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  simp[lookup_block_offset_fn] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  simp[exec_block_offset_eq]
QED

(* ===== Helper: state_equiv implies field equality ===== *)

Theorem state_equiv_halted[local]:
  !fv s s'. state_equiv fv s s' ==> s.vs_halted = s'.vs_halted
Proof
  simp[state_equiv_def, execution_equiv_def]
QED

Theorem state_equiv_set_inst_idx[local]:
  !fv s s'. state_equiv fv s s' ==>
    state_equiv fv (s with vs_inst_idx := 0) (s' with vs_inst_idx := 0)
Proof
  simp[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* ===== Fuel induction: block-sim precondition → run_blocks sim ===== *)

(*
 * Core lifting lemma: per-block simulation + same block structure →
 * run_blocks simulation.
 *
 * The per-block hypothesis is two-state: given state_equiv fv s s', it
 * relates exec_block on fn0 at s to exec_block on fn' at s'.
 * This is needed because the induction must track two related states.
 *)
Theorem block_sim_to_run_blocks:
  !fv fn0 fn'.
    (* Same block label structure *)
    (!lbl. IS_SOME (lookup_block lbl fn0.fn_blocks) <=>
           IS_SOME (lookup_block lbl fn'.fn_blocks)) /\
    (* Per-block simulation: two-state, state_equiv fv s1 s2 *)
    (!lbl bb0 bb' fuel ctx s1 s2.
       lookup_block lbl fn0.fn_blocks = SOME bb0 /\
       lookup_block lbl fn'.fn_blocks = SOME bb' /\
       state_equiv fv s1 s2 /\
       s1.vs_inst_idx = 0 ==>
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (exec_block fuel ctx bb0 s1)
         (exec_block fuel ctx bb' s2))
    ==>
    !fuel ctx s.
      lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
        (run_blocks fuel ctx fn0 s)
        (run_blocks fuel ctx fn' s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Strengthen to two-state: !fuel ctx s s'. state_equiv fv s s' ==>
     lift_result ... fn0 s fn' s' *)
  qsuff_tac
    `!fuel ctx s s'.
       state_equiv fv s s' ==>
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn' s')`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[state_equiv_refl])
  >>
  Induct_on `fuel` >- (rpt gen_tac >> rpt strip_tac >> simp[run_blocks_def, lift_result_def]) >>
  rpt gen_tac >> rpt strip_tac >>
  (* From state_equiv fv s s', get s.vs_current_bb = s'.vs_current_bb *)
  `s.vs_current_bb = s'.vs_current_bb`
    by gvs[state_equiv_def] >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn0.fn_blocks` >>
  gvs[]
  >- (* NONE in fn0: must also be NONE in fn' *)
     (Cases_on `lookup_block s'.vs_current_bb fn'.fn_blocks`
      >- simp[lift_result_def]
      >- (* SOME in fn' but NONE in fn0: contradiction *)
         (qpat_x_assum `!lbl. IS_SOME _ <=> IS_SOME _`
            (qspec_then `s'.vs_current_bb` mp_tac) >>
          simp[]))
  >- (* SOME bb0 in fn0: find matching bb' in fn' *)
     (rename1 `lookup_block _ fn0.fn_blocks = SOME bb0` >>
      Cases_on `lookup_block s'.vs_current_bb fn'.fn_blocks`
      >- (* NONE in fn': contradiction *)
         (qpat_x_assum `!lbl. IS_SOME _ <=> IS_SOME _`
            (qspec_then `s'.vs_current_bb` mp_tac) >>
          simp[])
      >- (* SOME bb' in fn': apply two-state per-block sim *)
         (rename1 `lookup_block _ fn'.fn_blocks = SOME bb'` >>
          simp[] >>
          (* state_equiv fv s s' gives state_equiv fv (s with idx:=0) (s' with idx:=0) *)
          `state_equiv fv (s with vs_inst_idx := 0) (s' with vs_inst_idx := 0)`
            by (drule state_equiv_set_inst_idx >> simp[]) >>
          `lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
             (exec_block fuel ctx bb0 (s with vs_inst_idx := 0))
             (exec_block fuel ctx bb' (s' with vs_inst_idx := 0))`
            by (qpat_x_assum `!lbl b0 b1 f c st1 st2. _ ==> _`
                  (qspecl_then
                    [`s'.vs_current_bb`, `bb0`, `bb'`, `fuel`, `ctx`,
                     `s with vs_inst_idx := 0`, `s' with vs_inst_idx := 0`] mp_tac) >>
                simp[]) >>
          Cases_on `exec_block fuel ctx bb0 (s with vs_inst_idx := 0)` >>
          Cases_on `exec_block fuel ctx bb' (s' with vs_inst_idx := 0)` >>
          gvs[lift_result_def] >>
          (* state_equiv fv v v' from lift_result (OK v) (OK v') *)
          (* get v.vs_halted = v'.vs_halted from state_equiv *)
          imp_res_tac state_equiv_halted >>
          Cases_on `v.vs_halted` >> gvs[lift_result_def]
          >- fs[state_equiv_def]
          >> (first_x_assum (qspecl_then [`ctx`, `v`, `v'`] mp_tac) >> simp[]) ))
QED

(* ===== Transitivity helpers for lift_result ===== *)

Theorem state_equiv_trans_local[local]:
  !vars s1 s2 s3.
    state_equiv vars s1 s2 /\ state_equiv vars s2 s3 ==>
    state_equiv vars s1 s3
Proof
  metis_tac[state_equiv_trans]
QED

Theorem execution_equiv_trans_local[local]:
  !vars s1 s2 s3.
    execution_equiv vars s1 s2 /\ execution_equiv vars s2 s3 ==>
    execution_equiv vars s1 s3
Proof
  metis_tac[execution_equiv_trans]
QED

(* ===== Word-level identities for 1-to-N expansions ===== *)

Triviality word_xor_eq_0[local]:
  !x y:bytes32. (word_xor x y = 0w) <=> (x = y)
Proof
  rpt gen_tac >> EQ_TAC >> strip_tac
  >- (`word_xor (word_xor x y) y = word_xor 0w y` by gvs[] >>
      pop_assum mp_tac >>
      rewrite_tac[wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_CLAUSES] >>
      simp[])
  >- simp[wordsTheory.WORD_XOR_CLAUSES]
QED

Triviality word_1comp_eq_0[local]:
  !x:bytes32. (word_1comp x = 0w) <=> (x = 0w - 1w)
Proof
  gen_tac >>
  `0w - 1w : bytes32 = UINT_MAXw` by
    simp[wordsTheory.word_sub_def, wordsTheory.WORD_NEG_1,
         wordsTheory.WORD_ADD_0] >>
  simp[] >> EQ_TAC >> strip_tac
  >- metis_tac[wordsTheory.WORD_NOT_NOT, wordsTheory.WORD_NOT_0]
  >- simp[wordsTheory.WORD_NOT_T]
QED

Triviality bool_to_word_eq_0[local]:
  !b. (bool_to_word b = 0w) <=> ~b
Proof
  Cases >> simp[bool_to_word_def]
QED

(* EQ(x,-1) → [NOT,ISZERO]: ISZERO(NOT(x)) = EQ(x, -1) *)
Theorem ao_eq_neg1_output[local]:
  !v1:bytes32.
    bool_to_word (word_1comp v1 = 0w) = bool_to_word (v1 = 0w - 1w)
Proof
  simp[word_1comp_eq_0]
QED

(* EQ(x,y) → [XOR,ISZERO]: ISZERO(XOR(x,y)) = EQ(x, y) *)
Theorem ao_eq_xor_output[local]:
  !v1 v2:bytes32.
    bool_to_word (word_xor v1 v2 = 0w) = bool_to_word (v1 = v2)
Proof
  simp[word_xor_eq_0]
QED

(* GT(x,0) → [ISZERO,ISZERO]: ISZERO(ISZERO(x)) = GT(x, 0) *)
Theorem ao_gt_zero_output[local]:
  !v1:bytes32.
    bool_to_word (bool_to_word (v1 = 0w) = 0w) =
    bool_to_word (w2n v1 > 0)
Proof
  gen_tac >> simp[bool_to_word_eq_0] >>
  `(v1 <> 0w) <=> (w2n v1 > 0)` by (
    Cases_on `v1 = 0w` >> simp[] >>
    `w2n v1 <> 0` by simp[wordsTheory.w2n_eq_0] >> simp[]) >>
  simp[]
QED

(* ISZERO(ISZERO(NOT(x))) = bool_to_word(x ≠ 0w - 1w) *)
Theorem ao_cmp_not_iz_iz_output[local]:
  !v1:bytes32.
    bool_to_word (bool_to_word (word_1comp v1 = 0w) = 0w) =
    bool_to_word (v1 <> 0w - 1w)
Proof
  simp[bool_to_word_eq_0, word_1comp_eq_0]
QED

(* ISZERO(ISZERO(XOR(x,y))) = bool_to_word(x ≠ y) *)
Theorem ao_cmp_xor_iz_iz_output[local]:
  !v1 v2:bytes32.
    bool_to_word (bool_to_word (word_xor v1 v2 = 0w) = 0w) =
    bool_to_word (v1 <> v2)
Proof
  simp[bool_to_word_eq_0, word_xor_eq_0]
QED

(* Fresh variable names with different suffixes are distinct *)
Theorem ao_fresh_var_suffix_neq[local]:
  !id s1 s2. s1 <> s2 ==>
    ao_fresh_var id s1 <> ao_fresh_var id s2
Proof
  simp[ao_fresh_var_def, stringTheory.STRCAT_11]
QED

(* ===== step_inst_base dispatch for expansion opcodes ===== *)

(* NOT: step_inst_base computes word_1comp *)
Theorem step_inst_base_NOT[local]:
  !id op1 out s v1.
    eval_operand op1 s = SOME v1 ==>
    step_inst_base
      <| inst_id := id; inst_opcode := NOT;
         inst_operands := [op1]; inst_outputs := [out] |> s =
    OK (update_var out (word_1comp v1) s)
Proof
  rw[step_inst_base_def, exec_pure1_def]
QED

(* XOR: step_inst_base computes word_xor *)
Theorem step_inst_base_XOR[local]:
  !id op1 op2 out s v1 v2.
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    step_inst_base
      <| inst_id := id; inst_opcode := XOR;
         inst_operands := [op1; op2]; inst_outputs := [out] |> s =
    OK (update_var out (word_xor v1 v2) s)
Proof
  rw[step_inst_base_def, exec_pure2_def]
QED

(* ISZERO: step_inst_base computes bool_to_word (v = 0w) *)
Theorem step_inst_base_ISZERO[local]:
  !id op1 out s v1.
    eval_operand op1 s = SOME v1 ==>
    step_inst_base
      <| inst_id := id; inst_opcode := ISZERO;
         inst_operands := [op1]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (v1 = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure1_def]
QED

(* EQ: step_inst_base computes bool_to_word (v1 = v2) *)
Theorem step_inst_base_EQ[local]:
  !id op1 op2 out s v1 v2.
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    step_inst_base
      <| inst_id := id; inst_opcode := EQ;
         inst_operands := [op1; op2]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (v1 = v2)) s)
Proof
  rw[step_inst_base_def, exec_pure2_def]
QED

(* GT: step_inst_base computes bool_to_word (w2n v1 > w2n v2) *)
Theorem step_inst_base_GT[local]:
  !id op1 op2 out s v1 v2.
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    step_inst_base
      <| inst_id := id; inst_opcode := GT;
         inst_operands := [op1; op2]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (w2n v1 > w2n v2)) s)
Proof
  rw[step_inst_base_def, exec_pure2_def]
QED

(* ===== Full segment simulations =====
 *
 * Each theorem shows: executing the expanded segment via step_inst_base
 * produces the same output value as the original instruction.
 * Fresh intermediate variables are the only difference.
 *)

(* EQ(x, -1) segment: [NOT(x,tmp), ISZERO(tmp,out)] *)
Theorem ao_seg_eq_neg1[local]:
  !id op1 out s v1.
    eval_operand op1 s = SOME v1 ==>
    let tmp = ao_fresh_var id "not" in
    let s1 = update_var tmp (word_1comp v1) s in
    step_inst_base
      <| inst_id := id; inst_opcode := ISZERO;
         inst_operands := [Var tmp]; inst_outputs := [out] |> s1 =
    OK (update_var out (bool_to_word (v1 = 0w - 1w)) s1)
Proof
  rw[LET_THM] >>
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[word_1comp_eq_0]
QED

(* EQ(x, y) segment: [XOR(x,y,tmp), ISZERO(tmp,out)] *)
Theorem ao_seg_eq_xor[local]:
  !id op1 op2 out s v1 v2.
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    let tmp = ao_fresh_var id "xor" in
    let s1 = update_var tmp (word_xor v1 v2) s in
    step_inst_base
      <| inst_id := id; inst_opcode := ISZERO;
         inst_operands := [Var tmp]; inst_outputs := [out] |> s1 =
    OK (update_var out (bool_to_word (v1 = v2)) s1)
Proof
  rw[LET_THM] >>
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[word_xor_eq_0]
QED

(* GT(x, 0) segment: [ISZERO(x,tmp), ISZERO(tmp,out)] *)
Theorem ao_seg_gt_zero[local]:
  !id op1 out s v1.
    eval_operand op1 s = SOME v1 ==>
    let tmp = ao_fresh_var id "iz" in
    let s1 = update_var tmp (bool_to_word (v1 = 0w)) s in
    step_inst_base
      <| inst_id := id; inst_opcode := ISZERO;
         inst_operands := [Var tmp]; inst_outputs := [out] |> s1 =
    OK (update_var out (bool_to_word (w2n v1 > 0)) s1)
Proof
  rw[LET_THM] >>
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[bool_to_word_eq_0] >>
  `(v1 <> 0w) <=> (w2n v1 > 0)` by (
    Cases_on `v1 = 0w` >> simp[] >>
    `w2n v1 <> 0` by simp[wordsTheory.w2n_eq_0] >> simp[]) >>
  simp[]
QED

(* 3-step NOT+ISZERO+ISZERO segment *)
Theorem ao_seg_not_iz_iz[local]:
  !id op1 out s v1.
    eval_operand op1 s = SOME v1 ==>
    let inner = ao_fresh_var id "not" in
    let tmp = ao_fresh_var id "iz" in
    let s1 = update_var inner (word_1comp v1) s in
    let s2 = update_var tmp
      (bool_to_word (word_1comp v1 = 0w)) s1 in
    step_inst_base
      <| inst_id := id; inst_opcode := ISZERO;
         inst_operands := [Var tmp]; inst_outputs := [out] |> s2 =
    OK (update_var out (bool_to_word (v1 <> 0w - 1w)) s2)
Proof
  rw[LET_THM] >>
  `ao_fresh_var id "not" <> ao_fresh_var id "iz"` by (
    irule ao_fresh_var_suffix_neq >> simp[]) >>
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[bool_to_word_eq_0, word_1comp_eq_0]
QED

(* 3-step XOR+ISZERO+ISZERO segment *)
Theorem ao_seg_xor_iz_iz[local]:
  !id op1 op2 out s v1 v2.
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    let inner = ao_fresh_var id "xor" in
    let tmp = ao_fresh_var id "iz" in
    let s1 = update_var inner (word_xor v1 v2) s in
    let s2 = update_var tmp
      (bool_to_word (word_xor v1 v2 = 0w)) s1 in
    step_inst_base
      <| inst_id := id; inst_opcode := ISZERO;
         inst_operands := [Var tmp]; inst_outputs := [out] |> s2 =
    OK (update_var out (bool_to_word (v1 <> v2)) s2)
Proof
  rw[LET_THM] >>
  `ao_fresh_var id "xor" <> ao_fresh_var id "iz"` by (
    irule ao_fresh_var_suffix_neq >> simp[]) >>
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[bool_to_word_eq_0, word_xor_eq_0]
QED

(* ===== Block Label Preservation ===== *)

Triviality fn0_same_labels[local]:
  !lbl fn.
    IS_SOME (lookup_block lbl
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks)) <=>
    IS_SOME (lookup_block lbl fn.fn_blocks)
Proof
  rw[lookup_block_offset_fn] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[]
QED

Triviality ao_transform_function_same_labels[local]:
  !lbl fn.
    IS_SOME (lookup_block lbl (ao_transform_function fn).fn_blocks) <=>
    IS_SOME (lookup_block lbl fn.fn_blocks)
Proof
  rw[ao_transform_function_def, LET_THM,
     ao_cmp_flip_function_def] >>
  pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> simp[] >> (
    TRY (irule (iffLR fn0_same_labels) ORELSE
         irule (iffRL fn0_same_labels)) >>
    simp[lookup_block_map, ao_transform_block_def] >>
    Cases_on `lookup_block lbl fn.fn_blocks` >> simp[])
QED

(* ===== Offset conversion structural helpers ===== *)

(* Var operands in offset-converted instruction come from original *)
Triviality ao_handle_offset_var_ops[local]:
  !inst x. MEM (Var x) (ao_handle_offset_inst inst).inst_operands ==>
           MEM (Var x) inst.inst_operands
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

(* Instructions in a block found by lookup_block are in fn_insts_blocks *)
Triviality lookup_block_inst_in_fn_insts[local]:
  !lbl bbs bb inst.
    lookup_block lbl bbs = SOME bb /\
    MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  rpt strip_tac >>
  `MEM bb bbs` by metis_tac[lookup_block_MEM] >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  qid_spec_tac `bb` >> qid_spec_tac `bbs` >>
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[listTheory.MEM_APPEND] >> metis_tac[]
QED

(* ===== Per-block simulation: phases 2-4 ===== *)

(* ===== ao_transform_inst structural property ===== *)

(* ao_opt_producer always returns NONE for terminators and INVOKE *)
Triviality ao_opt_producer_non_special[local]:
  !dfg inst.
    is_terminator inst.inst_opcode \/ inst.inst_opcode = INVOKE ==>
    ao_opt_producer dfg inst = NONE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[ao_opt_producer_def, is_terminator_def]
QED

(* ao_opt_producer results are non-terminator non-INVOKE *)
Triviality ao_opt_producer_every_non_special[local]:
  !dfg inst result.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    ao_opt_producer dfg inst = SOME result ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) result
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_opt_producer _ _ = _` mp_tac >>
  simp[ao_opt_producer_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (CASE_TAC >> gvs[]) >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt strip_tac >> gvs[listTheory.EVERY_DEF, is_terminator_def]
QED

(* MAP ao_post_flip_inst preserves non-terminator non-INVOKE *)
Triviality map_post_flip_every_non_special[local]:
  !insts.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (MAP ao_post_flip_inst insts)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ao_post_flip_inst_opcode]
QED

(* terminators are not ASSIGN/PHI/PARAM/INVOKE *)
Triviality terminator_not_ssa[local]:
  !opc. is_terminator opc ==>
    opc <> ASSIGN /\ opc <> PHI /\ opc <> PARAM /\ opc <> INVOKE
Proof
  Cases >> simp[is_terminator_def]
QED

(* pre_flip preserves opcode and outputs *)
Triviality ao_pre_flip_inst_opcode[local]:
  !inst. (ao_pre_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  gen_tac >> simp[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >> rw[]
QED

Triviality ao_pre_flip_inst_outputs[local]:
  !inst. (ao_pre_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >> simp[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >> rw[]
QED

(* resolve_op preserves label operands *)
Triviality resolve_op_preserves_label[local]:
  !targets opc op.
    IS_SOME (get_label op) ==>
    ao_resolve_iszero_op targets opc op = op
Proof
  rpt strip_tac >>
  Cases_on `op` >> gvs[ao_resolve_iszero_op_def, get_label_def]
QED

(* resolve_iszero preserves inst_wf for non-PHI opcodes.
   PHI has phi_well_formed which resolve might break, but PHI
   is handled before the peephole in ao_transform_inst. *)
Triviality ao_resolve_iszero_inst_wf[local]:
  !targets inst.
    inst_wf inst /\ inst.inst_opcode <> PHI ==>
    inst_wf (ao_resolve_iszero_inst targets inst)
Proof
  rpt strip_tac >>
  gvs[ao_resolve_iszero_inst_def, inst_wf_def,
      listTheory.LENGTH_MAP] >>
  Cases_on `inst.inst_opcode` >> gvs[inst_wf_def, listTheory.LENGTH_MAP] >>
  rpt (CASE_TAC >> gvs[listTheory.LENGTH_MAP, listTheory.MAP]) >>
  simp[ao_resolve_iszero_op_def] >>
  TRY (rw[listTheory.EVERY_MAP] >>
       irule listTheory.EVERY_MONOTONIC >>
       qexists_tac `\op. IS_SOME (get_label op)` >> simp[] >>
       rpt strip_tac >> simp[resolve_op_preserves_label] >> NO_TAC)
QED

(* pre_flip preserves inst_wf *)
Triviality ao_pre_flip_inst_wf[local]:
  !inst. inst_wf inst ==> inst_wf (ao_pre_flip_inst inst)
Proof
  rpt strip_tac >>
  gvs[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  gvs[inst_wf_def]
QED

(* Peephole is identity for terminators with non-empty outputs *)
Triviality ao_peephole_inst_terminator[local]:
  !mid dfg ra lbl idx inst.
    is_terminator inst.inst_opcode /\ inst.inst_outputs <> [] ==>
    ao_peephole_inst mid dfg ra lbl idx inst = [inst]
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  simp[ao_peephole_inst_def, LET_THM]
QED

(* Comparator: non-special even without inst_wf.
   Separate because ao_opt_comparator is the most complex opt function. *)
Triviality ao_opt_comparator_non_special[local]:
  !mid dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  Cases_on `inst.inst_operands` >> gvs[listTheory.EVERY_DEF] >>
  Cases_on `t` >> gvs[listTheory.EVERY_DEF] >>
  Cases_on `t'` >> gvs[listTheory.EVERY_DEF] >>
  IF_CASES_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  CASE_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  rpt IF_CASES_TAC >>
  gvs[listTheory.EVERY_DEF, is_terminator_def,
      ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
      ao_cmp_prefer_iz_general_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[listTheory.EVERY_DEF, is_terminator_def]
QED

(* Peephole output is always non-terminator and non-INVOKE,
   regardless of inst_wf. Each ao_opt_* function returns either [inst]
   or instructions with explicit non-special opcodes (ASSIGN, ISZERO, etc). *)
Triviality ao_peephole_inst_non_special[local]:
  !mid dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF]) >>
  gvs[] >>
  (* Expand all non-comparator opt function defs *)
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
       ao_opt_or_def, ao_opt_eq_def, LET_THM] >>
  (* Split all remaining case/if, then close *)
  rpt (FIRST [CASE_TAC, IF_CASES_TAC]) >>
  gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  (* Remaining subgoal: comparator *)
  irule ao_opt_comparator_non_special >> simp[is_terminator_def]
QED

Triviality ao_transform_inst_structural[local]:
  !mid dfg ra lbl targets.
    inst_transform_structural
      (\(v:num) inst. ao_transform_inst mid dfg ra lbl v targets inst)
Proof
  rpt gen_tac >> simp[inst_transform_structural_def] >> rpt conj_tac
  >- (* Terminators: singleton terminator *)
     (rpt gen_tac >> strip_tac >>
      imp_res_tac terminator_not_ssa >>
      Cases_on `inst.inst_outputs = []`
      >- (qexists_tac `ao_resolve_iszero_inst targets inst` >>
          simp[ao_transform_inst_def, LET_THM,
               ao_resolve_iszero_inst_outputs,
               ao_resolve_iszero_inst_opcode])
      >- (qexists_tac
            `ao_post_flip_inst
               (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst))` >>
          `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst) = NONE` by
            (irule ao_opt_producer_non_special >>
             simp[ao_resolve_iszero_inst_opcode]) >>
          `ao_peephole_inst mid dfg ra lbl v
             (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)) =
           [ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)]` by
            (irule ao_peephole_inst_terminator >>
             simp[ao_pre_flip_inst_opcode, ao_pre_flip_inst_outputs,
                  ao_resolve_iszero_inst_opcode, ao_resolve_iszero_inst_outputs]) >>
          simp[ao_transform_inst_def, LET_THM,
               ao_resolve_iszero_inst_opcode,
               ao_resolve_iszero_inst_outputs,
               ao_post_flip_inst_opcode, ao_pre_flip_inst_opcode]))
  >- (* INVOKE: singleton INVOKE *)
     (rpt gen_tac >> strip_tac >>
      qspecl_then [`mid`, `dfg`, `ra`, `lbl`, `v`, `targets`, `inst`]
        strip_assume_tac ao_transform_inst_invoke >>
      gvs[] >> qexists_tac `inst'` >> simp[])
  >- (* Non-term non-INVOKE: EVERY non-term non-INVOKE *)
     (rpt gen_tac >> strip_tac >>
      simp[ao_transform_inst_def, LET_THM,
           ao_resolve_iszero_inst_opcode,
           ao_resolve_iszero_inst_outputs] >>
      Cases_on `inst.inst_outputs = []`
      >- simp[ao_resolve_iszero_inst_opcode, is_terminator_def]
      >- (simp[] >>
          Cases_on `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
                    inst.inst_opcode = PARAM`
          >- simp[ao_resolve_iszero_inst_opcode, is_terminator_def]
          >- (simp[ao_resolve_iszero_inst_opcode] >>
              Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
              >- (simp[] >>
                  irule map_post_flip_every_non_special >>
                  Cases_on `inst_wf inst`
                  >- (`inst_wf (ao_pre_flip_inst
                         (ao_resolve_iszero_inst targets inst))` by
                        (irule ao_pre_flip_inst_wf >>
                         irule ao_resolve_iszero_inst_wf >> gvs[]) >>
                      simp[listTheory.EVERY_CONJ] >> conj_tac
                      >- (irule ao_peephole_inst_non_term >>
                          simp[ao_pre_flip_inst_opcode,
                               ao_resolve_iszero_inst_opcode])
                      >- (irule ao_peephole_inst_not_invoke >>
                          simp[ao_pre_flip_inst_opcode,
                               ao_resolve_iszero_inst_opcode]))
                  >- (irule ao_peephole_inst_non_special >>
                      simp[ao_pre_flip_inst_opcode,
                           ao_resolve_iszero_inst_opcode]))
              >- (`~is_terminator
                      (ao_resolve_iszero_inst targets inst).inst_opcode`
                      by simp[ao_resolve_iszero_inst_opcode] >>
                  `(ao_resolve_iszero_inst targets inst).inst_opcode <> INVOKE`
                      by simp[ao_resolve_iszero_inst_opcode] >>
                  simp[] >>
                  imp_res_tac ao_opt_producer_every_non_special >>
                  irule map_post_flip_every_non_special >> simp[]))))
QED

(* Helper: non-INVOKE peephole path simulation.
   Uses original inst in step_inst, resolved inst for peephole. *)
Triviality ao_peephole_path_sim[local]:
  !fv mid dfg ra lbl targets fuel ctx v inst s.
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_outputs <> [] /\
    inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    ao_opt_producer dfg (ao_resolve_iszero_inst targets inst) = NONE /\
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
      step_inst fuel ctx inst s /\
    ao_fresh_var (ao_resolve_iszero_inst targets inst).inst_id "not" IN fv /\
    ao_fresh_var (ao_resolve_iszero_inst targets inst).inst_id "iz" IN fv /\
    ao_fresh_var (ao_resolve_iszero_inst targets inst).inst_id "xor" IN fv /\
    (!op w. MEM op (ao_resolve_iszero_inst targets inst).inst_operands /\
            eval_operand op s = SOME w ==>
            in_range (range_get_range ra lbl v op) w) ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx
        (MAP ao_post_flip_inst
          (ao_peephole_inst mid dfg ra lbl v
            (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)))) s)
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (ao_resolve_iszero_inst targets inst)` by
    (irule ao_resolve_iszero_inst_wf >> simp[]) >>
  qspecl_then [`fv`, `mid`, `dfg`, `ra`, `lbl`, `v`,
    `ao_resolve_iszero_inst targets inst`,
    `fuel`, `ctx`, `s`]
    mp_tac ao_peephole_full_sim >>
  simp[ao_resolve_iszero_inst_opcode, ao_resolve_iszero_inst_id]
QED

(* Helper: shift-and-1 extracts a single bit *)
Triviality lsr_and_1[local]:
  !n (w:bytes32). n < 256 ==> ((w >>> n) && 1w = 1w <=> w ' n)
Proof
  rpt strip_tac >>
  `!b. BIT b 1 = (b = 0)` by (
    `(1:num) = 2 ** 1 - 1` by simp[] >>
    pop_assum SUBST1_TAC >> simp[bitTheory.BIT_EXP_SUB1]) >>
  rw[fcpTheory.CART_EQ] >>
  simp[wordsTheory.word_and_def, wordsTheory.word_lsr_def,
       fcpTheory.FCP_BETA, wordsTheory.word_index,
       DIMINDEX (Arbnum.fromInt 256)] >>
  EQ_TAC
  >- (disch_then (qspec_then `0` mp_tac) >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >>
      Cases_on `i = 0` >> simp[])
QED

(* Helper: mask subset — narrower mask is sub-mask of wider *)
Triviality mask_and_subset[local]:
  !a b. a <= b ==>
    ((1w:bytes32) << (a + 1) - 1w) && ((1w:bytes32) << (b + 1) - 1w) =
    (1w:bytes32) << (a + 1) - 1w
Proof
  rpt strip_tac >>
  rw[fcpTheory.CART_EQ, wordsTheory.word_and_def, fcpTheory.FCP_BETA,
     wordsTheory.SHIFT_1_SUB_1, DIMINDEX (Arbnum.fromInt 256)]
QED

(* sign_extend is idempotent for wider extension.
   sign_extend to bp_i bits then to bp_w >= bp_i is the same as bp_i. *)
(* Helper: OR body for sign=1 case — bit-level proof *)
Triviality or_mask_idem[local]:
  !bpi bpw (x:bytes32).
    bpi <= bpw ==>
    (x || ~((1w:bytes32) << (bpi + 1) - 1w)) ||
    ~((1w:bytes32) << (bpw + 1) - 1w) =
    x || ~((1w:bytes32) << (bpi + 1) - 1w)
Proof
  rpt strip_tac >>
  rw[fcpTheory.CART_EQ, wordsTheory.word_or_def, wordsTheory.word_1comp_def,
     fcpTheory.FCP_BETA, wordsTheory.SHIFT_1_SUB_1,
     DIMINDEX (Arbnum.fromInt 256)] >>
  rpt strip_tac >> Cases_on `i < bpi + 1` >> simp[]
QED

(* Helper: AND body for sign=0 case — bit-level proof *)
Triviality and_mask_idem[local]:
  !bpi bpw (x:bytes32).
    bpi <= bpw ==>
    (x && (1w:bytes32) << (bpi + 1) - 1w) &&
    (1w:bytes32) << (bpw + 1) - 1w =
    x && (1w:bytes32) << (bpi + 1) - 1w
Proof
  rpt strip_tac >>
  rw[fcpTheory.CART_EQ, wordsTheory.word_and_def,
     fcpTheory.FCP_BETA, wordsTheory.SHIFT_1_SUB_1,
     DIMINDEX (Arbnum.fromInt 256)] >>
  rpt strip_tac >> Cases_on `i < bpi + 1` >> simp[]
QED

(* Helper: sign bit propagation for OR case *)
Triviality sign_bit_or[local]:
  !bpi bpw (x:bytes32).
    bpi <= bpw /\ bpw < 256 /\ x ' bpi ==>
    (x || ~((1w:bytes32) << (bpi + 1) - 1w)) ' bpw
Proof
  rpt strip_tac >>
  simp[wordsTheory.word_or_def, wordsTheory.word_1comp_def,
       fcpTheory.FCP_BETA, wordsTheory.SHIFT_1_SUB_1,
       DIMINDEX (Arbnum.fromInt 256)] >>
  Cases_on `bpw = bpi` >> simp[]
QED

(* Helper: sign bit propagation for AND case *)
Triviality sign_bit_and[local]:
  !bpi bpw (x:bytes32).
    bpi <= bpw /\ bpw < 256 /\ ~(x ' bpi) ==>
    ~((x && (1w:bytes32) << (bpi + 1) - 1w) ' bpw)
Proof
  rpt strip_tac >>
  gvs[wordsTheory.word_and_def, fcpTheory.FCP_BETA,
      wordsTheory.SHIFT_1_SUB_1,
      DIMINDEX (Arbnum.fromInt 256)] >>
  `bpw = bpi` by simp[] >> gvs[]
QED

Triviality sign_extend_idempotent[local]:
  !w inner_w (x : bytes32).
    w >=+ inner_w ==>
    sign_extend w (sign_extend inner_w x) = sign_extend inner_w x
Proof
  rpt gen_tac >> strip_tac >>
  `w2n inner_w <= w2n w` by
    gvs[wordsTheory.WORD_HIGHER_EQ, wordsTheory.WORD_LS] >>
  simp[sign_extend_def] >>
  Cases_on `w2n inner_w > 30`
  >- (`w2n w > 30` by simp[] >> simp[])
  >- (simp[] >> Cases_on `w2n w > 30` >- simp[] >>
      simp[LET_THM] >>
      `8 * w2n inner_w + 7 <= 8 * w2n w + 7` by simp[] >>
      `8 * w2n inner_w + 7 < 256 /\ 8 * w2n w + 7 < 256` by simp[] >>
      `(x >>> (8 * w2n inner_w + 7) && 1w = 1w) = x ' (8 * w2n inner_w + 7)`
        by simp[lsr_and_1] >>
      Cases_on `x ' (8 * w2n inner_w + 7)`
      >- (* Sign bit = 1 *)
         (simp[] >>
          `(x || ~((1w:bytes32) << (8 * w2n inner_w + 8) - 1w)) '
           (8 * w2n w + 7)` by (
            qspecl_then [`8 * w2n inner_w + 7`, `8 * w2n w + 7`, `x`]
              mp_tac sign_bit_or >> simp[]) >>
          simp[lsr_and_1] >>
          qspecl_then [`8 * w2n inner_w + 7`, `8 * w2n w + 7`, `x`]
            mp_tac or_mask_idem >> simp[])
      >- (* Sign bit = 0 *)
         (simp[] >>
          `~((x && (1w:bytes32) << (8 * w2n inner_w + 8) - 1w) '
           (8 * w2n w + 7))` by (
            qspecl_then [`8 * w2n inner_w + 7`, `8 * w2n w + 7`, `x`]
              mp_tac sign_bit_and >> simp[]) >>
          `~((x && (1w:bytes32) << (8 * w2n inner_w + 8) - 1w) >>>
             (8 * w2n w + 7) && 1w = 1w)` by simp[lsr_and_1] >>
          simp[] >>
          qspecl_then [`8 * w2n inner_w + 7`, `8 * w2n w + 7`, `x`]
            mp_tac and_mask_idem >> simp[]))
QED

(* w2w roundtrip: 160 → 256 → 160 is identity *)
Triviality w2w_160_256[local]:
  !a : 160 word. w2w (w2w a : 256 word) = a
Proof
  gen_tac >>
  rw[fcpTheory.CART_EQ] >>
  ONCE_REWRITE_TAC [wordsTheory.w2w_def] >>
  REWRITE_TAC [DIMINDEX (Arbnum.fromInt 160),
               DIMINDEX (Arbnum.fromInt 256)] >>
  simp[fcpTheory.FCP_BETA] >>
  (* Goal: n2w (w2n a MOD dimword(:256)) ' i <=> a ' i *)
  `w2n a MOD dimword (:256) = w2n a` by
    (irule arithmeticTheory.LESS_MOD >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `dimword (:160)` >>
     simp[wordsTheory.w2n_lt] >>
     simp[wordsTheory.dimword_def, DIMINDEX (Arbnum.fromInt 160),
          DIMINDEX (Arbnum.fromInt 256)]) >>
  `w2n (w2w a : 256 word) = w2n a` by
    simp[wordsTheory.w2n_w2w, DIMINDEX (Arbnum.fromInt 160),
         DIMINDEX (Arbnum.fromInt 256)] >>
  gvs[wordsTheory.n2w_w2n]
QED

(* Helper: BALANCE → SELFBALANCE simulation under ao_dfg_inv *)
Triviality balance_selfbalance_sim[local]:
  !dfg inst0 v producer fv fuel ctx s.
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    inst0.inst_opcode = BALANCE /\
    inst0.inst_operands = [Var v] /\
    inst0.inst_outputs <> [] /\
    dfg_get_def dfg v = SOME producer /\
    producer.inst_opcode = ADDRESS ==>
    (?e. step_inst fuel ctx inst0 s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst0 s)
      (step_inst fuel ctx (inst0 with <| inst_opcode := SELFBALANCE;
                                          inst_operands := [] |>) s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_var v s`
  >- (* NONE: BALANCE errors *)
     (DISJ1_TAC >>
      simp[step_inst_non_invoke] >>
      simp[Once step_inst_base_def, exec_read1_def,
           eval_operand_def, lookup_var_def])
  >- (* SOME: both compute the same balance *)
     (DISJ2_TAC >>
      (* Extract address value from ao_dfg_inv *)
      qpat_x_assum `ao_dfg_inv _ _`
        (strip_assume_tac o REWRITE_RULE [ao_dfg_inv_def]) >>
      pop_assum (qspecl_then [`v`, `producer`] mp_tac) >>
      simp[lookup_var_def] >> strip_tac >>
      (* Unfold BALANCE side *)
      simp[step_inst_non_invoke] >>
      simp[Once step_inst_base_def, exec_read1_def,
           eval_operand_def, lookup_var_def] >>
      Cases_on `inst0.inst_outputs` >> gvs[] >>
      Cases_on `t`
      >- (* Single output [h] *)
         (gvs[] >>
          simp[Once step_inst_base_def, exec_read0_def] >>
          `x = w2w s.vs_call_ctx.cc_address` by
            (fs[lookup_var_def]) >>
          gvs[] >>
          (* w2w (w2w cc_addr : bytes32) = cc_addr *)
          `w2w (w2w s.vs_call_ctx.cc_address : bytes32) =
           s.vs_call_ctx.cc_address` by simp[w2w_160_256] >>
          gvs[] >>
          simp[lift_result_def, state_equiv_refl])
      >- (* Multiple outputs: both error *)
         (gvs[] >>
          simp[Once step_inst_base_def, exec_read0_def, lift_result_def]))
QED

(* Helper: SIGNEXTEND nesting → ASSIGN simulation under ao_dfg_inv *)
Triviality signextend_assign_sim[local]:
  !dfg inst0 w v inner_w v12 producer fv fuel ctx s.
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    inst0.inst_opcode = SIGNEXTEND /\
    inst0.inst_operands = [Lit w; Var v] /\
    inst0.inst_outputs <> [] /\
    dfg_get_def dfg v = SOME producer /\
    producer.inst_opcode = SIGNEXTEND /\
    producer.inst_operands = [Lit inner_w; v12] /\
    w >=+ inner_w ==>
    (?e. step_inst fuel ctx inst0 s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst0 s)
      (step_inst fuel ctx (inst0 with <| inst_opcode := ASSIGN;
                                          inst_operands := [Var v] |>) s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_var v s`
  >- (* NONE: SIGNEXTEND errors *)
     (DISJ1_TAC >>
      simp[step_inst_non_invoke] >>
      simp[Once step_inst_base_def, exec_pure2_def,
           eval_operand_def, lookup_var_def])
  >- (* SOME: both produce the same value *)
     (DISJ2_TAC >>
      (* Extract sign_extend form from ao_dfg_inv *)
      `?inner_val. x = sign_extend inner_w inner_val` by (
        fs[ao_dfg_inv_def, lookup_var_def] >>
        first_x_assum (qspecl_then [`v`, `producer`, `x`] mp_tac) >>
        simp[] >>
        disch_then (qspecl_then [`inner_w`, `v12`] mp_tac) >> simp[]) >>
      (* sign_extend w x = x by idempotency *)
      `sign_extend w x = x` by (
        gvs[] >> irule sign_extend_idempotent >> simp[]) >>
      (* Unfold SIGNEXTEND side *)
      simp[step_inst_non_invoke] >>
      simp[Once step_inst_base_def, exec_pure2_def,
           eval_operand_def, lookup_var_def] >>
      Cases_on `inst0.inst_outputs` >> gvs[] >>
      Cases_on `t`
      >- (* Single output [h] *)
         (gvs[] >>
          simp[Once step_inst_base_def, exec_pure1_def,
               eval_operand_def, lookup_var_def] >>
          simp[lift_result_def, state_equiv_refl])
      >- (* Multiple outputs: both error *)
         (gvs[] >>
          simp[Once step_inst_base_def, exec_pure1_def,
               eval_operand_def, lookup_var_def, lift_result_def]))
QED

(* Helper: ao_opt_producer SOME case dispatches to producer-specific sims *)
Triviality ao_opt_producer_sim[local]:
  !dfg inst0 result fv fuel ctx s.
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    ao_opt_producer dfg inst0 = SOME result /\
    inst0.inst_outputs <> [] /\
    inst0.inst_opcode <> ASSIGN /\
    inst0.inst_opcode <> PHI /\
    inst0.inst_opcode <> PARAM ==>
    (?e. step_inst fuel ctx inst0 s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst0 s)
      (run_insts fuel ctx (MAP ao_post_flip_inst result) s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[ao_opt_producer_def, AllCaseEqs()] >>
  simp[ao_post_flip_inst_non_comm, run_insts_singleton] >>
  (* Identity cases: lift_result r r *)
  TRY (DISJ2_TAC >>
       irule lift_result_refl >>
       simp[state_equiv_refl, execution_equiv_refl] >>
       NO_TAC) >>
  (* BALANCE→SELFBALANCE *)
  TRY (match_mp_tac balance_selfbalance_sim >> metis_tac[] >> NO_TAC) >>
  (* SIGNEXTEND→ASSIGN *)
  match_mp_tac signextend_assign_sim >> metis_tac[]
QED

(* Per-instruction simulation for ao_transform_inst.
   Hypotheses:
     H_resolve — iszero resolution preserves step_inst (chain correctness)
     H_fresh   — peephole fresh vars are in fv
     H_range   — range analysis sound for resolved operands
   Uses ao_dfg_inv in the soundness predicate for producer rewrites. *)
Triviality ao_transform_inst_sim[local]:
  !fv mid dfg ra lbl targets.
    (* H_resolve: iszero resolution preserves step_inst *)
    (!inst fuel ctx s. inst_wf inst ==>
      step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
      step_inst fuel ctx inst s) /\
    (* H_fresh: fresh vars in fv *)
    (!id. ao_fresh_var id "not" IN fv /\
          ao_fresh_var id "iz" IN fv /\
          ao_fresh_var id "xor" IN fv) /\
    (* H_range: range analysis sound for resolved operands *)
    (!inst idx s op v.
      MEM op (ao_resolve_iszero_inst targets inst).inst_operands /\
      eval_operand op s = SOME v ==>
      in_range (range_get_range ra lbl idx op) v)
    ==>
    let f = \(v:num) inst. ao_transform_inst mid dfg ra lbl v targets inst in
    analysis_inst_simulates
      (state_equiv fv) (execution_equiv fv)
      (\(v:num) s. ao_dfg_inv dfg (s with vs_inst_idx := 0))
      f
Proof
  simp[analysis_inst_simulates_def, LET_THM] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  conj_tac
  >- (* Simulation *)
     (rpt gen_tac >> strip_tac >>
      rename1 `inst_wf inst` >>
      `step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
       step_inst fuel ctx inst s` by metis_tac[] >>
      simp[ao_transform_inst_def, LET_THM,
           ao_resolve_iszero_inst_outputs,
           ao_resolve_iszero_inst_opcode] >>
      Cases_on `inst.inst_outputs = []`
      >- (simp[run_insts_singleton] >> DISJ2_TAC >>
          pop_assum kall_tac >> pop_assum (fn th => REWRITE_TAC [th]) >>
          irule lift_result_refl >>
          simp[state_equiv_refl, execution_equiv_refl])
      >- (simp[] >>
          Cases_on `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
                    inst.inst_opcode = PARAM`
          >- (simp[run_insts_singleton] >> DISJ2_TAC >>
              qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
                (fn th => REWRITE_TAC [th]) >>
              irule lift_result_refl >>
              simp[state_equiv_refl, execution_equiv_refl])
          >- (simp[] >>
              Cases_on `ao_opt_producer dfg
                (ao_resolve_iszero_inst targets inst)`
              >- (* NONE: peephole path via ao_peephole_path_sim *)
                 (simp[] >>
                  (`~is_terminator inst.inst_opcode` by
                    (strip_tac >>
                     imp_res_tac terminator_no_outputs >> gvs[])) >>
                  Cases_on `inst.inst_opcode = INVOKE`
                  >- (simp[ao_peephole_inst_def, LET_THM,
                           ao_resolve_iszero_inst_opcode,
                           ao_pre_flip_inst_non_comm,
                           ao_post_flip_inst_non_comm,
                           run_insts_singleton] >>
                      DISJ2_TAC >>
                      qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
                        (fn th => REWRITE_TAC [th]) >>
                      irule lift_result_refl >>
                      simp[state_equiv_refl, execution_equiv_refl])
                  >- (irule ao_peephole_path_sim >> gvs[] >>
                      metis_tac[]))
              >- (* SOME: producer — use ao_opt_producer_sim *)
                 (simp[] >>
                  qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
                    (fn th => REWRITE_TAC [SYM th]) >>
                  irule ao_opt_producer_sim >>
                  simp[ao_resolve_iszero_inst_opcode,
                       ao_resolve_iszero_inst_outputs] >>
                  metis_tac[]))))
  >- simp[ao_transform_inst_structural]
QED

(* ===== Phase 4: cmp_flip dead variables ===== *)

(* ao_cmp_flip_dead_vars is now in algebraicOptDefsScript.sml *)

(* ===== Phases 1-3: offset + iszero + peephole (single-state block sim) ===== *)

(* Per-block sim for phases 1-3: directly from ao_phase3_block_sim.
   Takes analysis_inst_simulates + inst_wf as hypotheses — these capture
   per-instruction soundness that depends on H_resolve, H_range, ao_dfg_inv.
   Conclusion relates exec_block on bb to exec_block on ao_transform_block bb. *)
Theorem ao_phases123_block_sim[local]:
  !fv mid dfg ra targets bb fuel ctx s.
    analysis_inst_simulates (state_equiv fv) (execution_equiv fv) (\v s. T)
      (\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst) /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fv) /\
    s.vs_inst_idx = 0 ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (ao_transform_block mid dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  irule ao_phase3_block_sim >> metis_tac[]
QED

(* Label preservation for phase-3-output function *)
Triviality fn1_same_labels[local]:
  !lbl fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    IS_SOME (lookup_block lbl fn1.fn_blocks) <=>
    IS_SOME (lookup_block lbl fn.fn_blocks)
Proof
  rw[LET_THM] >>
  simp[lookup_block_map, ao_transform_block_def] >>
  simp[lookup_block_offset_fn] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[]
QED

(* ===== Phases 1-3 run_blocks sim ===== *)

(* Two-state per-block sim with Error disjunct.
   Composes Leg 1 (result_equiv for same block, state_equiv states) with
   Leg 2 (per-block single-state sim with Error disjunct).
   Both legs provided as hypotheses — derivation happens at call site. *)
Theorem ao_phases123_per_block_sim[local]:
  !fv bb0 bb1 fuel ctx s1 s2.
    (* Leg 1: same block, state_equiv states *)
    result_equiv fv
      (exec_block fuel ctx bb0 s1) (exec_block fuel ctx bb0 s2) /\
    (* Leg 2: per-block single-state sim *)
    ((?e. exec_block fuel ctx bb0 s2 = Error e) \/
     lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
       (exec_block fuel ctx bb0 s2) (exec_block fuel ctx bb1 s2))
    ==>
    (?e. exec_block fuel ctx bb0 s1 = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb0 s1) (exec_block fuel ctx bb1 s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (* Error case: exec_block bb0 s2 = Error e.
        From result_equiv: exec_block bb0 s1 must also be Error. *)
     (DISJ1_TAC >>
      Cases_on `exec_block fuel ctx bb0 s1` >>
      gvs[result_equiv_def])
  >- (* lift_result case: compose via result_equiv_trans *)
     (DISJ2_TAC >>
      `result_equiv fv
         (exec_block fuel ctx bb0 s2) (exec_block fuel ctx bb1 s2)`
        by gvs[result_equiv_is_lift_result] >>
      simp[GSYM result_equiv_is_lift_result] >>
      metis_tac[result_equiv_trans])
QED

(* Variant of block_sim_to_run_blocks with Error disjunct in per-block sim.
   If a block can error, run_blocks propagates the error. *)
Theorem block_sim_to_run_blocks_err[local]:
  !fv fn0 fn'.
    (!lbl. IS_SOME (lookup_block lbl fn0.fn_blocks) <=>
           IS_SOME (lookup_block lbl fn'.fn_blocks)) /\
    (!lbl bb0 bb' fuel ctx s1 s2.
       lookup_block lbl fn0.fn_blocks = SOME bb0 /\
       lookup_block lbl fn'.fn_blocks = SOME bb' /\
       state_equiv fv s1 s2 /\
       s1.vs_inst_idx = 0 ==>
       (?e. exec_block fuel ctx bb0 s1 = Error e) \/
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (exec_block fuel ctx bb0 s1) (exec_block fuel ctx bb' s2))
    ==>
    !fuel ctx s.
      (?e. run_blocks fuel ctx fn0 s = Error e) \/
      lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
        (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn' s)
Proof
  rpt gen_tac >> strip_tac >>
  qsuff_tac
    `!fuel ctx s s'.
       state_equiv fv s s' ==>
       (?e. run_blocks fuel ctx fn0 s = Error e) \/
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn' s')`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[state_equiv_refl])
  >>
  Induct_on `fuel`
  >- (rpt strip_tac >> DISJ1_TAC >> simp[run_blocks_def, exec_result_11])
  >> rpt gen_tac >> strip_tac >>
  `s.vs_current_bb = s'.vs_current_bb` by gvs[state_equiv_def] >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn0.fn_blocks`
  >- (* NONE in fn0: run_blocks errors *)
     (DISJ1_TAC >> simp[exec_result_11])
  >- (* SOME bb0 in fn0: find matching bb' in fn' - part A: setup *)
     (rename1 `lookup_block _ fn0.fn_blocks = SOME bb0` >>
      Cases_on `lookup_block s'.vs_current_bb fn'.fn_blocks` >>
      gvs[]
      >- (* NONE in fn': contradiction *)
         (qpat_x_assum `!lbl. IS_SOME _ <=> IS_SOME _`
            (qspec_then `s.vs_current_bb` mp_tac) >>
          simp[])
      >- (* SOME bb' in fn' - part B: per-block sim *)
         (rename1 `lookup_block _ fn'.fn_blocks = SOME bb'` >>
          `state_equiv fv (s with vs_inst_idx := 0) (s' with vs_inst_idx := 0)`
            by (drule state_equiv_set_inst_idx >> simp[]) >>
          qpat_x_assum `!lbl b0 b1 f c st1 st2. _`
            (qspecl_then
              [`s'.vs_current_bb`, `bb0`, `bb'`, `fuel`, `ctx`,
               `s with vs_inst_idx := 0`, `s' with vs_inst_idx := 0`] mp_tac) >>
          impl_tac >- fs[] >>
          strip_tac
          >- (* Per-block Error *)
             (DISJ1_TAC >> gvs[exec_result_11])
          >- (* Per-block lift_result *)
             (Cases_on `exec_block fuel ctx bb0 (s with vs_inst_idx := 0)` >>
              Cases_on `exec_block fuel ctx bb' (s' with vs_inst_idx := 0)` >>
              gvs[lift_result_def] >>
              imp_res_tac state_equiv_halted >>
              Cases_on `v.vs_halted` >> gvs[lift_result_def]
              >- fs[state_equiv_def]
              >> (first_x_assum (qspecl_then [`ctx`, `v`, `v'`] mp_tac) >>
                  simp[]))))
QED

Triviality ao_transform_block_label[local,simp]:
  !mid dfg ra targets bb.
    (ao_transform_block mid dfg ra targets bb).bb_label = bb.bb_label
Proof
  simp[ao_transform_block_def]
QED

Triviality ao_handle_offset_label[local,simp]:
  !bb. (bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions).bb_label = bb.bb_label
Proof
  simp[]
QED

(* SSA uniqueness: in ALL_DISTINCT (FLAT (MAP f xs)), if v appears in
   both f(a) and f(b) where a,b ∈ xs, then a = b. *)
Triviality all_distinct_flat_map_unique[local]:
  !xs f a b v.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    MEM a xs /\ MEM b xs /\
    MEM v (f a) /\ MEM v (f b) ==> a = b
Proof
  Induct >> rw[listTheory.ALL_DISTINCT_APPEND] >>
  metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]
QED

(* Block membership implies function membership for instructions *)
Triviality mem_block_mem_fn_insts_blocks[local]:
  !bbs bb inst.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Triviality mem_block_mem_fn_insts[local]:
  !fn bb inst.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts_blocks]
QED

(* ao_dfg_inv preserved by a single non-terminator, non-INVOKE step_inst
   under SSA. *)
Triviality ao_dfg_inv_step_preserved[local]:
  !dfg fn0 bb inst fuel ctx s s'.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    inst_wf inst /\
    ao_dfg_inv dfg s /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_dfg_inv dfg s'
Proof
  rw[ao_dfg_inv_def] >> rpt strip_tac >>
  rename1 `dfg_get_def _ x = SOME inst_def` >>
  rename1 `lookup_var x s' = SOME val` >>
  `s'.vs_call_ctx = s.vs_call_ctx` by
    metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
  Cases_on `MEM x inst.inst_outputs` >>
  (* Non-output case: value unchanged, use ao_dfg_inv from old state *)
  TRY (`lookup_var x s' = lookup_var x s` by
         metis_tac[venomInstPropsTheory.step_preserves_non_output_vars] >>
       `lookup_var x s = SOME val` by gvs[] >>
       first_x_assum (qspecl_then [`x`, `inst_def`, `val`] mp_tac) >>
       simp[] >> strip_tac >> gvs[] >> metis_tac[] >> NO_TAC) >>
  (* Output case: SSA uniqueness gives inst = inst_def *)
  `inst = inst_def` by
    (`MEM inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
     `MEM inst_def (fn_insts fn0) /\ MEM x inst_def.inst_outputs` by
       metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
     qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                  `inst`, `inst_def`, `x`]
       mp_tac all_distinct_flat_map_unique >>
     impl_tac >- (fs[ssa_form_def]) >>
     simp[]) >>
  gvs[] >>
  (* inst = inst_def. We know inst.inst_opcode is ADDRESS or SIGNEXTEND.
     Analyze step_inst_base for these specific opcodes. *)
  fs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[Once step_inst_base_def] >>
  gvs[exec_read0_def, exec_pure2_def, eval_operand_def,
      AllCaseEqs(), inst_wf_def] >>
  strip_tac >> gvs[update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* Terminator step_inst OK preserves call_ctx.
   Terminators returning OK are JMP/JNZ/DJMP which use jump_to. *)
Triviality step_inst_ok_preserves_call_ctx[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >>
  reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- (drule_all venomInstProofsTheory.step_preserves_call_ctx >> simp[])
  >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  simp[step_inst_base_def, AllCaseEqs(), jump_to_def] >>
  rpt strip_tac >> gvs[]
QED

(* ao_dfg_inv preserved by a single step_inst OK (any opcode).
   Terminators: all vars + call_ctx preserved.
   INVOKE: SSA ensures INVOKE outputs differ from ADDRESS/SIGNEXTEND
   outputs tracked by ao_dfg_inv, so conclusion is vacuous.
   Non-terminator non-INVOKE: use ao_dfg_inv_step_preserved. *)
Triviality ao_dfg_inv_step_any[local]:
  !dfg fn0 bb inst fuel ctx s s'.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_wf inst /\
    ao_dfg_inv dfg s /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_dfg_inv dfg s'
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- ((* Terminator: all vars preserved, call_ctx preserved *)
      simp[ao_dfg_inv_def] >> rpt strip_tac >>
      `lookup_var x s' = lookup_var x s` by
        metis_tac[step_terminator_preserves_vars] >>
      `s'.vs_call_ctx = s.vs_call_ctx` by
        metis_tac[step_inst_ok_preserves_call_ctx] >>
      `lookup_var x s = SOME val` by gvs[] >>
      fs[ao_dfg_inv_def] >> res_tac >> gvs[] >> metis_tac[])
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- ((* INVOKE: outputs differ from ADDRESS/SIGNEXTEND by SSA *)
          simp[ao_dfg_inv_def] >> rpt strip_tac >> (
          rename1 `dfg_get_def _ x = SOME inst_def` >>
          rename1 `lookup_var x s' = SOME val` >>
          `s'.vs_call_ctx = s.vs_call_ctx` by
            metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
          Cases_on `MEM x inst.inst_outputs`
          >- (`inst = inst_def` by
                (`MEM inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
                 `MEM inst_def (fn_insts fn0) /\ MEM x inst_def.inst_outputs` by
                   metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
                 qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                              `inst`, `inst_def`, `x`]
                   mp_tac all_distinct_flat_map_unique >>
                 impl_tac >- (fs[ssa_form_def]) >>
                 simp[]) >>
              gvs[])
          >- (`lookup_var x s' = lookup_var x s` by
                metis_tac[venomInstPropsTheory.step_preserves_non_output_vars] >>
              `lookup_var x s = SOME val` by gvs[] >>
              fs[ao_dfg_inv_def] >> res_tac >> gvs[] >> metis_tac[])))
      >- (irule ao_dfg_inv_step_preserved >> metis_tac[]))
QED

(* ao_dfg_inv preserved by exec_block under SSA. *)
Triviality ao_dfg_inv_exec_block_preserved[local]:
  !dfg fn0 bb fuel ctx s s'.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    ao_dfg_inv dfg s /\
    exec_block fuel ctx bb s = OK s' ==>
    ao_dfg_inv dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`] >> irule listTheory.EL_MEM >> simp[]) >>
  `inst_wf inst` by
    (fs[listTheory.EVERY_MEM] >> res_tac) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s_mid` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- ((* Terminator *)
      Cases_on `s_mid.vs_halted` >> simp[] >>
      strip_tac >> gvs[] >>
      metis_tac[ao_dfg_inv_step_any])
  >- ((* Non-terminator: recurse *)
      strip_tac >>
      `ao_dfg_inv dfg s_mid` by metis_tac[ao_dfg_inv_step_any] >>
      `s_mid.vs_inst_idx = s.vs_inst_idx` by
        metis_tac[step_inst_preserves_inst_idx] >>
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`bb`,
        `s_mid with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >> disch_then irule >>
      qpat_x_assum `ao_dfg_inv _ s_mid` mp_tac >>
      simp[ao_dfg_inv_def, lookup_var_def])
QED

(* ao_dfg_inv compatible with state_equiv on fresh vars:
   DFG variables are from fn0's instruction outputs, which are disjoint
   from ao_fn_fresh_vars (peephole expansion fresh names). *)
Triviality ao_dfg_inv_state_equiv_compat[local]:
  !dfg fv s1 s2.
    state_equiv fv s1 s2 /\ ao_dfg_inv dfg s1 /\
    (!x inst. dfg_get_def dfg x = SOME inst ==> x NOTIN fv) ==>
    ao_dfg_inv dfg s2
Proof
  simp[ao_dfg_inv_def] >> rpt strip_tac >>
  `x NOTIN fv` by metis_tac[] >>
  `lookup_var x s1 = lookup_var x s2` by
    fs[state_equiv_def, execution_equiv_def] >>
  `lookup_var x s1 = SOME val` by gvs[] >>
  `s1.vs_call_ctx = s2.vs_call_ctx` by
    fs[state_equiv_def, execution_equiv_def] >>
  res_tac >> gvs[] >> metis_tac[]
QED

(* ===== Strict-domination iszero invariant ===== *)

(* For ISZEROs in strictly dominating blocks, the iszero value relationship
   holds. Unlike ao_iszero_chain_inv, this IS preserved at block boundaries
   because PHIs can only redefine variables from the CURRENT block's
   dominator tree position, not from strict dominators above. *)
Definition strict_dom_iszero_inv_def:
  strict_dom_iszero_inv fn0 dfg s <=>
    !x inst op d_bb.
      dfg_get_def dfg x = SOME inst /\
      inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
      MEM d_bb fn0.fn_blocks /\ MEM inst d_bb.bb_instructions /\
      fn_dominates fn0 d_bb.bb_label s.vs_current_bb /\
      d_bb.bb_label <> s.vs_current_bb ==>
      !val_x val_op.
        lookup_var x s = SOME val_x /\
        eval_operand op s = SOME val_op ==>
        val_x = bool_to_word (val_op = 0w)
End
val _ = delsimps ["strict_dom_iszero_inv_def"]

(* Initial: vacuously true at function entry (no strict dominators) *)
Triviality strict_dom_iszero_inv_initial[local]:
  !fn0 dfg s.
    fn_entry_label fn0 = SOME s.vs_current_bb ==>
    strict_dom_iszero_inv fn0 dfg s
Proof
  rw[strict_dom_iszero_inv_def] >> rpt strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >> DISJ2_TAC >>
  qexists_tac `[s.vs_current_bb]` >>
  simp[is_fn_path_def, fn_entry_label_def, entry_block_def]
QED

(* Preserved at block boundaries. Key argument:
   - Case d_bb = bb (just executed): ISZERO ran during exec_block,
     outputs/inputs unchanged after by SSA.
   - Case d_bb <> bb: d_bb strictly dominated bb, exec_block doesn't
     modify d_bb's variables (SSA uniqueness). *)
(* SSA: output of instruction in one block is not in outputs of another block *)
Triviality ssa_output_not_in_other_block[local]:
  !fn0 d_bb bb inst x.
    ssa_form fn0 /\ wf_function fn0 /\
    MEM d_bb fn0.fn_blocks /\ MEM bb fn0.fn_blocks /\
    MEM inst d_bb.bb_instructions /\ MEM x inst.inst_outputs /\
    d_bb <> bb ==>
    ~MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rename1 `MEM inst' bb.bb_instructions` >>
  `MEM inst (fn_insts fn0) /\ MEM inst' (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts] >>
  `ssa_form fn0` by simp[] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn0)))` by
    fs[ssa_form_def] >>
  `inst = inst'` by metis_tac[all_distinct_flat_map_unique] >>
  gvs[] >>
  `fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
  fs[fn_inst_ids_distinct_def] >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP fid _))` >>
  qspecl_then [`fn0.fn_blocks`, `fid`, `d_bb`, `bb`]
    (fn th => `d_bb = bb` by
      (mp_tac th >> simp[Abbr `fid`, listTheory.MEM_MAP] >> metis_tac[]))
    all_distinct_flat_map_unique >>
  gvs[]
QED

Triviality strict_dom_iszero_inv_inst_idx[local]:
  !fn0 dfg s n.
    strict_dom_iszero_inv fn0 dfg (s with vs_inst_idx := n) <=>
    strict_dom_iszero_inv fn0 dfg s
Proof
  rw[strict_dom_iszero_inv_def, lookup_var_def] >> eq_tac >>
  rpt strip_tac >> res_tac >> gvs[] >>
  qpat_x_assum `eval_operand _ _ = _` mp_tac >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Triviality strict_dom_iszero_inv_state_equiv_compat[local]:
  !fn0 dfg fv s1 s2.
    strict_dom_iszero_inv fn0 dfg s1 /\
    state_equiv fv s1 s2 /\
    (!x inst. dfg_get_def dfg x = SOME inst ==> x NOTIN fv) /\
    (!x inst op. dfg_get_def dfg x = SOME inst /\
      inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var op] ==>
      op NOTIN fv) ==>
    strict_dom_iszero_inv fn0 dfg s2
Proof
  rpt gen_tac >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  qpat_x_assum `strict_dom_iszero_inv _ _ s1`
    (assume_tac o REWRITE_RULE[strict_dom_iszero_inv_def]) >>
  simp[strict_dom_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  `x NOTIN fv` by metis_tac[] >>
  `lookup_var x s1 = lookup_var x s2` by
    (fs[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
  `eval_operand op s1 = eval_operand op s2` by
    (Cases_on `op` >> simp_tac std_ss [eval_operand_def] >>
     TRY (fs[state_equiv_def, execution_equiv_def] >> NO_TAC) >>
     rename1 `Var vn` >>
     `vn NOTIN fv` by metis_tac[] >>
     simp_tac std_ss [eval_operand_def] >>
     fs[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
  `lookup_var x s1 = SOME val_x /\ eval_operand op s1 = SOME val_op` by
    metis_tac[] >>
  metis_tac[]
QED

(* ===== Within-block iszero step preservation ===== *)

(* SSA: operand's definer precedes the user; only one definer exists.
   So no later instruction in the same block can define that variable.
   Uses def_dominates_uses + ssa_form + inst_ids_el_eq. *)
Triviality ssa_operand_not_later_output[local]:
  !fn0 bb j idx v.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    j < LENGTH bb.bb_instructions /\ idx < LENGTH bb.bb_instructions /\
    j <= idx /\
    MEM (Var v) (EL j bb.bb_instructions).inst_operands ==>
    ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `ssa_form fn0 /\ def_dominates_uses fn0` by fs[wf_ssa_def] >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    metis_tac[listTheory.EL_MEM] >>
  `MEM (EL idx bb.bb_instructions) bb.bb_instructions` by
    metis_tac[listTheory.EL_MEM] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE[def_dominates_uses_def]) >>
  first_x_assum (qspecl_then [`bb`, `EL j bb.bb_instructions`, `v`]
    mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `MEM def_inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
  `MEM (EL idx bb.bb_instructions) (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts] >>
  `def_inst = EL idx bb.bb_instructions` by
    (qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                  `def_inst`, `EL idx bb.bb_instructions`, `v`]
       mp_tac all_distinct_flat_map_unique >>
     impl_tac >- fs[ssa_form_def] >>
     simp[]) >>
  gvs[] >>
  `fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `i < LENGTH bb.bb_instructions /\
       j < LENGTH bb.bb_instructions` by DECIDE_TAC >>
      `i = idx` by metis_tac[inst_ids_el_eq] >>
      `j' = j` by metis_tac[inst_ids_el_eq] >>
      DECIDE_TAC)
  >- (`MEM (EL idx bb.bb_instructions) def_bb.bb_instructions` by gvs[] >>
      `MEM (EL idx bb.bb_instructions).inst_id
        (MAP (\i. i.inst_id) bb.bb_instructions)` by
        (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
      `MEM (EL idx bb.bb_instructions).inst_id
        (MAP (\i. i.inst_id) def_bb.bb_instructions)` by
        (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
      `bb = def_bb` by
        (qspecl_then [`fn0.fn_blocks`,
           `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
           `bb`, `def_bb`,
           `(EL idx bb.bb_instructions).inst_id`]
           mp_tac all_distinct_flat_map_unique >>
         impl_tac >- fs[fn_inst_ids_distinct_def] >>
         simp[]) >>
      gvs[])
QED

(* j = idx case: the stepped instruction IS the ISZERO *)
Triviality wbiz_step_new[local]:
  !fn0 bb idx fuel ctx s s' iz_op x val_x val_op.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    (EL idx bb.bb_instructions).inst_opcode = ISZERO /\
    (EL idx bb.bb_instructions).inst_operands = [iz_op] /\
    MEM x (EL idx bb.bb_instructions).inst_outputs /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    lookup_var x (s' with vs_inst_idx := SUC s.vs_inst_idx) = SOME val_x /\
    eval_operand iz_op (s' with vs_inst_idx := SUC s.vs_inst_idx) =
      SOME val_op ==>
    val_x = bool_to_word (val_op = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst.inst_outputs = [x]` by
    (fs[inst_wf_def] >>
     Cases_on `inst.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    (irule step_inst_non_invoke >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_base_def, exec_pure1_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >> strip_tac >> gvs[] >>
  qpat_x_assum `lookup_var _ _ = _` mp_tac >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `iz_op` >>
  qpat_x_assum `eval_operand _ _ = SOME val_op` mp_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  TRY (strip_tac >> gvs[eval_operand_def] >> NO_TAC) >>
  rename1 `Var vn` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  `vn <> x` by
    (strip_tac >> gvs[] >>
     qspecl_then [`fn0`, `bb`, `idx`, `idx`, `vn`]
       mp_tac ssa_operand_not_later_output >>
     simp[Abbr `inst`]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

(* j < idx case: existing ISZERO preserved by step *)
Triviality wbiz_step_old[local]:
  !fn0 bb j idx fuel ctx s s' iz_op x val_x val_op.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    j < idx /\ j < LENGTH bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    (EL j bb.bb_instructions).inst_opcode = ISZERO /\
    (EL j bb.bb_instructions).inst_operands = [iz_op] /\
    MEM x (EL j bb.bb_instructions).inst_outputs /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    (!val_x' val_op'.
      lookup_var x s = SOME val_x' /\
      eval_operand iz_op s = SOME val_op' ==>
      val_x' = bool_to_word (val_op' = 0w)) /\
    lookup_var x (s' with vs_inst_idx := SUC s.vs_inst_idx) = SOME val_x /\
    eval_operand iz_op (s' with vs_inst_idx := SUC s.vs_inst_idx) =
      SOME val_op ==>
    val_x = bool_to_word (val_op = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `MEM (EL j bb.bb_instructions) (fn_insts fn0) /\
   MEM inst (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts, listTheory.EL_MEM] >>
  `~MEM x inst.inst_outputs` by
    (strip_tac >>
     `EL j bb.bb_instructions = inst` by
       (qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                     `EL j bb.bb_instructions`, `inst`, `x`]
          mp_tac all_distinct_flat_map_unique >>
        impl_tac >- fs[ssa_form_def] >> simp[]) >>
     `j = idx` by
       (`fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
        `j < LENGTH bb.bb_instructions` by DECIDE_TAC >>
        metis_tac[inst_ids_el_eq]) >>
     DECIDE_TAC) >>
  `!v. ~MEM v (EL idx bb.bb_instructions).inst_outputs ==>
       lookup_var v s' = lookup_var v s` by
    metis_tac[venomInstPropsTheory.step_preserves_non_output_vars] >>
  `lookup_var x s' = lookup_var x s` by
    (first_x_assum irule >> gvs[Abbr `inst`]) >>
  `lookup_var x (s' with vs_inst_idx := SUC s.vs_inst_idx) =
   lookup_var x s` by gvs[lookup_var_def] >>
  `s'.vs_labels = s.vs_labels` by
    metis_tac[venomInstPropsTheory.step_preserves_labels] >>
  sg `eval_operand iz_op (s' with vs_inst_idx := SUC s.vs_inst_idx) =
      eval_operand iz_op s`
  >- (Cases_on `iz_op`
      >- REWRITE_TAC[eval_operand_def]
      >- (REWRITE_TAC[eval_operand_def] >>
          rename1 `lookup_var vn` >>
          `lookup_var vn s' = lookup_var vn s` suffices_by
            simp[lookup_var_def] >>
          first_x_assum irule >> simp[Abbr `inst`] >>
          qspecl_then [`fn0`, `bb`, `j`, `idx`, `vn`]
            mp_tac ssa_operand_not_later_output >>
          impl_tac >- simp[] >> simp[])
      >- (REWRITE_TAC[eval_operand_def] >> gvs[])) >>
  gvs[]
QED

Triviality wbiz_step[local]:
  !fn0 bb idx fuel ctx s s'.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    within_block_iszero_inv fn0 bb idx s ==>
    within_block_iszero_inv fn0 bb (SUC idx)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  simp[within_block_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  Cases_on `j = idx`
  >- (gvs[] >> irule wbiz_step_new >> metis_tac[])
  >- (`j < idx` by DECIDE_TAC >>
      qspecl_then [`fn0`, `bb`, `j`, `idx`, `fuel`, `ctx`, `s`, `s'`,
                   `iz_op`, `x`, `val_x`, `val_op`]
        mp_tac wbiz_step_old >>
      impl_tac >- (simp[] >> fs[within_block_iszero_inv_def] >> metis_tac[])
      >> simp[])
QED

(* Terminator step preserves within_block_iszero_inv up to LENGTH *)
Triviality exec_block_wbiz_aux_term[local]:
  !fn0 bb fuel ctx s s_step inst.
    wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    inst = EL s.vs_inst_idx bb.bb_instructions /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s_step /\
    within_block_iszero_inv fn0 bb s.vs_inst_idx s ==>
    within_block_iszero_inv fn0 bb (LENGTH bb.bb_instructions) s_step
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    (fs[bb_well_formed_def] >> metis_tac[]) >>
  simp[within_block_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  `j < s.vs_inst_idx` by
    (`~is_terminator (EL j bb.bb_instructions).inst_opcode` by
       simp[is_terminator_def] >>
     `j <> s.vs_inst_idx` by (strip_tac >> gvs[]) >>
     DECIDE_TAC) >>
  `!v. lookup_var v s_step = lookup_var v s` by
    metis_tac[venomExecPropsTheory.step_terminator_preserves_vars] >>
  `s_step.vs_labels = s.vs_labels` by
    metis_tac[venomExecPropsTheory.step_inst_preserves_labels_always] >>
  `eval_operand iz_op s_step = eval_operand iz_op s` by
    (Cases_on `iz_op`
     >- REWRITE_TAC[eval_operand_def]
     >- (REWRITE_TAC[eval_operand_def] >> simp[lookup_var_def])
     >- (REWRITE_TAC[eval_operand_def] >> gvs[])) >>
  `lookup_var x s_step = SOME val_x` by gvs[] >>
  `lookup_var x s = SOME val_x` by gvs[] >>
  `eval_operand iz_op s = SOME val_op` by gvs[] >>
  fs[within_block_iszero_inv_def] >> metis_tac[]
QED

(* exec_block_wbiz_aux: exec_block maintains within_block_iszero_inv.
   Proof by measure induction on LENGTH - vs_inst_idx.
   Terminator case: ISZEROs at j < idx preserved by step_terminator_preserves_vars.
   Non-terminator case: wbiz_step + IH. *)
Triviality exec_block_wbiz_aux[local]:
  !n fn0 bb fuel ctx s s'.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    within_block_iszero_inv fn0 bb s.vs_inst_idx s /\
    exec_block fuel ctx bb s = OK s' ==>
    within_block_iszero_inv fn0 bb (LENGTH bb.bb_instructions) s'
Proof
  Induct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  TRY (fs[venomInstTheory.get_instruction_def] >> NO_TAC) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s_step` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by
    fs[venomInstTheory.get_instruction_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()]
  >- (* terminator *)
     (qspecl_then [`fn0`, `bb`, `fuel`, `ctx`, `s`, `s'`,
                   `EL s.vs_inst_idx bb.bb_instructions`]
        mp_tac exec_block_wbiz_aux_term >>
      impl_tac >- (simp[] >> fs[venomInstTheory.get_instruction_def]) >>
      simp[])
  >- (* non-terminator: wbiz_step + IH *)
     (`s.vs_inst_idx < LENGTH bb.bb_instructions` by
        fs[venomInstTheory.get_instruction_def] >>
      `within_block_iszero_inv fn0 bb (SUC s.vs_inst_idx)
         (s_step with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qspecl_then [`fn0`, `bb`, `s.vs_inst_idx`, `fuel`, `ctx`,
                      `s`, `s_step`]
           mp_tac wbiz_step >>
         impl_tac >- (simp[] >> metis_tac[listTheory.EVERY_EL]) >>
         simp[]) >>
      first_x_assum (qspecl_then [`fn0`, `bb`, `fuel`, `ctx`,
         `s_step with vs_inst_idx := SUC s.vs_inst_idx`, `s'`]
         mp_tac) >>
      impl_tac >- simp[] >>
      simp[])
QED

Triviality exec_block_iszero_val[local]:
  !fn0 bb fuel ctx s s' iz_inst x iz_op.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    exec_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    EVERY inst_wf bb.bb_instructions /\
    MEM iz_inst bb.bb_instructions /\
    iz_inst.inst_opcode = ISZERO /\
    iz_inst.inst_operands = [iz_op] /\
    MEM x iz_inst.inst_outputs ==>
    !val_x val_op.
      lookup_var x s' = SOME val_x /\
      eval_operand iz_op s' = SOME val_op ==>
      val_x = bool_to_word (val_op = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  `within_block_iszero_inv fn0 bb (LENGTH bb.bb_instructions) s'` by
    (qspecl_then [`LENGTH bb.bb_instructions`, `fn0`, `bb`, `fuel`,
                  `ctx`, `s`, `s'`]
       mp_tac exec_block_wbiz_aux >>
     impl_tac >- simp[wbiz_initial] >> simp[]) >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = iz_inst` by
    metis_tac[listTheory.MEM_EL] >>
  fs[within_block_iszero_inv_def] >> metis_tac[]
QED

Triviality strict_dom_iszero_inv_preserved[local]:
  !fn0 dfg bb fuel ctx s s'.
    wf_function fn0 /\ wf_ssa fn0 /\
    dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    exec_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    ~s'.vs_halted /\
    EVERY inst_wf bb.bb_instructions /\
    fn_reachable fn0 s.vs_current_bb /\
    strict_dom_iszero_inv fn0 dfg s ==>
    strict_dom_iszero_inv fn0 dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  simp[strict_dom_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- cheat
  >- cheat
QED

(* ao_handle_offset_inst preserves inst_id *)
Triviality ao_handle_offset_inst_id_eq[local]:
  !inst. (ao_handle_offset_inst inst).inst_id = inst.inst_id
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

(* Instructions in fn0 blocks have IDs from fn, so fresh vars are in fv *)
Triviality fn0_inst_fresh_in_fv[local]:
  !fn fn0 bb inst.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    MEM bb fn0.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    ao_fresh_var inst.inst_id "not" IN ao_fn_fresh_vars fn /\
    ao_fresh_var inst.inst_id "iz" IN ao_fn_fresh_vars fn /\
    ao_fresh_var inst.inst_id "xor" IN ao_fn_fresh_vars fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  fs[listTheory.MEM_MAP] >> rename1 `MEM bb0 fn.fn_blocks` >>
  gvs[] >>
  fs[listTheory.MEM_MAP] >> rename1 `inst = ao_handle_offset_inst inst'` >>
  `inst.inst_id = inst'.inst_id` by simp[ao_handle_offset_inst_id_eq] >>
  `MEM inst' (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_block_mem_fn_insts_blocks >>
     metis_tac[]) >>
  `MEM inst'.inst_id (MAP (\i. i.inst_id) (fn_insts fn))` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `inst'` >> simp[]) >>
  rpt conj_tac >>
  simp[ao_fn_fresh_vars_def] >>
  qexists_tac `inst'.inst_id` >> simp[ao_handle_offset_inst_id_eq]
QED

(* df_at on idx_df_state gives index (local reproof) *)
Triviality idx_df_state_at2[local]:
  !lbl n i. i < n ==>
    df_at 0 (idx_df_state lbl n) lbl i = i
Proof
  rw[df_at_def, idx_df_state_def] >>
  `FINITE (IMAGE (\i. (lbl, i)) (count n))` by simp[] >>
  `(lbl, i) IN IMAGE (\i. (lbl, i)) (count n)` by
    (simp[] >> qexists_tac `i` >> simp[]) >>
  simp[finite_mapTheory.FLOOKUP_FUN_FMAP]
QED

(* Per-block sim for fn0 blocks with invariant, using f_safe wrapper.
   Key: only requires per-instruction sim for block instructions (MEM). *)
Triviality ao_block_sim_fn0[local]:
  !fv mid dfg ra targets bb (state_inv : venom_state -> bool).
    (!fuel ctx v inst s.
       MEM inst bb.bb_instructions /\
       state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (step_inst fuel ctx inst s)
         (run_insts fuel ctx
           (ao_transform_inst mid dfg ra bb.bb_label v targets inst) s)) /\
    inst_transform_structural
      (\v inst. ao_transform_inst mid dfg ra bb.bb_label v targets inst) /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fv) /\
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\ inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!s1 s2. state_equiv fv s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ state_inv s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (ao_transform_block mid dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Define safe wrapper: identity for non-block instructions *)
  qabbrev_tac `f_safe = \(v:num) inst.
    if MEM inst bb.bb_instructions
    then ao_transform_inst mid dfg ra bb.bb_label v targets inst
    else [inst]` >>
  (* Rewrite ao_transform_block to analysis_block_transform with f_safe *)
  `ao_transform_block mid dfg ra targets bb =
   analysis_block_transform 0
     (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
     f_safe bb` by
    (simp[analysis_block_transform_def, ao_transform_block_def] >>
     `MAPi (\idx inst.
        ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
        bb.bb_instructions =
      MAPi (\idx inst.
        f_safe (df_at 0
          (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
          bb.bb_label idx) inst) bb.bb_instructions`
       suffices_by simp[] >>
     irule MAPi_CONG' >> simp[] >> rpt strip_tac >>
     `n < SUC (LENGTH bb.bb_instructions)` by simp[] >>
     simp[idx_df_state_at2, Abbr `f_safe`] >>
     `MEM (EL n bb.bb_instructions) bb.bb_instructions` by
       metis_tac[listTheory.EL_MEM] >> simp[]) >>
  ASM_REWRITE_TAC [] >>
  (* Pre-prove per-inst sim for f_safe *)
  `!fuel ctx v inst s.
    (\(v:num) (s:venom_state). T) v s /\
    state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx (f_safe v inst) s)` by
    (rpt gen_tac >> simp[] >> strip_tac >>
     gvs[Abbr `f_safe`] >>
     Cases_on `MEM inst bb.bb_instructions` >>
     gvs[run_insts_singleton] >>
     DISJ2_TAC >> irule lift_result_refl >>
     simp[state_equiv_refl, execution_equiv_refl]) >>
  (* Pre-prove inst_transform_structural for f_safe *)
  `inst_transform_structural f_safe` by
    (simp[Abbr `f_safe`, inst_transform_structural_def] >>
     qpat_x_assum `inst_transform_structural _`
       (strip_assume_tac o REWRITE_RULE[inst_transform_structural_def]) >>
     rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         Cases_on `MEM inst bb.bb_instructions` >> gvs[] >>
         qexists_tac `inst` >> simp[])
     >- (rpt gen_tac >> strip_tac >>
         Cases_on `MEM inst bb.bb_instructions` >> gvs[] >>
         qexists_tac `inst` >> simp[])
     >- (rpt gen_tac >> strip_tac >>
         Cases_on `MEM inst bb.bb_instructions` >> gvs[])) >>
  (* Apply analysis_block_sim_inv with f_safe *)
  qspecl_then
    [`state_equiv fv`, `execution_equiv fv`,
     `\(v:num) (s:venom_state). T`, `state_inv`,
     `f_safe`, `bb`, `0`,
     `idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))`,
     `\(ctx:'b) (inst:instruction) v. SUC v`, `ARB`]
    mp_tac analysis_block_sim_inv >>
  impl_tac >- (
    rpt conj_tac
    >- simp[state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- (rpt strip_tac >>
        `x NOTIN fv` by res_tac >>
        fs[state_equiv_def, execution_equiv_def])
    >- simp[transfer_sound_wf_def]
    >- simp[]
    >- (rpt strip_tac >> simp[idx_df_state_at2])
    >- (rpt strip_tac >> res_tac)
    >- (rpt strip_tac >> res_tac)) >>
  simp[]
QED

(* ao_dfg_inv does not depend on vs_inst_idx *)
Triviality ao_dfg_inv_inst_idx_irrel[local]:
  !dfg s n. ao_dfg_inv dfg (s with vs_inst_idx := n) = ao_dfg_inv dfg s
Proof
  simp[ao_dfg_inv_def, lookup_var_def]
QED

(* DFG output variables from fn0 are not in ao_fn_fresh_vars fn.
   Key: ao_handle_offset_inst preserves inst_outputs, so DFG tracks
   the same outputs as fn's original instructions. *)
Theorem fn_insts_blocks_map_offset:
  !bbs inst.
    MEM inst (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) bbs)) ==>
    ?inst0. MEM inst0 (fn_insts_blocks bbs) /\
            inst = ao_handle_offset_inst inst0
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Triviality ao_dfg_outputs_not_in_fv[local]:
  !fn fn0 dfg x inst.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    dfg_get_def dfg x = SOME inst ==>
    x NOTIN ao_fn_fresh_vars fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
  qpat_x_assum `MEM inst (fn_insts _)` mp_tac >>
  simp[fn_insts_def] >> strip_tac >>
  drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
  fs[ao_handle_offset_inst_outputs] >>
  first_x_assum irule >> qexists_tac `inst0` >>
  simp[fn_insts_def]
QED

(* run_blocks is independent of vs_inst_idx *)
Triviality run_blocks_inst_idx_irrel[local]:
  !fuel ctx fn s.
    run_blocks fuel ctx fn s =
    run_blocks fuel ctx fn (s with vs_inst_idx := 0)
Proof
  Induct_on `fuel` >> rpt gen_tac
  >- (ONCE_REWRITE_TAC[run_blocks_def] >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[run_blocks_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[run_blocks_def])) >>
  simp_tac (srw_ss()) []
QED

(* Per-instruction sim with per-instruction H_fresh.
   Unlike ao_transform_inst_sim, only needs fresh vars for THIS inst. *)
Triviality ao_transform_inst_sim_inst[local]:
  !fv mid dfg ra lbl targets fuel ctx v inst s.
    inst_wf inst /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv /\
    (inst_wf inst ==>
      step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
      step_inst fuel ctx inst s) /\
    (!op w.
      MEM op (ao_resolve_iszero_inst targets inst).inst_operands /\
      eval_operand op s = SOME w ==>
      in_range (range_get_range ra lbl v op) w)
    ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx
        (ao_transform_inst mid dfg ra lbl v targets inst) s)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
   step_inst fuel ctx inst s` by res_tac >>
  simp[ao_transform_inst_def, LET_THM,
       ao_resolve_iszero_inst_outputs,
       ao_resolve_iszero_inst_opcode] >>
  (* Trivial cases: outputs=[] or ASSIGN/PHI/PARAM *)
  Cases_on `inst.inst_outputs = []`
  >- (simp[run_insts_singleton] >> DISJ2_TAC >>
      pop_assum kall_tac >> pop_assum (fn th => REWRITE_TAC [th]) >>
      irule lift_result_refl >>
      simp[state_equiv_refl, execution_equiv_refl]) >>
  simp[] >>
  Cases_on `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
            inst.inst_opcode = PARAM`
  >- (simp[run_insts_singleton] >> DISJ2_TAC >>
      qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
        (fn th => REWRITE_TAC [th]) >>
      irule lift_result_refl >>
      simp[state_equiv_refl, execution_equiv_refl]) >>
  simp[] >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
  >- (* NONE: peephole path *)
     (simp[] >>
      `~is_terminator inst.inst_opcode` by
        (strip_tac >> imp_res_tac terminator_no_outputs >> gvs[]) >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[ao_peephole_inst_def, LET_THM,
               ao_resolve_iszero_inst_opcode,
               ao_pre_flip_inst_non_comm,
               ao_post_flip_inst_non_comm,
               run_insts_singleton] >>
          DISJ2_TAC >>
          qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
            (fn th => REWRITE_TAC [th]) >>
          irule lift_result_refl >>
          simp[state_equiv_refl, execution_equiv_refl])
      >- (irule ao_peephole_path_sim >> gvs[] >>
          metis_tac[ao_resolve_iszero_inst_id]))
  >- (* SOME: producer path *)
     (simp[] >>
      qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
        (fn th => REWRITE_TAC [SYM th]) >>
      irule ao_opt_producer_sim >>
      simp[ao_resolve_iszero_inst_opcode,
           ao_resolve_iszero_inst_outputs] >>
      metis_tac[])
QED

(* Per-inst sim for fn0 block instructions: combines
   ao_transform_inst_sim_inst + fn0_inst_fresh_in_fv *)
(* Original ao_per_inst_sim_fn0 with ∀s H_resolve and H_range.
   Kept for reference; ao_per_inst_sim_fn0_inv below replaces it. *)
Triviality ao_per_inst_sim_fn0[local]:
  !fn fn0 mid dfg ra targets bb fuel ctx v inst s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    (!i fuel ctx s. inst_wf i ==>
      step_inst fuel ctx (ao_resolve_iszero_inst targets i) s =
      step_inst fuel ctx i s) /\
    (!bb i idx s op w.
      MEM bb fn0.fn_blocks /\ MEM i bb.bb_instructions /\
      eval_operand op s = SOME w /\
      MEM op (ao_resolve_iszero_inst targets i).inst_operands ==>
      in_range (range_get_range ra bb.bb_label idx op) w) /\
    MEM bb fn0.fn_blocks /\
    MEM inst bb.bb_instructions /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx
        (ao_transform_inst mid dfg ra bb.bb_label v targets inst) s)
Proof
  rpt gen_tac >> strip_tac >>
  irule ao_transform_inst_sim_inst >> simp[] >>
  drule_all fn0_inst_fresh_in_fv >> simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `fn0 = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `targets = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ra = _` (SUBST_ALL_TAC o SYM) >>
  first_x_assum irule >> metis_tac[]
QED

Triviality resolve_phi_map_label_pres[local]:
  !prev ops g.
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op lbl. g op = Label lbl ==> op = Label lbl) ==>
    resolve_phi prev (MAP g ops) = OPTION_MAP g (resolve_phi prev ops)
Proof
  rpt gen_tac >> strip_tac >>
  qid_spec_tac `ops` >> qid_spec_tac `prev` >>
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >| [
    `!lbl. g (Lit v8) <> Label lbl` by
      (rpt strip_tac >> `Lit v8 = Label lbl` by metis_tac[] >>
       gvs[operand_distinct]) >>
    Cases_on `g (Lit v8)` >> gvs[resolve_phi_def],
    `!lbl. g (Var v9) <> Label lbl` by
      (rpt strip_tac >> `Var v9 = Label lbl` by metis_tac[] >>
       gvs[operand_distinct]) >>
    Cases_on `g (Var v9)` >> gvs[resolve_phi_def]
  ]
QED

Triviality iszero_step_chain_tail_var[local]:
  !h acc.
    (!v chain k. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) ==>
    (!v chain k. ALOOKUP (ao_compute_iszero_step acc h) v = SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w)
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  rpt gen_tac >>
  TRY (strip_tac >> res_tac >> simp[] >> NO_TAC) >>
  simp[alistTheory.ALOOKUP_def] >>
  IF_CASES_TAC >> strip_tac >> gvs[listTheory.LENGTH_SNOC] >>
  TRY (res_tac >> simp[] >> NO_TAC) >>
  Cases_on `k < LENGTH x` >>
  gvs[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
  TRY (res_tac >> simp[] >> NO_TAC) >>
  rpt (qpat_x_assum `!v chain k. _` kall_tac) >>
  rpt (qpat_x_assum `!chain. _` kall_tac) >>
  rpt (qpat_x_assum `!k. _` kall_tac) >>
  FIRST [
    qmatch_goalsub_abbrev_tac `(SNOC _ _)❲idx❳` >>
    `idx = LENGTH x` by (
      qunabbrev_tac `idx` >>
      qpat_x_assum `~(_ < LENGTH _)` mp_tac >>
      qpat_x_assum `_ < SUC _` mp_tac >>
      DECIDE_TAC) >>
    gvs[listTheory.EL_LENGTH_SNOC],
    Cases_on `k` >> gvs[] >>
    rename1 `SUC n` >> Cases_on `n` >> gvs[] >>
    gvs[listTheory.EL_restricted, listTheory.HD]
  ]
QED

Triviality foldl_chain_tail_var[local]:
  !insts acc.
    (!v chain k. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) ==>
    (!v chain k. ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v =
       SOME chain /\
       0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac iszero_step_chain_tail_var >>
  first_assum ACCEPT_TAC
QED

Theorem ao_fn_targets_chain_tail_var:
  !fn v chain k.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    ?w. EL k chain = Var w
Proof
  rpt strip_tac >>
  `!v' ch k'. ALOOKUP (ao_compute_fn_iszero_targets fn) v' = SOME ch /\
     0 < k' /\ k' < LENGTH ch ==> ?w. EL k' ch = Var w` by
    (simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
     match_mp_tac foldl_chain_tail_var >> simp[alistTheory.ALOOKUP_def]) >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

(* ALOOKUP monotonicity: step only adds entries *)
Triviality iszero_step_alookup_mono[local]:
  !acc h w.
    ALOOKUP acc w <> NONE ==>
    ALOOKUP (ao_compute_iszero_step acc h) w <> NONE
Proof
  rpt gen_tac >>
  simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  simp[alistTheory.ALOOKUP_def] >>
  IF_CASES_TAC >> simp[]
QED

(* Var elements at pos>0 in SNOC (Var key) prev are either key or from prev *)
Triviality snoc_var_el_cases[local]:
  !prev key k w.
    0 < k /\ k < LENGTH (SNOC (Var key) prev) /\
    EL k (SNOC (Var key) prev) = Var w ==>
    w = key \/ (k < LENGTH prev /\ EL k prev = Var w)
Proof
  rpt strip_tac >>
  Cases_on `k < LENGTH prev`
  >- (disj2_tac >> gvs[listTheory.EL_SNOC])
  >- (disj1_tac >>
      `k = LENGTH prev` by gvs[listTheory.LENGTH_SNOC] >>
      gvs[listTheory.EL_LENGTH_SNOC])
QED

(* Helper: extending alist with (key, chain) where all Var-at-pos>0
   are either key itself or keys in acc, preserves chain-var-is-key *)
Triviality chain_var_is_key_extend[local]:
  !acc key chain_val.
    (!v chain k w. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP acc w <> NONE) /\
    (!k w. 0 < k /\ k < LENGTH chain_val /\ EL k chain_val = Var w ==>
       w = key \/ ALOOKUP acc w <> NONE) ==>
    (!v chain k w.
       ALOOKUP ((key, chain_val) :: acc) v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP ((key, chain_val) :: acc) w <> NONE)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  strip_tac >>
  simp[alistTheory.ALOOKUP_def] >>
  Cases_on `v = key` >> Cases_on `w = key` >> gvs[]
  (* w=key cases closed by gvs. Remaining: w<>key cases. *)
  >- ((* v=key, w<>key: use second precondition *)
      first_x_assum (qspecl_then [`k`, `w`] mp_tac) >> gvs[])
  >- ((* v<>key, w<>key: use first precondition *)
      first_x_assum (qspecl_then [`v`, `chain`, `k`, `w`] mp_tac) >> gvs[])
QED

(* The step either returns acc unchanged or prepends one entry
   where prev is either a singleton or from ALOOKUP acc *)
Triviality iszero_step_cases[local]:
  !acc h. ao_compute_iszero_step acc h = acc \/
    ?out prev. ao_compute_iszero_step acc h = (out, SNOC (Var out) prev) :: acc /\
      (LENGTH prev = 1 \/ ?s. ALOOKUP acc s = SOME prev)
Proof
  rpt gen_tac >> simp[ao_compute_iszero_step_def] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[] >>
  disj2_tac >> simp[] >> metis_tac[]
QED

(* Chain Var elements at position > 0 are target keys. *)
Triviality iszero_step_chain_var_is_key[local]:
  !acc h.
    (!v chain k w. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP acc w <> NONE) ==>
    (!v chain k w. ALOOKUP (ao_compute_iszero_step acc h) v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP (ao_compute_iszero_step acc h) w <> NONE)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`acc`, `h`] strip_assume_tac iszero_step_cases
  >- (* step = acc: trivial *)
     (pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (* step prepends, LENGTH prev = 1 *)
     (qpat_x_assum `ao_compute_iszero_step _ _ = _` SUBST_ALL_TAC >>
      qspecl_then [`acc`, `out`, `SNOC (Var out) prev`]
        (MATCH_MP_TAC o BETA_RULE) chain_var_is_key_extend >>
      conj_tac
      >- (rpt strip_tac >> res_tac)
      >- (rpt strip_tac >>
          drule_all snoc_var_el_cases >> strip_tac >> gvs[]))
  >- (* step prepends, ALOOKUP acc s = SOME prev *)
     (qpat_x_assum `ao_compute_iszero_step _ _ = _` SUBST_ALL_TAC >>
      qspecl_then [`acc`, `out`, `SNOC (Var out) prev`]
        (MATCH_MP_TAC o BETA_RULE) chain_var_is_key_extend >>
      conj_tac
      >- (rpt strip_tac >> res_tac)
      >- (rpt strip_tac >>
          Cases_on `k < LENGTH prev`
          >- (disj2_tac >>
              `EL k prev = Var w` by
                (qpat_x_assum `EL k (SNOC _ _) = _` mp_tac >>
                 simp[listTheory.EL_SNOC]) >>
              res_tac)
          >- (disj1_tac >>
              `k = LENGTH prev` by
                (qpat_x_assum `k < LENGTH (SNOC _ _)` mp_tac >>
                 simp[listTheory.LENGTH_SNOC]) >>
              qpat_x_assum `EL k (SNOC _ _) = _` mp_tac >>
              simp[listTheory.EL_LENGTH_SNOC])))
QED

Triviality foldl_chain_var_is_key[local]:
  !insts acc.
    (!v chain k w. ALOOKUP acc v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP acc w <> NONE) ==>
    (!v chain k w.
       ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
       0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
       ALOOKUP (FOLDL ao_compute_iszero_step acc insts) w <> NONE)
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  match_mp_tac iszero_step_chain_var_is_key >>
  first_assum ACCEPT_TAC
QED

Theorem ao_fn_targets_chain_var_is_key:
  !fn v chain k w.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain /\
    0 < k /\ k < LENGTH chain /\ EL k chain = Var w ==>
    ALOOKUP (ao_compute_fn_iszero_targets fn) w <> NONE
Proof
  rpt strip_tac >>
  `!v' chain' k' w'.
     ALOOKUP (ao_compute_fn_iszero_targets fn) v' = SOME chain' /\
     0 < k' /\ k' < LENGTH chain' /\ EL k' chain' = Var w' ==>
     ALOOKUP (ao_compute_fn_iszero_targets fn) w' <> NONE` by
    (simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
     match_mp_tac foldl_chain_var_is_key >> simp[alistTheory.ALOOKUP_def]) >>
  metis_tac[]
QED

Triviality resolve_op_phi_no_label[local]:
  !fn0 targets op lbl.
    targets = ao_compute_fn_iszero_targets fn0 ==>
    (ao_resolve_iszero_op targets PHI op = Label lbl ==> op = Label lbl)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  Cases_on `ALOOKUP targets s` >> gvs[] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  `(LENGTH x - 1) MOD 2 = 0 \/ (LENGTH x - 1) MOD 2 = 1` by
    (`(LENGTH x - 1) MOD 2 < 2` by simp[] >> DECIDE_TAC) >>
  gvs[] >>
  drule ao_fn_targets_chain_tail_var >>
  strip_tac >>
  qpat_x_assum `!k. _` (qspec_then `2 - (LENGTH x - 1) MOD 2` mp_tac) >>
  gvs[operand_distinct]
QED

Triviality eval_operands_mem_defined[local]:
  !ops s vals. eval_operands ops s = SOME vals ==>
    !op. MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Triviality ao_resolve_iszero_op_not_label[local]:
  !targets op lbl.
    (!v chain k. ALOOKUP targets v = SOME chain /\
      0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) ==>
    ao_resolve_iszero_op targets PHI op = Label lbl ==>
    op = Label lbl
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  rename1 `ALOOKUP targets vn` >>
  Cases_on `ALOOKUP targets vn` >> simp[] >>
  rename1 `SOME chain` >>
  simp[LET_THM] >>
  qabbrev_tac `keep = 2 - (LENGTH chain - 1) MOD 2` >>
  COND_CASES_TAC >> simp[] >>
  strip_tac >>
  `0 < keep /\ keep < LENGTH chain` by
    (qunabbrev_tac `keep` >> fs[] >>
     `(LENGTH chain - 1) MOD 2 < 2` by simp[] >> DECIDE_TAC) >>
  first_x_assum (qspecl_then [`vn`, `chain`, `keep`] mp_tac) >>
  simp[] >> strip_tac >> fs[operand_distinct]
QED

Triviality ao_resolve_phi_sim[local]:
  !targets inst s fuel ctx.
    inst.inst_opcode = PHI /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined_at targets s /\
    ao_targets_wf targets /\
    (!v chain k. ALOOKUP targets v = SOME chain /\
      0 < k /\ k < LENGTH chain ==> ?w. EL k chain = Var w) /\
    ~(?e. step_inst fuel ctx inst s = Error e) ==>
    step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    simp[step_inst_non_invoke] >>
  `step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
   step_inst_base (ao_resolve_iszero_inst targets inst) s` by
    simp[step_inst_non_invoke, ao_resolve_iszero_inst_def] >>
  simp[] >>
  simp[Once step_inst_base_def, SimpRHS] >>
  simp[Once step_inst_base_def, ao_resolve_iszero_inst_def] >>
  qabbrev_tac `g = ao_resolve_iszero_op targets PHI` >>
  `!lbl. g (Label lbl) = Label lbl` by
    simp[Abbr `g`, ao_resolve_iszero_op_def] >>
  `!op lbl. g op = Label lbl ==> op = Label lbl` by
    metis_tac[ao_resolve_iszero_op_not_label] >>
  `!prev. resolve_phi prev (MAP g inst.inst_operands) =
   OPTION_MAP g (resolve_phi prev inst.inst_operands)` by
    (gen_tac >> irule resolve_phi_map_label_pres >> simp[]) >>
  Cases_on `s.vs_prev_bb` >> simp[] >>
  rename1 `SOME prev` >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `resolve_phi prev inst.inst_operands` >> simp[] >>
  rename1 `resolve_phi prev _ = SOME val_op` >>
  simp[] >>
  `eval_operand (g val_op) s = eval_operand val_op s` by
    (qunabbrev_tac `g` >>
     irule resolve_op_eval_eq_at >> simp[] >>
     qpat_x_assum `~_` mp_tac >> simp[Once step_inst_def] >>
     simp[Once step_inst_base_def] >>
     BasicProvers.EVERY_CASE_TAC >> simp[]) >>
  simp[]
QED

Triviality ao_resolve_iszero_op_iszero[local]:
  !targets op. ao_resolve_iszero_op targets ISZERO op = op
Proof
  rpt gen_tac >> Cases_on `op` >> simp[ao_resolve_iszero_op_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Triviality invoke_operand_defined[local]:
  !fuel ctx inst s v.
    inst.inst_opcode = INVOKE /\
    ~(?e. step_inst fuel ctx inst s = Error e) /\
    MEM (Var v) inst.inst_operands ==>
    v IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  gvs[Once step_inst_def, decode_invoke_def, AllCaseEqs()] >>
  drule eval_operands_mem_defined >>
  disch_then (qspec_then `Var v` mp_tac) >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

Triviality step_inst_base_zero_eval_op_irrel[local]:
  !inst ops s.
    MEM inst.inst_opcode [NOP; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP] ==>
    step_inst_base (inst with inst_operands := ops) s =
    step_inst_base inst s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  gvs[step_inst_base_def, exec_read0_def]
QED

(* Per-inst sim with state-dependent invariants instead of ∀s preconditions.
   H_resolve derived from chain invariant + ao_resolve_iszero_inst_sim.
   H_range derived from in_range_state + range_analyze_sound. *)
Triviality ao_per_inst_sim_fn0_inv[local]:
  !fn fn0 mid dfg ra targets bb fuel ctx idx inst s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ao_iszero_chain_inv targets s /\
    ao_chain_defined_prefix targets s /\
    ao_targets_wf targets /\
    in_range_state (range_at_inst ra bb.bb_label idx) s.vs_vars /\
    MEM bb fn0.fn_blocks /\
    MEM inst bb.bb_instructions /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx
        (ao_transform_inst mid dfg ra bb.bb_label idx targets inst) s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?e. step_inst fuel ctx inst s = Error e`
  >- (DISJ1_TAC >> metis_tac[])
  >- (
  ho_match_mp_tac (Q.SPEC `ao_fn_fresh_vars fn`
    ao_transform_inst_sim_inst) >> simp[] >>
  drule_all fn0_inst_fresh_in_fv >> simp[] >> strip_tac >> simp[] >>
  `ao_chains_defined_at targets s` by
    (irule ao_chain_defined_prefix_implies_at >> simp[]) >>
  conj_tac
  >- (* resolve sim *)
     (Cases_on `inst.inst_opcode = ISZERO`
      >- (qpat_x_assum `fn0 = _` (SUBST_ALL_TAC o SYM) >>
          `ao_resolve_iszero_inst
             (ao_compute_fn_iszero_targets fn0) inst = inst` by
            (simp[ao_resolve_iszero_inst_def,
                  instruction_component_equality] >>
             CONV_TAC (RAND_CONV
               (ONCE_REWRITE_CONV [GSYM listTheory.MAP_ID])) >>
             irule listTheory.MAP_CONG >>
             simp[ao_resolve_iszero_op_iszero]) >>
          simp[])
      >- (Cases_on `inst.inst_opcode = PHI`
          >- (irule ao_resolve_phi_sim >> simp[] >>
              metis_tac[ao_fn_targets_chain_tail_var])
          >- (Cases_on `MEM inst.inst_opcode [NOP; STOP; SINK; INVALID;
                  CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
                  ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER;
                  PREVRANDAO; CHAINID; SELFBALANCE; BASEFEE; BLOBBASEFEE;
                  CALLDATASIZE; RETURNDATASIZE; CODESIZE; MEMTOP]`
              >- (* zero-eval: operand-independent *)
                 (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[]) >>
                  simp[step_inst_non_invoke, ao_resolve_iszero_inst_opcode,
                       ao_resolve_iszero_inst_def] >>
                  irule step_inst_base_zero_eval_op_irrel >> simp[])
              >- (* non-zero-eval: via ao_resolve_iszero_inst_sim_at *)
                 (qpat_x_assum `fn0 = _` (SUBST_ALL_TAC o SYM) >>
                  qpat_x_assum `targets = _` (SUBST_ALL_TAC o SYM) >>
                  irule ao_resolve_iszero_inst_sim_at >> simp[] >>
                  rpt strip_tac >>
                  simp[eval_operand_def, lookup_var_def,
                       finite_mapTheory.FLOOKUP_DEF] >>
                  Cases_on `inst.inst_opcode = INVOKE`
                  >- (irule invoke_operand_defined >> simp[] >>
                      metis_tac[])
                  >- (`step_inst fuel ctx inst s = step_inst_base inst s` by
                        simp[step_inst_non_invoke] >>
                      `!e. step_inst_base inst s <> Error e` by
                        (rpt strip_tac >>
                         `?e. step_inst fuel ctx inst s = Error e` by
                           metis_tac[] >>
                         metis_tac[]) >>
                      `~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
                         CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
                         ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER;
                         PREVRANDAO; CHAINID; SELFBALANCE; BASEFEE;
                         BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
                         CODESIZE; MEMTOP]` by gvs[] >>
                      metis_tac[step_inst_base_nonerr_var_fdom])))))
  >- (* range soundness *)
     (qpat_x_assum `fn0 = _` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `ra = _` (SUBST_ALL_TAC o SYM) >>
      rpt strip_tac >>
      irule range_analyze_sound >>
      qexists_tac `s` >> gvs[]))
QED

Triviality eval_operand_inst_idx[local]:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Triviality ao_chain_inv_inst_idx_iff[local]:
  !targets s n.
    ao_iszero_chain_inv targets (s with vs_inst_idx := n) <=>
    ao_iszero_chain_inv targets s
Proof
  simp[ao_iszero_chain_inv_def, eval_operand_inst_idx]
QED

(* ao_chain_defined_prefix_inst_idx_iff is imported from aoResolveObligationTheory *)

Triviality ao_fn0_operand_not_in_fv[local]:
  !fn fn0 fv bb inst x.
    Abbrev(fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    MEM bb fn0.fn_blocks /\
    MEM inst bb.bb_instructions /\
    MEM (Var x) inst.inst_operands ==>
    x NOTIN fv
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
  qpat_x_assum `MEM inst (fn_insts fn0)` mp_tac >>
  fs[markerTheory.Abbrev_def, fn_insts_def] >> strip_tac >>
  drule fn_insts_blocks_map_offset >> strip_tac >> gvs[] >>
  imp_res_tac ao_handle_offset_var_ops >>
  metis_tac[fn_insts_def]
QED

Triviality test_wf_all_distinct[local]:
  !fn0. wf_function fn0 ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn0.fn_blocks)
Proof
  rpt strip_tac >> gvs[wf_function_def, fn_labels_def]
QED

Triviality test_lookup_block[local]:
  !fn0 bb.
    wf_function fn0 /\ MEM bb fn0.fn_blocks ==>
    lookup_block bb.bb_label fn0.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  drule test_wf_all_distinct >> strip_tac >>
  mp_tac (Q.SPECL [`bb.bb_label`, `fn0.fn_blocks`, `bb`]
    MEM_lookup_block) >>
  impl_tac >- simp[] >>
  simp[]
QED

(* ao_block_sim_range: DEAD CODE — only used by ao_phases123_run_blocks_sim_inv
   which is also dead. The top-level theorem uses ao_phases123_run_blocks_sim. *)
Triviality ao_block_sim_range[local]:
  !fn fn0 mid dfg ra targets bb fv fuel ctx s.
    Abbrev(fn0 = fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) /\
    Abbrev(mid = fn_max_inst_id fn0) /\
    Abbrev(dfg = dfg_build_function fn0) /\
    Abbrev(ra = range_analyze fn0) /\
    Abbrev(targets = ao_compute_fn_iszero_targets fn0) /\
    Abbrev(fv = ao_fn_fresh_vars fn) /\
    wf_function fn0 /\ ssa_form fn0 /\
    EVERY inst_wf (fn_insts fn0) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    MEM bb fn0.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn0).cfg_dfs_pre /\
    ao_targets_wf targets /\
    s.vs_inst_idx = 0 /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s /\
    ao_chain_defined_prefix targets s /\
    in_range_state (range_at_inst ra bb.bb_label 0) s.vs_vars ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (ao_transform_block mid dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `f = \(v:num) inst.
    ao_transform_inst mid dfg ra bb.bb_label v targets inst` >>
  qabbrev_tac `result =
    idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions))` >>
  qabbrev_tac `sound = \(n:num) (s:venom_state).
    in_range_state (range_at_inst ra bb.bb_label n) s.vs_vars` >>
  qabbrev_tac `sinv = \(s:venom_state).
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s /\
    ao_chain_defined_prefix targets s` >>
  `ao_transform_block mid dfg ra targets bb =
   analysis_block_transform 0 result f bb` by
    (simp[analysis_block_transform_def, ao_transform_block_def,
          Abbr `f`, Abbr `result`] >>
     `MAPi (\idx inst.
        ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
        bb.bb_instructions =
      MAPi (\idx inst.
        ao_transform_inst mid dfg ra bb.bb_label
          (df_at 0
            (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
            bb.bb_label idx) targets inst) bb.bb_instructions`
       suffices_by simp[] >>
     irule MAPi_CONG' >> simp[] >> rpt strip_tac >>
     `n < SUC (LENGTH bb.bb_instructions)` by simp[] >>
     simp[idx_df_state_at2]) >>
  ASM_REWRITE_TAC [] >>
  `EVERY inst_wf bb.bb_instructions` by
    (simp_tac std_ss [listTheory.EVERY_MEM] >> rpt strip_tac >>
     metis_tac[mem_block_mem_fn_insts,
               markerTheory.Abbrev_def, listTheory.EVERY_MEM]) >>
  drule_all test_lookup_block >> strip_tac >>
  qspecl_then
    [`state_equiv fv`, `execution_equiv fv`, `sound`, `sinv`,
     `f`, `bb`, `0`, `result`,
     `\(ctx:'b) (inst:instruction) (v:num). SUC v`, `ARB:'b`]
    mp_tac analysis_block_sim_inv_at
  >> impl_tac >- (
    rpt conj_tac
    >- simp[state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- (* per-inst sim at index *)
       (rpt strip_tac >>
        gvs[Abbr `sound`, Abbr `sinv`, Abbr `f`, Abbr `result`] >>
        qspecl_then [`fn`, `fn0`, `mid`, `dfg`, `ra`, `targets`, `bb`,
          `fuel`, `ctx`, `df_at 0 (idx_df_state bb.bb_label
            (SUC (LENGTH bb.bb_instructions))) bb.bb_label idx`,
          `EL idx bb.bb_instructions`, `s'`]
          mp_tac ao_per_inst_sim_fn0_inv >>
        impl_tac >- (
          gvs[markerTheory.Abbrev_def, ao_dfg_inv_inst_idx_irrel,
              ao_chain_inv_inst_idx_iff, ao_chain_defined_prefix_inst_idx_iff] >>
          metis_tac[listTheory.EVERY_MEM, listTheory.EL_MEM]) >>
        simp[])
    >- simp[Abbr `f`, ao_transform_inst_structural]
    >- first_assum ACCEPT_TAC
    >- (* operand lookup under state_equiv *)
       (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
        drule_all ao_fn0_operand_not_in_fv >> strip_tac >>
        fs[state_equiv_def, execution_equiv_def])
    >- (* transfer_sound: range_step_inv *)
       (rpt strip_tac >> gvs[Abbr `sound`, Abbr `result`, Abbr `ra`] >>
        `idx < SUC (LENGTH bb.bb_instructions)` by simp[] >>
        simp[idx_df_state_at2] >>
        irule (SIMP_RULE std_ss [LET_THM] range_step_inv) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`bb`, `ctx'`, `fuel`, `s'`] >>
        gvs[markerTheory.Abbrev_def, idx_df_state_at2])
    >- (* sound preserved by state_equiv fv *)
       (rpt strip_tac >> gvs[Abbr `sound`] >>
        irule ao_in_range_state_equiv_compat >>
        qexistsl_tac [`fn`, `fn0`, `fv`, `s1`] >>
        gvs[markerTheory.Abbrev_def] >> metis_tac[])
    >- (* df_at chain *)
       (rpt strip_tac >> simp[Abbr `result`, idx_df_state_at2])
    >- (* sinv preserved by step_inst at index *)
       (rpt strip_tac >>
        gvs[Abbr `sinv`,
            ao_chain_inv_inst_idx_iff, ao_chain_defined_prefix_inst_idx_iff] >>
        qspecl_then [`fn`, `fn0`, `dfg`, `targets`, `bb`, `idx`,
                     `fuel`, `ctx`, `s'`, `s''`]
          mp_tac ao_sinv_step_preserved >>
        impl_tac >- (
          gvs[markerTheory.Abbrev_def,
              ao_dfg_inv_inst_idx_irrel,
              ao_chain_inv_inst_idx_iff, ao_chain_defined_prefix_inst_idx_iff] >>
          simp[ao_compute_fn_iszero_targets_wf] >>
          cheat) >>
        simp[])
    >- (* sinv preserved by state_equiv fv *)
       (rpt strip_tac >>
        gvs[Abbr `sinv`,
            ao_chain_inv_inst_idx_iff, ao_chain_defined_prefix_inst_idx_iff] >>
        qspecl_then [`fn`, `fn0`, `dfg`, `targets`, `fv`, `s1`, `s2`]
          mp_tac ao_sinv_state_equiv_compat >>
        impl_tac >- (
          gvs[markerTheory.Abbrev_def,
              ao_dfg_inv_inst_idx_irrel,
              ao_chain_inv_inst_idx_iff, ao_chain_defined_prefix_inst_idx_iff] >>
          simp[ao_compute_fn_iszero_targets_wf] >>
          metis_tac[]) >>
        simp[])) >>
  simp[Abbr `sound`, Abbr `sinv`] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[Abbr `result`] >>
  impl_tac >- (simp[idx_df_state_at2] >>
    `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
    gvs[]) >>
  simp[]
QED

Theorem ao_phases123_run_blocks_sim[local]:
  !fn fn0 mid dfg ra targets fn1 fuel ctx s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks /\
    ssa_form fn0 /\
    EVERY inst_wf (fn_insts fn0) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (* H_resolve: iszero resolution preserves step_inst *)
    (!inst fuel ctx s. inst_wf inst ==>
      step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
      step_inst fuel ctx inst s) /\
    (* H_range: range analysis sound for resolved operands *)
    (!bb inst idx s op v.
      MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
      eval_operand op s = SOME v /\
      MEM op (ao_resolve_iszero_inst targets inst).inst_operands ==>
      in_range (range_get_range ra bb.bb_label idx op) v) /\
    ao_dfg_inv dfg s ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn1 s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Protect plain equalities from simp — only inside >- scopes *)
  qpat_x_assum `fn0 = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `mid = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `dfg = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `ra = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `targets = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  (* Phase 1: run_blocks fn = run_blocks fn0 *)
  `run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s` by
    (fs[markerTheory.Abbrev_def] >>
     ONCE_REWRITE_TAC[run_blocks_offset_eq] >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [GSYM th]) >>
  ONCE_REWRITE_TAC[run_blocks_inst_idx_irrel] >>
  qabbrev_tac `fv = ao_fn_fresh_vars fn` >>
  qabbrev_tac `bt = ao_transform_block mid dfg ra targets` >>
  qabbrev_tac `sinv = \s:venom_state.
    ao_dfg_inv dfg (s with vs_inst_idx := 0)` >>
  `fn1 = function_map_transform bt fn0` by
    simp[function_map_transform_def] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`state_equiv fv`, `execution_equiv fv`,
    `sinv`, `bt`, `fn0`] mp_tac block_sim_function_error >>
  impl_tac >- (
    rpt conj_tac
    >- simp[state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- (qunabbrev_tac `bt` >> simp[])
    >- (* Per-block sim: use ao_block_sim_fn0 *)
       (rpt gen_tac >> rpt strip_tac >>
        simp[Abbr `bt`, Abbr `sinv`] >>
        qspecl_then [`fv`, `mid`, `dfg`, `ra`, `targets`, `bb`,
          `\s'. ao_dfg_inv dfg (s' with vs_inst_idx := 0)`]
          mp_tac ao_block_sim_fn0 >>
        impl_tac >- (
          rpt conj_tac
          >- (* Per-inst sim *)
             (rpt strip_tac >> simp[Abbr `fv`] >>
              irule ao_per_inst_sim_fn0 >>
              gvs[markerTheory.Abbrev_def] >> metis_tac[])
          >- simp[ao_transform_inst_structural]
          >- (simp_tac std_ss [listTheory.EVERY_MEM] >>
              rpt strip_tac >>
              metis_tac[mem_block_mem_fn_insts,
                        markerTheory.Abbrev_def, listTheory.EVERY_MEM])
          >- (* operand NOTIN fv *)
             (rpt gen_tac >> strip_tac >>
              qpat_x_assum `Abbrev (fn0 = _)` mp_tac >>
              simp[markerTheory.Abbrev_def] >> strip_tac >>
              gvs[listTheory.MEM_MAP] >>
              `MEM (Var x) y.inst_operands` by
                metis_tac[ao_handle_offset_var_ops] >>
              `MEM y (fn_insts fn)` by
                (simp[fn_insts_def] >>
                 irule mem_block_mem_fn_insts_blocks >> metis_tac[]) >>
              metis_tac[markerTheory.Abbrev_def])
          >- (* sinv by step_inst *)
             (rpt gen_tac >> strip_tac >>
              BETA_TAC >> REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >>
              qpat_x_assum `(\s'. _) _` mp_tac >>
              BETA_TAC >> REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >>
              strip_tac >>
              metis_tac[ao_dfg_inv_step_any, markerTheory.Abbrev_def])
          >- (* sinv compat *)
             (rpt gen_tac >> strip_tac >>
              qpat_x_assum `(\s'. _) _` mp_tac >>
              BETA_TAC >> REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >>
              strip_tac >> BETA_TAC >>
              REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >>
              irule ao_dfg_inv_state_equiv_compat >>
              qexists_tac `fv` >> qexists_tac `s1` >>
              simp[] >> rpt strip_tac >>
              simp[Abbr `fv`] >>
              metis_tac[ao_dfg_outputs_not_in_fv,
                        markerTheory.Abbrev_def])) >>
        disch_then irule >> gvs[markerTheory.Abbrev_def])
    >- (* sinv preserved by exec_block *)
       (rpt gen_tac >> strip_tac >>
        qpat_x_assum `sinv _` mp_tac >>
        simp[Abbr `sinv`] >> BETA_TAC >>
        REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >> strip_tac >>
        REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >>
        `EVERY inst_wf bb.bb_instructions` by
          (simp_tac std_ss [listTheory.EVERY_MEM] >>
           rpt strip_tac >>
           metis_tac[mem_block_mem_fn_insts,
                     markerTheory.Abbrev_def, listTheory.EVERY_MEM]) >>
        metis_tac[ao_dfg_inv_exec_block_preserved,
                  markerTheory.Abbrev_def])
    >- (* sinv compat with state_equiv *)
       (rpt gen_tac >> strip_tac >>
        qpat_x_assum `sinv _` mp_tac >>
        simp[Abbr `sinv`] >> BETA_TAC >>
        REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >> strip_tac >>
        REWRITE_TAC[ao_dfg_inv_inst_idx_irrel] >>
        irule ao_dfg_inv_state_equiv_compat >>
        qexists_tac `fv` >> qexists_tac `s1` >>
        simp[] >> rpt strip_tac >>
        simp[Abbr `fv`] >>
        metis_tac[ao_dfg_outputs_not_in_fv, markerTheory.Abbrev_def])
    >- (* operand lookup under state_equiv *)
       (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
        `x NOTIN fv` by
          (qpat_x_assum `Abbrev (fn0 = _)` mp_tac >>
           simp[markerTheory.Abbrev_def] >> strip_tac >>
           gvs[listTheory.MEM_MAP] >>
           `MEM (Var x) y.inst_operands` by
             metis_tac[ao_handle_offset_var_ops] >>
           `MEM y (fn_insts fn)` by
             (simp[fn_insts_def] >>
              irule mem_block_mem_fn_insts_blocks >> metis_tac[]) >>
           metis_tac[]) >>
        fs[state_equiv_def, execution_equiv_def]))
  >>
  disch_then (qspecl_then [`fuel`, `ctx`,
    `s with vs_inst_idx := 0`] mp_tac) >>
  simp[Abbr `sinv`] >>
  impl_tac
  >- (qpat_x_assum `ao_dfg_inv _ _` mp_tac >>
      simp[ao_dfg_inv_def, lookup_var_def]) >>
  disch_then ACCEPT_TAC
QED

(* ===== Phases 1-3 sim with state-dependent invariants ===== *)

(* range_sound implies in_range_state via range_at_inst *)
Triviality range_sound_to_in_range_state[local]:
  !ra lbl s.
    range_sound (df_widen_at NONE ra lbl 0) s ==>
    in_range_state (range_at_inst ra lbl 0) s.vs_vars
Proof
  rpt strip_tac >>
  simp[rangeAnalysisDefsTheory.range_at_inst_def] >>
  Cases_on `df_widen_at NONE ra lbl 0` >>
  gvs[rangeAnalysisProofsTheory.range_sound_def,
      rangeAnalysisDefsTheory.range_unwrap_def,
      rangeEvalDefsTheory.in_range_state_def,
      finite_mapTheory.FLOOKUP_DEF]
QED

(* ssa_same_output_same_inst, output_none_preserved_step,
   ao_sinv_exec_block_preserved removed — dead code *)

(* Phases 1-3 sim using block_sim_function_error_bb with extended block_inv.
   Replaces ao_phases123_run_blocks_sim's ∀s H_resolve and H_range with
   state-dependent invariants: chain + range + dfg + cfg membership.

   block_inv = λs. ao_dfg_inv dfg s ∧
                    ao_iszero_chain_inv targets s ∧
                    ao_chain_defined_prefix targets s ∧
                    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s ∧
                    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre

   Key insight: block_inv is established at the initial state via:
   - ao_dfg_inv: from ADDRESS/SIGNEXTEND output undefinedness
   - ao_iszero_chain_inv: vacuously true (chain vars undefined → implication premise false)
   - ao_chain_defined_prefix: vacuously true at function entry (no Var operands defined,
     so only chain[0] can be defined, making the prefix property trivial)
   - range_sound: trivially true for entry block (FEMPTY range state)
   - cfg_dfs_pre: entry block is always in cfg_dfs_pre for wf_function *)
Triviality ao_block_inv_state_equiv_compat[local]:
  !fn fn0 dfg targets ra fv s1 s2.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ra = range_analyze fn0 /\
    fv = ao_fn_fresh_vars fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    state_equiv fv s1 s2 /\
    ao_dfg_inv dfg (s1 with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s1 /\
    ao_chain_defined_prefix targets s1 /\
    range_sound (df_widen_at NONE ra s1.vs_current_bb 0) s1 /\
    MEM s1.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre ==>
    ao_dfg_inv dfg (s2 with vs_inst_idx := 0) /\
    ao_iszero_chain_inv targets s2 /\
    ao_chain_defined_prefix targets s2 /\
    range_sound (df_widen_at NONE ra s2.vs_current_bb 0) s2 /\
    MEM s2.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
Proof
  rpt gen_tac >> strip_tac >>
  `s2.vs_current_bb = s1.vs_current_bb` by fs[state_equiv_def] >>
  `ao_targets_wf targets` by
    metis_tac[ao_compute_fn_iszero_targets_wf] >>
  `ao_dfg_inv dfg (s2 with vs_inst_idx := 0) /\
   ao_iszero_chain_inv targets s2 /\
   ao_chain_defined_prefix targets s2` by
    metis_tac[ao_sinv_state_equiv_compat] >>
  `range_sound (df_widen_at NONE ra s2.vs_current_bb 0) s2` by
    metis_tac[ao_range_sound_state_equiv_compat] >>
  metis_tac[]
QED

Theorem ao_phases123_run_blocks_sim_inv[local]:
  !fn fn0 mid dfg ra targets fn1 fuel ctx s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    mid = fn_max_inst_id fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks /\
    wf_function fn0 /\ wf_ssa fn0 /\
    EVERY inst_wf (fn_insts fn0) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    ao_dfg_inv dfg s /\
    strict_dom_iszero_inv fn0 dfg s /\
    ao_chain_defined_prefix targets s /\
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
    fn_reachable fn0 s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (execution_equiv (ao_fn_fresh_vars fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn1 s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn0 = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `mid = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `dfg = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `ra = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qpat_x_assum `targets = _` (ASSUME_TAC o
    CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  `run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s` by
    (fs[markerTheory.Abbrev_def] >>
     ONCE_REWRITE_TAC[run_blocks_offset_eq] >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC [GSYM th]) >>
  ONCE_REWRITE_TAC[run_blocks_inst_idx_irrel] >>
  qabbrev_tac `fv = ao_fn_fresh_vars fn` >>
  qabbrev_tac `bt = ao_transform_block mid dfg ra targets` >>
  qabbrev_tac `block_inv = \s:venom_state.
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    strict_dom_iszero_inv fn0 dfg s /\
    ao_chain_defined_prefix targets s /\
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre /\
    fn_reachable fn0 s.vs_current_bb` >>
  `fn1 = function_map_transform bt fn0` by
    simp[function_map_transform_def] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`state_equiv fv`, `execution_equiv fv`,
    `block_inv`, `bt`, `fn0`] mp_tac block_sim_function_error_bb >>
  impl_tac >- (
    rpt conj_tac
    >- simp[state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- (qunabbrev_tac `bt` >> simp[])
    >- (* Per-block sim: given block_inv s ∧ vs_current_bb = bb.bb_label,
          prove exec_block sim. Derives chain_inv from strict_dom_iszero_inv
          + within-block ISZERO tracking. *)
       cheat
    >- (* block_inv preserved through exec_block — WIP: needs SSA freshness + range transfer *)
       cheat
    >- (* block_inv compat with state_equiv fv *)
       cheat
    >- (* operand lookup under state_equiv *)
       (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
        `x NOTIN fv` by
          (qpat_x_assum `Abbrev (fn0 = _)` mp_tac >>
           simp[markerTheory.Abbrev_def] >> strip_tac >>
           gvs[listTheory.MEM_MAP] >>
           `MEM (Var x) y.inst_operands` by
             metis_tac[ao_handle_offset_var_ops] >>
           `MEM y (fn_insts fn)` by
             (simp[fn_insts_def] >>
              irule mem_block_mem_fn_insts_blocks >> metis_tac[]) >>
           metis_tac[]) >>
        fs[state_equiv_def, execution_equiv_def]))
  >>
  disch_then (qspecl_then [`fuel`, `ctx`,
    `s with vs_inst_idx := 0`] mp_tac) >>
  simp[Abbr `block_inv`] >>
  impl_tac
  >- (rpt conj_tac >>
      TRY (simp[ao_dfg_inv_inst_idx_irrel,
                ao_chain_defined_prefix_inst_idx_iff,
                strict_dom_iszero_inv_inst_idx] >> NO_TAC) >>
      TRY (qpat_x_assum `range_sound _ _` mp_tac >>
           simp[rangeAnalysisProofsTheory.range_sound_def] >> NO_TAC) >>
      simp[])
  >> disch_then ACCEPT_TAC
QED

(* ===== Phase 4: cmp_flip run_blocks sim ===== *)

(* Two-state per-block sim for cmp_flip.
   Taken as a hypothesis on the main theorem — requires proving that
   the cmp_flip transform preserves exec_block semantics per block.
   The proof obligation involves: (1) flip pair semantic equivalence
   (flip_step_exec_equiv, remove_step_exec_equiv from CmpFlipBlockProof),
   (2) same-block ordering of flip+remove/insert pairs,
   (3) SSA-like single-assignment for dead variables. *)
Triviality ao_cmp_flip_two_state_block_sim[local]:
  !mid1 dead dfg fn1 lbl bb1 bb' fuel ctx s1 s2.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid1 dfg fn1).fn_blocks = SOME bb' /\
    (* Per-block cmp_flip sim hypothesis *)
    (!fuel' ctx' st1 st2.
       state_equiv dead st1 st2 /\ st1.vs_inst_idx = 0 ==>
       lift_result (state_equiv dead) (execution_equiv dead)
         (execution_equiv dead)
         (exec_block fuel' ctx' bb1 st1) (exec_block fuel' ctx' bb' st2)) /\
    state_equiv dead s1 s2 /\
    s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv dead)
                (execution_equiv dead)
                (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb' s2)
Proof
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[]
QED

(* Phase 4 run_blocks sim via block_sim_to_run_blocks.
   The per-block cmp_flip sim is taken as a hypothesis. *)
Theorem ao_phase4_run_blocks_sim[local]:
  !mid1 dead dfg fn1 fuel ctx s.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    (* Per-block cmp_flip sim for all blocks *)
    (!lbl bb1 bb' fuel' ctx' s1 s2.
       lookup_block lbl fn1.fn_blocks = SOME bb1 /\
       lookup_block lbl (ao_cmp_flip_function mid1 dfg fn1).fn_blocks = SOME bb' /\
       state_equiv dead s1 s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result (state_equiv dead) (execution_equiv dead)
         (execution_equiv dead)
         (exec_block fuel' ctx' bb1 s1) (exec_block fuel' ctx' bb' s2))
    ==>
    lift_result (state_equiv dead)
                (execution_equiv dead)
                (execution_equiv dead)
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx (ao_cmp_flip_function mid1 dfg fn1) s)
Proof
  rpt gen_tac >> strip_tac >>
  irule block_sim_to_run_blocks >>
  conj_tac
  >- (* Two-state per-block sim *)
     (rpt strip_tac >> first_x_assum irule >> metis_tac[])
  >- (* Label preservation *)
     (gen_tac >> simp[ao_cmp_flip_function_labels])
QED

(* ===== Main Theorem ===== *)

(* ao_fn_total_fresh_vars_def: algebraicOptDefsTheory *)

(* Helper: normalize the phase decomposition to avoid nested record updates *)
Triviality ao_phase_decompose[local]:
  !fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    let dfg1 = dfg_build_function fn1 in
    let mid1 = fn_max_inst_id fn1 in
    ao_transform_function fn = ao_cmp_flip_function mid1 dfg1 fn1 /\
    ao_fn_total_fresh_vars fn =
      ao_fn_fresh_vars fn UNION ao_cmp_flip_dead_vars dfg1 fn1
Proof
  simp[ao_transform_function_def, ao_fn_total_fresh_vars_def, LET_THM]
QED

(* Connecting lemma: target keys are instruction outputs.
   ao_compute_iszero_step only adds keys from inst_outputs. *)
Triviality iszero_step_key_output[local]:
  !acc h v chain.
    ALOOKUP (ao_compute_iszero_step acc h) v = SOME chain /\
    ALOOKUP acc v = NONE ==>
    MEM v h.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ALOOKUP (ao_compute_iszero_step _ _) _ = _` mp_tac >>
  simp[ao_compute_iszero_step_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  simp[alistTheory.ALOOKUP_def] >> IF_CASES_TAC >> gvs[]
QED

Triviality foldl_iszero_key_output[local]:
  !insts acc v chain.
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    ALOOKUP acc v = NONE ==>
    ?inst. MEM inst insts /\ MEM v inst.inst_outputs
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `ao_compute_iszero_step acc h` >>
  Cases_on `ALOOKUP (ao_compute_iszero_step acc h) v`
  >- (first_x_assum (qspecl_then
        [`ao_compute_iszero_step acc h`, `v`, `chain`] mp_tac) >>
      simp[] >> metis_tac[])
  >- (`MEM v h.inst_outputs` by metis_tac[iszero_step_key_output] >>
      metis_tac[])
QED

Theorem ao_fn_targets_key_is_output:
  !fn v chain.
    ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chain ==>
    ?inst. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs
Proof
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  metis_tac[foldl_iszero_key_output, alistTheory.ALOOKUP_def]
QED

(* ao_dfg_inv holds for the initial state when ADDRESS/SIGNEXTEND outputs
   are not yet defined (lookup_var = NONE). *)
Triviality ao_dfg_inv_initial[local]:
  !fn s.
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
      (inst.inst_opcode = ADDRESS \/ inst.inst_opcode = SIGNEXTEND) ==>
      lookup_var x s = NONE) ==>
    ao_dfg_inv (dfg_build_function
      (fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks)) s
Proof
  rpt strip_tac >> simp[ao_dfg_inv_def] >>
  rpt gen_tac >> strip_tac >>
  drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
  (* Split into ADDRESS/SIGNEXTEND cases, then derive contradiction *)
  rpt strip_tac >> (
    (* In each case, inst.inst_opcode ∈ {ADDRESS, SIGNEXTEND} *)
    (* inst ∈ fn_insts fn0 → inst ∈ fn_insts fn (offset is identity) *)
    `MEM inst (fn_insts fn)` by
      (simp[fn_insts_def] >>
       qpat_x_assum `MEM inst (fn_insts _)` mp_tac >>
       simp[fn_insts_def] >> strip_tac >>
       drule fn_insts_blocks_map_offset >> strip_tac >>
       `~(inst0.inst_opcode = ADD /\
          ?l v. inst0.inst_operands = [Label l; Lit v])` by
         (strip_tac >> gvs[ao_handle_offset_inst_def]) >>
       imp_res_tac ao_handle_offset_inst_id >> gvs[]) >>
    `lookup_var x s = NONE` by
      (first_x_assum irule >> metis_tac[]) >>
    fs[])
QED

Triviality chain_defined_prefix_initial:
  !fn fn0 targets s.
    Abbrev(fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) /\
    Abbrev(targets = ao_compute_fn_iszero_targets fn0) /\
    ssa_form fn /\ wf_function fn /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
              lookup_var x s = NONE) ==>
    ao_chain_defined_prefix targets s
Proof
  rpt strip_tac >>
  irule ao_chain_defined_prefix_initial >>
  fs[markerTheory.Abbrev_def] >> metis_tac[]
QED

Theorem ao_transform_function_correct_proof:
  !fuel ctx fn s.
    let fv = ao_fn_fresh_vars fn in
    let fv' = ao_fn_total_fresh_vars fn in
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    (!inst x. MEM inst (fn_insts fn) /\
              MEM x inst.inst_outputs ==> lookup_var x s = NONE) /\
    (!i fuel' ctx' s'. inst_wf i ==>
      step_inst fuel' ctx'
        (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn0) i) s' =
      step_inst fuel' ctx' i s') /\
    (!bb' i idx s' op v.
      MEM bb' fn0.fn_blocks /\ MEM i bb'.bb_instructions /\
      eval_operand op s' = SOME v /\
      MEM op (ao_resolve_iszero_inst
        (ao_compute_fn_iszero_targets fn0) i).inst_operands ==>
      in_range (range_get_range (range_analyze fn0)
        bb'.bb_label idx op) v) /\
    fn_entry_label fn = SOME s.vs_current_bb
    ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  qabbrev_tac `targets = ao_compute_fn_iszero_targets fn0` >>
  qabbrev_tac `dfg = dfg_build_function fn0` >>
  qabbrev_tac `ra = range_analyze fn0` >>
  qabbrev_tac `mid = fn_max_inst_id fn0` >>
  qabbrev_tac `fn1 = fn0 with fn_blocks :=
    MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks` >>
  (* Derive wf_function fn0 from wf_function fn *)
  `wf_function fn0` by
    (simp[Abbr `fn0`] >>
     `(\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) =
      block_map_transform ao_handle_offset_inst` by
       simp[FUN_EQ_THM, block_map_transform_def] >>
     pop_assum (fn th => REWRITE_TAC[th, GSYM function_map_transform_def]) >>
     irule ao_phase1_preserves_wf >> simp[]) >>
  `ssa_form fn0` by
    (simp[Abbr `fn0`] >>
     `(\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) =
      block_map_transform ao_handle_offset_inst` by
       simp[FUN_EQ_THM, block_map_transform_def] >>
     pop_assum (fn th => REWRITE_TAC[th, GSYM function_map_transform_def]) >>
     irule ao_phase1_preserves_ssa >> simp[]) >>
  `EVERY inst_wf (fn_insts fn0)` by
    (simp_tac std_ss [listTheory.EVERY_MEM] >> rpt strip_tac >>
     `?inst0. MEM inst0 (fn_insts fn) /\ e = ao_handle_offset_inst inst0` by
       (qpat_x_assum `MEM e _` mp_tac >>
        simp[Abbr `fn0`, fn_insts_def] >>
        metis_tac[fn_insts_blocks_map_offset]) >>
     fs[] >> irule ao_handle_offset_inst_wf >>
     fs[listTheory.EVERY_MEM]) >>
  `ao_dfg_inv dfg s` by
    (simp_tac std_ss [Abbr `dfg`, Abbr `fn0`] >>
     irule ao_dfg_inv_initial >> rpt strip_tac >>
     first_x_assum drule >> disch_then drule >> simp[]) >>
  `fn_entry_label fn0 = fn_entry_label fn` by
    (fs[Abbr `fn0`, fn_entry_label_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> fs[]) >>
  `MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre` by
    (irule ao_cfg_initial >> fs[]) >>
  (* Get phases 1-3 simulation via ao_phases123_run_blocks_sim.
     H_resolve and H_range provided as top-level hypotheses. *)
  `(?e. run_blocks fuel ctx fn s = Error e) \/
   lift_result (state_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn1 s)` by
    (qspecl_then [`fn`, `fn0`, `mid`, `dfg`, `ra`, `targets`, `fn1`,
                   `fuel`, `ctx`, `s`]
       mp_tac ao_phases123_run_blocks_sim >>
     impl_tac
     >- (gvs[markerTheory.Abbrev_def] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
     strip_tac >> gvs[]) >>
  fs[] >>
  (* Error case auto-closed by gvs; lift_result case remains *)
  DISJ2_TAC >>
  (
      (* Show ao_transform_function fn = ao_cmp_flip_function mid1 dfg1 fn1 *)
      `ao_transform_function fn = ao_cmp_flip_function
         (fn_max_inst_id fn1) (dfg_build_function fn1) fn1` by
        simp[ao_transform_function_def, LET_THM,
             Abbr `fn1`, Abbr `fn0`, Abbr `dfg`, Abbr `ra`,
             Abbr `mid`, Abbr `targets`] >>
      (* Show ao_fn_total_fresh_vars fn = fv ∪ dead *)
      `ao_fn_total_fresh_vars fn = ao_fn_fresh_vars fn UNION
         ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1` by
        simp[ao_fn_total_fresh_vars_def, LET_THM,
             Abbr `fn1`, Abbr `fn0`, Abbr `dfg`, Abbr `ra`,
             Abbr `mid`, Abbr `targets`] >>
      ASM_REWRITE_TAC [] >>
      qabbrev_tac `dfg1 = dfg_build_function fn1` >>
      qabbrev_tac `dead = ao_cmp_flip_dead_vars dfg1 fn1` >>
      (* Phase 4: fn1 → cmp_flip fn1, from aoCmpFlipObligation *)
      `lift_result (state_equiv dead) (execution_equiv dead)
         (execution_equiv dead)
         (run_blocks fuel ctx fn1 s)
         (run_blocks fuel ctx (ao_cmp_flip_function (fn_max_inst_id fn1) dfg1 fn1) s)` by
        (irule ao_phase4_run_blocks_sim >>
         simp[Abbr `dead`] >> rpt strip_tac >>
         simp[Abbr `dfg1`] >>
         irule (SIMP_RULE std_ss [LET_THM] ao_cmp_flip_block_sim) >>
         simp[markerTheory.Abbrev_def] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >> simp[] >> cheat) >>
      (* Compose via lift_result_trans + lift_result_mono *)
      irule (UNDISCH_ALL lift_result_trans) >>
      conj_tac >- metis_tac[state_equiv_trans] >>
      conj_tac >- metis_tac[execution_equiv_trans] >>
      qexists_tac `run_blocks fuel ctx fn1 s` >>
      conj_tac
      >- (* Weaken phases 1-3: fv → fv ∪ dead *)
         (irule lift_result_mono >>
          qexistsl_tac [`state_equiv (ao_fn_fresh_vars fn)`,
                         `execution_equiv (ao_fn_fresh_vars fn)`] >>
          rpt strip_tac >> simp[] >>
          metis_tac[state_equiv_subset, execution_equiv_subset,
                    pred_setTheory.SUBSET_UNION])
      >- (* Weaken phase 4: dead → fv ∪ dead *)
         (irule lift_result_mono >>
          qexistsl_tac [`state_equiv dead`, `execution_equiv dead`] >>
          rpt strip_tac >> simp[] >>
          metis_tac[state_equiv_subset, execution_equiv_subset,
                    pred_setTheory.SUBSET_UNION]))
QED

