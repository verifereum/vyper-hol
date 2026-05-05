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
  algebraicOptDefs algebraicOptRules algebraicOptSegSim
  algebraicOptPeepholeSim algebraicOptResolveSim
  algebraicOptBlockSim algebraicOptCmpFlipSim
  passSimulationProps passSharedDefs venomExecSemantics stateEquiv
  venomInst venomState venomExecProofs stateEquivProps
  execEquivProps execEquivParamProps
  execEquivParamProofs venomWf
  analysisSimProofsBase analysisSimDefs

(* ===== Fresh Variable Set ===== *)

Definition ao_fn_fresh_vars_def:
  ao_fn_fresh_vars fn =
    { v | ?id.
        MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
        (v = ao_fresh_var id "not" \/
         v = ao_fresh_var id "iz" \/
         v = ao_fresh_var id "xor") }
End

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

Theorem ao_handle_offset_inst_outputs[local]:
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

(* Offset conversion preserves non-INVOKE for instruction lists *)
Triviality offset_map_no_invoke[local]:
  !insts. EVERY (\inst. inst.inst_opcode <> INVOKE) insts ==>
          EVERY (\inst. inst.inst_opcode <> INVOKE)
                (MAP ao_handle_offset_inst insts)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ao_handle_offset_not_invoke]
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
  !dfg ra lbl idx inst.
    is_terminator inst.inst_opcode /\ inst.inst_outputs <> [] ==>
    ao_peephole_inst dfg ra lbl idx inst = [inst]
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  simp[ao_peephole_inst_def, LET_THM]
QED

(* Comparator: non-special even without inst_wf.
   Separate because ao_opt_comparator is the most complex opt function. *)
Triviality ao_opt_comparator_non_special[local]:
  !dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (ao_opt_comparator dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  (* Split on operand pattern *)
  Cases_on `inst.inst_operands` >> gvs[listTheory.EVERY_DEF] >>
  Cases_on `t` >> gvs[listTheory.EVERY_DEF] >>
  Cases_on `t'` >> gvs[listTheory.EVERY_DEF] >>
  (* [h; h'] case: split op1=op2, then range_result *)
  IF_CASES_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  CASE_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  (* NONE branch: split all remaining ifs, then close *)
  rpt IF_CASES_TAC >>
  gvs[listTheory.EVERY_DEF, is_terminator_def,
      ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
      ao_cmp_prefer_iz_general_def] >>
  rpt CASE_TAC >>
  gvs[listTheory.EVERY_DEF, is_terminator_def]
QED

(* Peephole output is always non-terminator and non-INVOKE,
   regardless of inst_wf. Each ao_opt_* function returns either [inst]
   or instructions with explicit non-special opcodes (ASSIGN, ISZERO, etc). *)
Triviality ao_peephole_inst_non_special[local]:
  !dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (ao_peephole_inst dfg ra lbl idx inst)
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
  !dfg ra lbl targets.
    inst_transform_structural
      (\(v:num) inst. ao_transform_inst dfg ra lbl v targets inst)
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
          `ao_peephole_inst dfg ra lbl v
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
      qspecl_then [`dfg`, `ra`, `lbl`, `v`, `targets`, `inst`]
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
   Extracted to avoid tactic nesting issues in ao_transform_inst_sim. *)
Triviality ao_peephole_path_sim[local]:
  !fv dfg ra lbl targets fuel ctx v inst s.
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
          (ao_peephole_inst dfg ra lbl v
            (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)))) s)
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (ao_resolve_iszero_inst targets inst)` by
    (qspecl_then [`targets`, `inst`]
       mp_tac ao_resolve_iszero_inst_wf >> fs[]) >>
  qspecl_then [`fv`, `dfg`, `ra`, `lbl`, `v`,
    `ao_resolve_iszero_inst targets inst`,
    `fuel`, `ctx`, `s`]
    mp_tac ao_peephole_full_sim >>
  simp[ao_resolve_iszero_inst_opcode, ao_resolve_iszero_inst_id] >>
  impl_tac >- simp[] >>
  strip_tac
  >- (DISJ1_TAC >> metis_tac[])
  >- (DISJ2_TAC >> gvs[])
QED

(* Per-instruction simulation for ao_transform_inst.
   Hypotheses:
     H_resolve — iszero resolution preserves step_inst (chain correctness)
     H_fresh   — peephole fresh vars are in fv
     H_range   — range analysis sound for resolved operands
     H_producer — DFG producer optimization simulates original *)
Triviality ao_transform_inst_sim[local]:
  !fv dfg ra lbl targets.
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
      in_range (range_get_range ra lbl idx op) v) /\
    (* H_producer: DFG producer sim *)
    (!inst fuel ctx s.
      inst_wf inst /\
      inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\
      inst.inst_outputs <> [] /\
      inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
      inst.inst_opcode <> PARAM ==>
      !result.
        ao_opt_producer dfg (ao_resolve_iszero_inst targets inst) =
          SOME result ==>
        (?e. step_inst fuel ctx inst s = Error e) \/
        lift_result (state_equiv fv) (execution_equiv fv)
          (execution_equiv fv)
          (step_inst fuel ctx inst s)
          (run_insts fuel ctx (MAP ao_post_flip_inst result) s))
    ==>
    let f = \(v:num) inst. ao_transform_inst dfg ra lbl v targets inst in
    analysis_inst_simulates
      (state_equiv fv) (execution_equiv fv) (\v s. T) f
Proof
  simp[analysis_inst_simulates_def, LET_THM] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  conj_tac
  >- (* Simulation *)
     (rpt gen_tac >> strip_tac >>
      (* Establish resolution step equivalence *)
      rename1 `inst_wf inst` >>
      `step_inst fuel ctx (ao_resolve_iszero_inst targets inst) s =
       step_inst fuel ctx inst s` by
        (qpat_x_assum `!i f c st. _ ==>
           step_inst _ _ (ao_resolve_iszero_inst _ _) _ =
           step_inst _ _ _ _` irule >> simp[]) >>
      simp[ao_transform_inst_def, LET_THM,
           ao_resolve_iszero_inst_outputs,
           ao_resolve_iszero_inst_opcode] >>
      Cases_on `inst.inst_outputs = []`
      >- (* outputs=[]: returns [resolved inst], sim by step eq + refl *)
         (simp[run_insts_singleton] >> DISJ2_TAC >>
          pop_assum kall_tac >> pop_assum (fn th => REWRITE_TAC [th]) >>
          irule lift_result_refl >>
          simp[state_equiv_refl, execution_equiv_refl])
      >- (simp[] >>
          Cases_on `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
                    inst.inst_opcode = PARAM`
          >- (* ASSIGN/PHI/PARAM: returns [resolved inst] *)
             (simp[run_insts_singleton] >> DISJ2_TAC >>
              qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
                (fn th => REWRITE_TAC [th]) >>
              irule lift_result_refl >>
              simp[state_equiv_refl, execution_equiv_refl])
          >- (simp[] >>
              Cases_on `ao_opt_producer dfg
                (ao_resolve_iszero_inst targets inst)`
              >- (* NONE: peephole path *)
                 (simp[] >>
                  `~is_terminator inst.inst_opcode` by
                    (strip_tac >>
                     imp_res_tac terminator_no_outputs >> gvs[]) >>
                  Cases_on `inst.inst_opcode = INVOKE`
                  >- (* INVOKE: peephole is identity *)
                     (simp[ao_peephole_inst_def, LET_THM,
                           ao_resolve_iszero_inst_opcode,
                           ao_pre_flip_inst_non_comm,
                           ao_post_flip_inst_non_comm,
                           run_insts_singleton] >>
                      DISJ2_TAC >>
                      qpat_x_assum `step_inst _ _ (ao_resolve_iszero_inst _ _) _ = _`
                        (fn th => REWRITE_TAC [th]) >>
                      irule lift_result_refl >>
                      simp[state_equiv_refl, execution_equiv_refl])
                  >- (* Non-INVOKE: use ao_peephole_full_sim.
                        CHEATED: inst_wf preservation through resolve + peephole wiring *)
                     cheat)
              >- (* SOME: producer — use H_producer *)
                 (simp[] >>
                  qpat_x_assum `!i f c st. _ /\ _ /\ _ /\ _ /\ _ ==> _`
                    (qspecl_then [`inst`, `fuel`, `ctx`, `s`] mp_tac) >>
                  impl_tac >- gvs[] >>
                  disch_then (qspec_then `x` mp_tac) >>
                  simp[] >>
                  strip_tac
                  >- (DISJ1_TAC >> metis_tac[])
                  >- (DISJ2_TAC >> simp[])))))
  >- (* Structural: proved *)
     simp[ao_transform_inst_structural]
QED

(* Phase 4: cmp_flip block simulation.
   NULL case proved, non-NULL case cheated:
     When flips are NULL, function is unchanged so trivial by lift_result_refl.
     Non-NULL case needs cross-instruction reasoning (flip+remove pairs). *)
Triviality ao_cmp_flip_block_sim[local]:
  !fv dfg fn1 lbl bb1 bb' fuel ctx s.
    fv = ao_fn_fresh_vars fn1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function dfg fn1).fn_blocks = SOME bb' /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb1 s) (exec_block fuel ctx bb' s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `NULL (FST (ao_cmp_flip_scan dfg (fn_insts fn1)))`
  >- (* NULL flips: function unchanged *)
     (`ao_cmp_flip_function dfg fn1 = fn1` by
        (irule ao_cmp_flip_null_sim >> simp[]) >>
      `bb' = bb1` by metis_tac[optionTheory.SOME_11] >>
      gvs[] >>
      irule lift_result_refl >> simp[state_equiv_refl, execution_equiv_refl])
  >- (* Non-NULL: cross-instruction flip+remove reasoning needed.
        The flipped comparator output variable gets a different value,
        but the corresponding iszero-to-assign compensates. The net
        observable effect is the same, but out_var differs in state.
        Requires expanding fv to include dead flip output variables,
        or proving at function level instead of block level. *)
     cheat
QED

(* Single-state per-block sim: same state, different blocks.
   Uses analysis_block_sim_univ for the Phase 3 block lifting,
   then ao_cmp_flip_block_sim for Phase 4, composed via lift_result_trans. *)
(* Single-state per-block sim: compose Phase 3 (transform_block via
   analysis_block_sim_univ) with Phase 4 (cmp_flip_block_sim).
   Structure:
     exec_block bb0 s ≈ exec_block bb1 s  (Phase 3: peephole transform)
     exec_block bb1 s ≈ exec_block bb' s  (Phase 4: cmp flip)
   Composed via lift_result_trans. *)
Theorem ao_single_state_block_sim[local]:
  !fv fn lbl bb0 bb' fuel ctx s.
    fv = ao_fn_fresh_vars fn /\
    lookup_block lbl
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) = SOME bb0 /\
    lookup_block lbl (ao_transform_function fn).fn_blocks = SOME bb' /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb0 s) (exec_block fuel ctx bb' s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Unfold ao_transform_function to get fn1 (Phase 3 result) *)
  qabbrev_tac `fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  qabbrev_tac `targets = ao_compute_fn_iszero_targets fn0` >>
  qabbrev_tac `dfg = dfg_build_function fn0` >>
  qabbrev_tac `ra = range_analyze fn0` >>
  qabbrev_tac `fn1 = fn0 with fn_blocks :=
    MAP (ao_transform_block dfg ra targets) fn0.fn_blocks` >>
  qabbrev_tac `dfg1 = dfg_build_function fn1` >>
  (* Get bb1 from fn1 (Phase 3 output) *)
  `lookup_block lbl fn0.fn_blocks = SOME bb0` by
    (markerLib.UNABBREV_TAC "fn0" >> gvs[]) >>
  `?bb1. lookup_block lbl fn1.fn_blocks = SOME bb1` by
    (markerLib.UNABBREV_TAC "fn1" >>
     simp[lookup_block_map, ao_transform_block_def] >>
     Cases_on `lookup_block lbl fn0.fn_blocks` >> gvs[]) >>
  (* Relate bb' to ao_cmp_flip_function dfg1 fn1 *)
  `lookup_block lbl (ao_cmp_flip_function dfg1 fn1).fn_blocks = SOME bb'` by
    (qpat_x_assum `lookup_block _ (ao_transform_function fn).fn_blocks = _` mp_tac >>
     simp[ao_transform_function_def, LET_THM] >>
     markerLib.UNABBREV_TAC "fn0" >> markerLib.UNABBREV_TAC "targets" >>
     markerLib.UNABBREV_TAC "dfg" >> markerLib.UNABBREV_TAC "ra" >>
     markerLib.UNABBREV_TAC "fn1" >> markerLib.UNABBREV_TAC "dfg1" >>
     simp[]) >>
  (* Compose Phase 3 and Phase 4 via lift_result_trans *)
  mp_tac (Q.SPECL [`state_equiv fv`, `execution_equiv fv`] lift_result_trans) >>
  impl_tac >- (conj_tac >> metis_tac[state_equiv_trans, execution_equiv_trans]) >>
  disch_then (qspecl_then [`exec_block fuel ctx bb0 s`,
                           `exec_block fuel ctx bb1 s`,
                           `exec_block fuel ctx bb' s`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (* Phase 3: bb0 -> bb1 -- peephole transform via ao_phase3_block_sim.
            Cheated: ao_phase3_block_sim gives Error \/ lift_result, and we
            need unconditional lift_result. Also needs inst_wf and freshness
            preconditions not available in current theorem statement. *)
         cheat
      >- (* Phase 4: bb1 -> bb' -- cmp flip *)
         (Cases_on `NULL (FST (ao_cmp_flip_scan dfg1 (fn_insts fn1)))`
          >- (* NULL flips: function unchanged, bb' = bb1 *)
             (`ao_cmp_flip_function dfg1 fn1 = fn1` by
                (irule ao_cmp_flip_null_sim >> simp[]) >>
              `bb' = bb1` by metis_tac[optionTheory.SOME_11] >>
              gvs[] >>
              irule lift_result_refl >>
              simp[state_equiv_refl, execution_equiv_refl])
          >- (* Non-NULL: cross-instruction flip+remove *)
             cheat))
  >>
  simp[]
QED

(* Two-state per-block sim via triangle:
   exec_block bb0 s1 ≈ exec_block bb0 s2  (same block, two states)
   exec_block bb0 s2 ≈ exec_block bb' s2  (different blocks, same state)
   Compose via result_equiv_trans. *)
Theorem ao_per_block_sim[local]:
  !fv fn lbl bb0 bb' fuel ctx s1 s2.
    fv = ao_fn_fresh_vars fn /\
    (* No INVOKE in function (standard precondition for state_equiv proofs) *)
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (* Freshness: original operands don't use fresh variable names *)
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    lookup_block lbl
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) = SOME bb0 /\
    lookup_block lbl (ao_transform_function fn).fn_blocks = SOME bb' /\
    state_equiv fv s1 s2 /\
    s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb0 s1) (exec_block fuel ctx bb' s2)
Proof
  rpt gen_tac >> strip_tac >>
  (* Leg 1: same block bb0, two states s1/s2 — from exec_block_result_equiv *)
  (* Derive bb0 from original block via lookup_block_offset_fn *)
  `?orig_bb. lookup_block lbl fn.fn_blocks = SOME orig_bb /\
     bb0 = orig_bb with bb_instructions :=
       MAP ao_handle_offset_inst orig_bb.bb_instructions` by (
    gvs[lookup_block_offset_fn] >>
    Cases_on `lookup_block lbl fn.fn_blocks` >> gvs[]) >>
  (* Establish preconditions for exec_block_result_equiv *)
  (* Derive bb0.bb_instructions = MAP ao_handle_offset_inst ... *)
  `bb0.bb_instructions =
   MAP ao_handle_offset_inst orig_bb.bb_instructions` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb0.bb_instructions` by (
    pop_assum SUBST1_TAC >>
    match_mp_tac offset_map_no_invoke >>
    simp[listTheory.EVERY_MEM] >> rpt gen_tac >> strip_tac >>
    first_x_assum match_mp_tac >> simp[fn_insts_def] >>
    match_mp_tac lookup_block_inst_in_fn_insts >> metis_tac[]) >>
  `!i. MEM i bb0.bb_instructions ==>
       !x. MEM (Var x) i.inst_operands ==> x NOTIN fv` by (
    simp[] >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
    `?orig. MEM orig orig_bb.bb_instructions /\
            i = ao_handle_offset_inst orig` by
      (fs[listTheory.MEM_MAP] >> metis_tac[]) >>
    `MEM (Var x) orig.inst_operands` by
      metis_tac[ao_handle_offset_var_ops] >>
    `MEM orig (fn_insts fn)` by (
      simp[fn_insts_def] >>
      match_mp_tac lookup_block_inst_in_fn_insts >> metis_tac[]) >>
    metis_tac[]) >>
  `result_equiv fv (exec_block fuel ctx bb0 s1) (exec_block fuel ctx bb0 s2)`
    by metis_tac[exec_block_result_equiv] >>
  (* Leg 2: single-state sim bb0/s2 ≈ bb'/s2 *)
  `result_equiv fv (exec_block fuel ctx bb0 s2) (exec_block fuel ctx bb' s2)`
    by (simp[result_equiv_is_lift_result] >>
        `s2.vs_inst_idx = 0` by gvs[state_equiv_def] >>
        qspecl_then [`fv`, `fn`, `lbl`, `bb0`, `bb'`, `fuel`, `ctx`, `s2`]
          mp_tac ao_single_state_block_sim >>
        simp[]) >>
  (* Compose via result_equiv_trans *)
  simp[GSYM result_equiv_is_lift_result] >>
  metis_tac[result_equiv_trans]
QED

(* ===== Main Theorem ===== *)

Theorem ao_transform_function_correct_proof:
  !fuel ctx fn s.
    let fv = ao_fn_fresh_vars fn in
    (* No INVOKE in function (standard for state_equiv-based proofs) *)
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (* Freshness: original operands don't use fresh variable names *)
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv)
    ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  (* Phase 1: rewrite LHS to use offset-converted function *)
  CONV_TAC (RATOR_CONV (RAND_CONV
    (ONCE_REWRITE_CONV [GSYM run_blocks_offset_eq]))) >>
  (* Apply block_sim_to_run_blocks *)
  match_mp_tac block_sim_to_run_blocks >>
  conj_tac
  >- (* Same labels *)
     (gen_tac >>
      simp[fn0_same_labels, ao_transform_function_same_labels])
  >- (* Per-block sim: delegate to ao_per_block_sim *)
     (rpt gen_tac >> strip_tac >>
      match_mp_tac ao_per_block_sim >>
      qexists_tac `fn` >> qexists_tac `lbl` >> fs[] >>
      metis_tac[])
QED

