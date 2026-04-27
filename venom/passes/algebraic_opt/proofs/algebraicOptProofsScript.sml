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
  passSimulationProps venomExecSemantics stateEquiv
  venomInst venomState venomExecProofs stateEquivProps
  execEquivProps execEquivParamProps

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
Theorem block_sim_to_run_blocks[local]:
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
  rw[ao_fresh_var_def] >> simp[stringTheory.STRCAT_11]
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

(* ===== Per-block simulation: phases 2-4 ===== *)

(* Single-state per-block sim: same state, different blocks.
   This is the core correctness of the peephole transformation.
   Agents A and B prove the per-instruction and per-phase parts. *)
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
  (* Agents A+B prove the per-instruction simulation.
     This theorem lifts it to exec_block level. *)
  cheat
QED

(* Two-state per-block sim via triangle:
   exec_block bb0 s1 ≈ exec_block bb0 s2  (same block, two states)
   exec_block bb0 s2 ≈ exec_block bb' s2  (different blocks, same state)
   Compose via result_equiv_trans. *)
Theorem ao_per_block_sim[local]:
  !fv fn lbl bb0 bb' fuel ctx s1 s2.
    fv = ao_fn_fresh_vars fn /\
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
  (* Leg 1: same block bb0, two states s1/s2 — from exec_block_preserves_R *)
  qabbrev_tac `fn0_rec = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  `result_equiv fv (exec_block fuel ctx bb0 s1) (exec_block fuel ctx bb0 s2)`
    by cheat >>
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
    (* Freshness: original operands don't use fresh variable names *)
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv)
    ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  qabbrev_tac `fv = ao_fn_fresh_vars fn` >>
  qabbrev_tac `fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  qabbrev_tac `fn' = ao_transform_function fn` >>
  (* Phase 1: run_blocks fn s = run_blocks fn0 s (equality) *)
  `run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s`
    by (unabbrev_all_tac >> simp[run_blocks_offset_eq]) >>
  (* Phase 1 lift_result (trivial from equality) *)
  `lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
     (run_blocks fuel ctx fn s)
     (run_blocks fuel ctx fn0 s)`
    by (pop_assum (fn eq => simp[GSYM eq]) >>
        irule lift_result_refl >>
        simp[state_equiv_refl, execution_equiv_refl]) >>
  (* Phases 2-4: run_blocks fn0 s ≤ run_blocks fn' s *)
  `lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
     (run_blocks fuel ctx fn0 s)
     (run_blocks fuel ctx fn' s)`
    by (qspecl_then [`fv`, `fn0`, `fn'`] mp_tac block_sim_to_run_blocks >>
        impl_tac
        >- (conj_tac
            >- (* Block label preservation *)
               (rw[] >> markerLib.UNABBREV_TAC "fn0" >>
                markerLib.UNABBREV_TAC "fn'" >>
                simp[fn0_same_labels, ao_transform_function_same_labels])
            >> (* Per-block two-state simulation:
                  uses ao_per_block_sim (which uses ao_single_state_block_sim).
                  Connection needs interactive debugging for variable scoping. *)
               cheat)
        >> disch_then (qspecl_then [`fuel`, `ctx`, `s`] ACCEPT_TAC)) >>
  (* Compose: fn ≤ fn0 ≤ fn' using lift_result_trans *)
  qspecl_then [`state_equiv fv`, `execution_equiv fv`] mp_tac lift_result_trans >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> metis_tac[state_equiv_trans_local])
      >> (rpt strip_tac >> metis_tac[execution_equiv_trans_local])) >>
  rw[] >>
  first_x_assum (drule_all_then ACCEPT_TAC)
QED

