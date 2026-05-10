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
  passSimulationProps passSimulationDefs passSharedDefs venomExecSemantics stateEquiv
  venomInst venomState venomExecProofs stateEquivProps
  execEquivProps execEquivParamProps
  execEquivParamProofs venomWf
  analysisSimProofsBase analysisSimDefs dfAnalyzeDefs indexedLists
Libs
  fcpLib

(* ===== Fresh Variable Set ===== *)

Definition ao_fn_fresh_vars_def:
  ao_fn_fresh_vars fn =
    { v | ?id.
        MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
        (v = ao_fresh_var id "not" \/
         v = ao_fresh_var id "iz" \/
         v = ao_fresh_var id "xor") }
End

(* DFG runtime invariant for the algebraic optimization.
   If a variable is tracked by the DFG and has a value in the state,
   that value is consistent with the instruction that produced it.
   Only constrains ADDRESS and SIGNEXTEND outputs — the two opcodes
   where ao_opt_producer applies non-trivial transforms. *)
Definition ao_dfg_inv_def:
  ao_dfg_inv dfg s <=>
    !x inst val. dfg_get_def dfg x = SOME inst /\
      lookup_var x s = SOME val ==>
      (inst.inst_opcode = ADDRESS ==>
        val = w2w s.vs_call_ctx.cc_address) /\
      (inst.inst_opcode = SIGNEXTEND ==>
        !w inner_op. inst.inst_operands = [Lit w; inner_op] ==>
        ?inner_val. val = sign_extend w inner_val)
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
   Uses original inst in step_inst, resolved inst for peephole. *)
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
    (irule ao_resolve_iszero_inst_wf >> simp[]) >>
  qspecl_then [`fv`, `dfg`, `ra`, `lbl`, `v`,
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
      in_range (range_get_range ra lbl idx op) v)
    ==>
    let f = \(v:num) inst. ao_transform_inst dfg ra lbl v targets inst in
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

(* Variables whose values may change under cmp_flip:
   - Comparator outputs that get flipped (out_var differs)
   - Fresh variables introduced by insert (ISZERO before ASSERT) *)
Definition ao_cmp_flip_dead_vars_def:
  ao_cmp_flip_dead_vars dfg fn =
    let (flips, removes, inserts) = ao_cmp_flip_scan dfg (fn_insts fn) in
    { v | ?inst. MEM inst (fn_insts fn) /\
          MEM inst.inst_id (MAP FST flips) /\
          MEM v inst.inst_outputs } UNION
    { fresh | ?aid out_var cmp_id.
          MEM (aid, out_var, fresh, cmp_id) inserts }
End

(* ===== Phases 1-3: offset + iszero + peephole (single-state block sim) ===== *)

(* Per-block sim for phases 1-3: directly from ao_phase3_block_sim.
   Takes analysis_inst_simulates + inst_wf as hypotheses — these capture
   per-instruction soundness that depends on H_resolve, H_range, ao_dfg_inv.
   Conclusion relates exec_block on bb to exec_block on ao_transform_block bb. *)
Theorem ao_phases123_block_sim[local]:
  !fv dfg ra targets bb fuel ctx s.
    analysis_inst_simulates (state_equiv fv) (execution_equiv fv) (\v s. T)
      (\v inst. ao_transform_inst dfg ra bb.bb_label v targets inst) /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fv) /\
    s.vs_inst_idx = 0 ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (ao_transform_block dfg ra targets bb) s)
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
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block dfg ra targets) fn0.fn_blocks in
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
  !dfg ra targets bb.
    (ao_transform_block dfg ra targets bb).bb_label = bb.bb_label
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
   Terminators: vars and call_ctx preserved, so ao_dfg_inv holds.
   Non-terminators: use ao_dfg_inv_step_preserved. *)
Triviality ao_dfg_inv_step_any[local]:
  !dfg fn0 bb inst fuel ctx s s'.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode <> INVOKE /\ inst_wf inst /\
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
  >- metis_tac[ao_dfg_inv_step_preserved]
QED

(* ao_dfg_inv preserved by exec_block under SSA. *)
Triviality ao_dfg_inv_exec_block_preserved[local]:
  !dfg fn0 bb fuel ctx s s'.
    ssa_form fn0 /\ dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
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
  `inst.inst_opcode <> INVOKE` by
    (fs[listTheory.EVERY_MEM] >> res_tac) >>
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
  !fv dfg ra targets bb (state_inv : venom_state -> bool).
    (!fuel ctx v inst s.
       MEM inst bb.bb_instructions /\
       state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
         (step_inst fuel ctx inst s)
         (run_insts fuel ctx
           (ao_transform_inst dfg ra bb.bb_label v targets inst) s)) /\
    inst_transform_structural
      (\v inst. ao_transform_inst dfg ra bb.bb_label v targets inst) /\
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
        (exec_block fuel ctx (ao_transform_block dfg ra targets bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Define safe wrapper: identity for non-block instructions *)
  qabbrev_tac `f_safe = \(v:num) inst.
    if MEM inst bb.bb_instructions
    then ao_transform_inst dfg ra bb.bb_label v targets inst
    else [inst]` >>
  (* Rewrite ao_transform_block to analysis_block_transform with f_safe *)
  `ao_transform_block dfg ra targets bb =
   analysis_block_transform 0
     (idx_df_state bb.bb_label (SUC (LENGTH bb.bb_instructions)))
     f_safe bb` by
    (simp[analysis_block_transform_def, ao_transform_block_def] >>
     `MAPi (\idx inst.
        ao_transform_inst dfg ra bb.bb_label idx targets inst)
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
Triviality fn_insts_blocks_map_offset[local]:
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
  simp[fn_insts_def] >> metis_tac[]
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
  !fv dfg ra lbl targets fuel ctx v inst s.
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
        (ao_transform_inst dfg ra lbl v targets inst) s)
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
Triviality ao_per_inst_sim_fn0[local]:
  !fn fn0 dfg ra targets bb fuel ctx v inst s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
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
        (ao_transform_inst dfg ra bb.bb_label v targets inst) s)
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

Theorem ao_phases123_run_blocks_sim[local]:
  !fn fn0 dfg ra targets fn1 fuel ctx s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block dfg ra targets) fn0.fn_blocks /\
    ssa_form fn0 /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
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
  qabbrev_tac `bt = ao_transform_block dfg ra targets` >>
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
        qspecl_then [`fv`, `dfg`, `ra`, `targets`, `bb`,
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
              `inst.inst_opcode <> INVOKE` by
                (qpat_x_assum `MEM inst bb.bb_instructions` mp_tac >>
                 qpat_x_assum `MEM bb fn0.fn_blocks` mp_tac >>
                 qpat_x_assum `Abbrev (fn0 = _)` mp_tac >>
                 simp[markerTheory.Abbrev_def, listTheory.MEM_MAP] >>
                 rpt strip_tac >> gvs[] >>
                 fs[listTheory.MEM_MAP] >>
                 metis_tac[ao_handle_offset_not_invoke,
                           mem_block_mem_fn_insts_blocks,
                           fn_insts_def]) >>
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
        `EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions` by
          (qpat_x_assum `Abbrev (fn0 = _)` mp_tac >>
           simp[markerTheory.Abbrev_def] >> strip_tac >>
           `?bb0. MEM bb0 fn.fn_blocks /\
                  bb.bb_instructions =
                    MAP ao_handle_offset_inst bb0.bb_instructions` by
             (gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
           ASM_REWRITE_TAC[] >>
           irule offset_map_no_invoke >>
           simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
           `MEM inst (fn_insts fn)` by
             (simp[fn_insts_def] >>
              irule mem_block_mem_fn_insts_blocks >> metis_tac[]) >>
           res_tac) >>
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

(* ===== Phase 4: cmp_flip run_blocks sim ===== *)

(* Two-state per-block sim for cmp_flip.
   Taken as a hypothesis on the main theorem — requires proving that
   the cmp_flip transform preserves exec_block semantics per block.
   The proof obligation involves: (1) flip pair semantic equivalence
   (flip_step_exec_equiv, remove_step_exec_equiv from CmpFlipBlockProof),
   (2) same-block ordering of flip+remove/insert pairs,
   (3) SSA-like single-assignment for dead variables. *)
Triviality ao_cmp_flip_two_state_block_sim[local]:
  !dead dfg fn1 lbl bb1 bb' fuel ctx s1 s2.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function dfg fn1).fn_blocks = SOME bb' /\
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
  !dead dfg fn1 fuel ctx s.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    (* Per-block cmp_flip sim for all blocks *)
    (!lbl bb1 bb' fuel' ctx' s1 s2.
       lookup_block lbl fn1.fn_blocks = SOME bb1 /\
       lookup_block lbl (ao_cmp_flip_function dfg fn1).fn_blocks = SOME bb' /\
       state_equiv dead s1 s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result (state_equiv dead) (execution_equiv dead)
         (execution_equiv dead)
         (exec_block fuel' ctx' bb1 s1) (exec_block fuel' ctx' bb' s2))
    ==>
    lift_result (state_equiv dead)
                (execution_equiv dead)
                (execution_equiv dead)
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx (ao_cmp_flip_function dfg fn1) s)
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

(* Total fresh+dead var set for the full transform *)
Definition ao_fn_total_fresh_vars_def:
  ao_fn_total_fresh_vars fn =
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block dfg ra targets) fn0.fn_blocks in
    let dfg1 = dfg_build_function fn1 in
    ao_fn_fresh_vars fn UNION ao_cmp_flip_dead_vars dfg1 fn1
End

(* Helper: normalize the phase decomposition to avoid nested record updates *)
Triviality ao_phase_decompose[local]:
  !fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block dfg ra targets) fn0.fn_blocks in
    let dfg1 = dfg_build_function fn1 in
    ao_transform_function fn = ao_cmp_flip_function dfg1 fn1 /\
    ao_fn_total_fresh_vars fn =
      ao_fn_fresh_vars fn UNION ao_cmp_flip_dead_vars dfg1 fn1
Proof
  simp[ao_transform_function_def, ao_fn_total_fresh_vars_def, LET_THM]
QED

Theorem ao_transform_function_correct_proof:
  !fuel ctx fn s.
    let fv = ao_fn_fresh_vars fn in
    let fv' = ao_fn_total_fresh_vars fn in
    (* No INVOKE in function (standard for state_equiv-based proofs) *)
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (* Freshness: original operands don't use fresh variable names *)
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (* Well-formedness *)
    ssa_form fn /\ EVERY inst_wf (fn_insts fn)
    ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  (* Abbreviate intermediate functions to avoid term explosion *)
  qabbrev_tac `fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` >>
  qabbrev_tac `targets = ao_compute_fn_iszero_targets fn0` >>
  qabbrev_tac `dfg = dfg_build_function fn0` >>
  qabbrev_tac `ra = range_analyze fn0` >>
  qabbrev_tac `fn1 = fn0 with fn_blocks :=
    MAP (ao_transform_block dfg ra targets) fn0.fn_blocks` >>
  (* Get phases 1-3 simulation: Error \/ lift_result *)
  `(?e. run_blocks fuel ctx fn s = Error e) \/
   lift_result (state_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (execution_equiv (ao_fn_fresh_vars fn))
     (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn1 s)` by
    (irule ao_phases123_run_blocks_sim >>
     rpt conj_tac >> fs[markerTheory.Abbrev_def] >>
     TRY (cheat (* ssa_form fn0, EVERY inst_wf fn0, ao_dfg_inv *))) >>
  gvs[] >>
  (* Error case auto-closed by gvs; lift_result case remains *)
  DISJ2_TAC >>
  (
      (* Show ao_transform_function fn = ao_cmp_flip_function dfg1 fn1 *)
      `ao_transform_function fn = ao_cmp_flip_function
         (dfg_build_function fn1) fn1` by
        simp[ao_transform_function_def, LET_THM,
             Abbr `fn1`, Abbr `fn0`, Abbr `dfg`, Abbr `ra`, Abbr `targets`] >>
      (* Show ao_fn_total_fresh_vars fn = fv ∪ dead *)
      `ao_fn_total_fresh_vars fn = ao_fn_fresh_vars fn UNION
         ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1` by
        simp[ao_fn_total_fresh_vars_def, LET_THM,
             Abbr `fn1`, Abbr `fn0`, Abbr `dfg`, Abbr `ra`, Abbr `targets`] >>
      ASM_REWRITE_TAC [] >>
      qabbrev_tac `dfg1 = dfg_build_function fn1` >>
      qabbrev_tac `dead = ao_cmp_flip_dead_vars dfg1 fn1` >>
      (* Phase 4: fn1 → cmp_flip fn1 *)
      `lift_result (state_equiv dead) (execution_equiv dead)
         (execution_equiv dead)
         (run_blocks fuel ctx fn1 s)
         (run_blocks fuel ctx (ao_cmp_flip_function dfg1 fn1) s)` by
        (* CHEATED subgoal: per-block cmp_flip sim not yet proved
           (tasks #2/#3: ao_cmp_flip_block_sim) *)
        (irule ao_phase4_run_blocks_sim >>
         simp[Abbr `dead`, Abbr `dfg1`, Abbr `fn1`, Abbr `fn0`,
              Abbr `dfg`, Abbr `ra`, Abbr `targets`] >> cheat) >>
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

