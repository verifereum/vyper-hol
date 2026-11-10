(*
 * Branch Optimization Pass — Output Checker Soundness
 *
 * check_branch_opt_fn fn fn' implies that fn' runs like fn, from any state:
 * the two runs end alike, and their states agree on everything except the
 * variables that only fn' has (the temporaries of rewrite 2). The check is
 * the only premise: nothing about fn (SSA, well-formedness) or the state.
 *
 * TOP-LEVEL:
 *   check_branch_opt_fn_run_blocks   — block-level simulation, any fuel
 *   check_branch_opt_fn_run_function — the same from a function's entry
 *)
Theory branchOptCheckProofs
Ancestors
  branchOptCheck stateEquiv stateEquivProps execEquivParamProps
  execEquivParamBase execEquivProofs venomExecProofs venomExecSemantics venomState venomInst venomInstProps
  venomWfProps irSupply list rich_list pred_set finite_map

(* ===== The instructions of the rewrites ===== *)

val step_inst_base_for = let
  fun key th = rhs (fst (dest_imp (snd (strip_forall (concl th)))))
  val eqs = map (fn th => (key th, th))
    (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs)
in fn opc => #2 (valOf (List.find (fn (k, _) => aconv k opc) eqs)) end;

Theorem step_inst_jnz[local]:
  inst.inst_opcode = JNZ /\ inst.inst_operands = [c; Label a; Label b] ==>
  step_inst fuel ctx inst s =
    case eval_operand c s of
      SOME w => OK (jump_to (if w <> 0w then a else b) s)
    | NONE => Error "undefined condition"
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_for ``JNZ``] >>
  CASE_TAC >> rw[]
QED

Theorem step_inst_iszero[local]:
  inst.inst_opcode = ISZERO /\ inst.inst_operands = [c] /\
  inst.inst_outputs = [out] ==>
  step_inst fuel ctx inst s =
    case eval_operand c s of
      SOME w => OK (update_var out (bool_to_word (w = 0w)) s)
    | NONE => Error "undefined operand"
Proof
  strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_for ``ISZERO``, exec_pure1_def] >>
  CASE_TAC >> simp[]
QED

Theorem EL_prefix_append[local]:
  !pre. EL (LENGTH pre) (pre ++ i::rest) = i /\
        EL (SUC (LENGTH pre)) (pre ++ i::j::rest) = j
Proof
  Induct >> simp[]
QED

(* ===== state_equiv facts ===== *)

Theorem state_equiv_halted[local]:
  state_equiv N s1 s2 ==> s1.vs_halted = s2.vs_halted
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  `(execution_frame s1).vs_halted = (execution_frame s2).vs_halted`
    by asm_rewrite_tac[] >>
  fs[stateFrameTheory.execution_frame_def]
QED

Theorem state_equiv_update_right[local]:
  state_equiv N s1 s2 /\ x IN N ==> state_equiv N s1 (update_var x w s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE] >>
  rw[] >> gvs[lookup_var_def]
QED

Theorem state_equiv_lookup[local]:
  state_equiv N s1 s2 /\ x NOTIN N ==> lookup_var x s1 = lookup_var x s2
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* A terminator's OK result ends the block alike on both sides. *)
Theorem terminator_ok_related[local]:
  state_equiv N s1 s2 ==>
  lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
    (if s1.vs_halted then Halt s1 else OK s1)
    (if s2.vs_halted then Halt s2 else OK s2)
Proof
  strip_tac >> imp_res_tac state_equiv_halted >>
  rw[lift_result_def, state_equiv_implies_execution_equiv]
QED

(* ===== bo_iszero_src ===== *)

Theorem bo_iszero_src_SOME[local]:
  !l v x. bo_iszero_src v l = SOME x ==>
    ?k. k < LENGTH l /\
        (EL k l).inst_opcode = ISZERO /\ (EL k l).inst_operands = [x] /\
        (EL k l).inst_outputs = [v] /\ x <> Var v /\ (!lbl. x <> Label lbl) /\
        !j. j < k ==> ~MEM v (EL j l).inst_outputs /\
                      ~MEM x (MAP Var (EL j l).inst_outputs)
Proof
  Induct >> simp[bo_iszero_src_def] >> rpt gen_tac >>
  IF_CASES_TAC
  >- (rw[] >> gvs[AllCaseEqs()] >> qexists_tac `0` >> simp[]) >>
  CASE_TAC >> rw[] >> first_x_assum drule >> strip_tac >>
  qexists_tac `SUC k` >> simp[] >> Cases >> simp[]
QED

(* The same, for the block's instructions in program order. *)
Theorem bo_iszero_src_REVERSE[local]:
  bo_iszero_src v (REVERSE pre) = SOME x ==>
  ?k. k < LENGTH pre /\
      (EL k pre).inst_opcode = ISZERO /\ (EL k pre).inst_operands = [x] /\
      (EL k pre).inst_outputs = [v] /\ x <> Var v /\ (!lbl. x <> Label lbl) /\
      !j. k < j /\ j < LENGTH pre ==>
          ~MEM v (EL j pre).inst_outputs /\
          ~MEM x (MAP Var (EL j pre).inst_outputs)
Proof
  strip_tac >> drule bo_iszero_src_SOME >> strip_tac >>
  fs[LENGTH_REVERSE] >>
  qexists_tac `PRE (LENGTH pre - k)` >>
  `EL k (REVERSE pre) = EL (PRE (LENGTH pre - k)) pre` by simp[EL_REVERSE] >>
  gvs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < k ==> _` (qspec_then `PRE (LENGTH pre - j)` mp_tac) >>
  `PRE (LENGTH pre - j) < k` by simp[] >>
  `PRE (LENGTH pre - j) < LENGTH pre` by simp[] >>
  `PRE (LENGTH pre - PRE (LENGTH pre - j)) = j` by simp[] >>
  simp[EL_REVERSE]
QED

(* ===== Blocks with a common prefix ===== *)

(* Two blocks that share an instruction prefix run alike through it, from
   any index in it: P is an invariant of the source block's states along the
   prefix, and the last hypothesis covers the two tails. *)
Theorem exec_block_common_prefix[local]:
  !N P pre t1 t2 bb1 bb2 fuel ctx.
    bb1.bb_instructions = pre ++ t1 /\ bb2.bb_instructions = pre ++ t2 /\
    (!inst x. MEM inst pre /\ MEM (Var x) inst.inst_operands ==> x NOTIN N) /\
    (!i s s'. i < LENGTH pre /\ P i s /\
       step_inst fuel ctx (EL i pre) s = OK s' /\
       ~is_terminator (EL i pre).inst_opcode ==>
       P (SUC i) (s' with vs_inst_idx := SUC i)) /\
    (!s1 s2. state_equiv N s1 s2 /\ s1.vs_inst_idx = LENGTH pre /\
       P (LENGTH pre) s1 ==>
       lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
         (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)) ==>
    !n s1 s2. n = LENGTH pre - s1.vs_inst_idx /\
      s1.vs_inst_idx <= LENGTH pre /\ state_equiv N s1 s2 /\
      P s1.vs_inst_idx s1 ==>
      lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
        (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt gen_tac >> strip_tac >> Induct >> rpt strip_tac
  >- (`s1.vs_inst_idx = LENGTH pre` by simp[] >> metis_tac[]) >>
  `s1.vs_inst_idx < LENGTH pre` by simp[] >>
  `s2.vs_inst_idx = s1.vs_inst_idx` by fs[state_equiv_def] >>
  qabbrev_tac `i = s1.vs_inst_idx` >>
  qabbrev_tac `inst = EL i pre` >>
  `MEM inst pre` by simp[Abbr `inst`, EL_MEM] >>
  `lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
     (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)`
    by (irule step_inst_preserves_R >>
        simp[state_equiv_execution_equiv_valid_state_rel] >>
        metis_tac[state_equiv_lookup]) >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  simp[get_instruction_def, EL_APPEND1] >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >> gvs[lift_result_def] >>
  IF_CASES_TAC >- simp[terminator_ok_related] >>
  simp[] >>
  qpat_x_assum `!s1 s2. n = _ /\ _ ==> _` irule >>
  simp[state_equiv_inst_idx] >>
  fs[Abbr `inst`] >>
  qpat_x_assum `!i s s'. _` irule >> simp[] >> metis_tac[]
QED

Theorem eval_phis_append_non_phi[local]:
  !pre t s. (t = [] \/ (HD t).inst_opcode <> PHI) ==>
    eval_phis s (pre ++ t) = eval_phis s pre /\
    phi_prefix_length (pre ++ t) = phi_prefix_length pre
Proof
  Induct >> rpt gen_tac >> disch_tac
  >- (Cases_on `t` >> gvs[eval_phis_def, phi_prefix_length_def]) >>
  first_x_assum drule >> strip_tac >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem phi_prefix_length_non_phi[local]:
  !l k. k < LENGTH l /\ (EL k l).inst_opcode <> PHI ==>
        phi_prefix_length l <= k
Proof
  Induct >> rw[phi_prefix_length_def] >> Cases_on `k` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* run_block of two blocks with a common prefix and non-PHI tails. *)
Theorem run_block_common_prefix[local]:
  !N P pre t1 t2 bb1 bb2 fuel ctx s1 s2.
    bb1.bb_instructions = pre ++ t1 /\ bb2.bb_instructions = pre ++ t2 /\
    (t1 = [] \/ (HD t1).inst_opcode <> PHI) /\
    (t2 = [] \/ (HD t2).inst_opcode <> PHI) /\
    (!inst x. MEM inst pre /\ MEM (Var x) inst.inst_operands ==> x NOTIN N) /\
    (!i s s'. i < LENGTH pre /\ P i s /\
       step_inst fuel ctx (EL i pre) s = OK s' /\
       ~is_terminator (EL i pre).inst_opcode ==>
       P (SUC i) (s' with vs_inst_idx := SUC i)) /\
    (!s1 s2. state_equiv N s1 s2 /\ s1.vs_inst_idx = LENGTH pre /\
       P (LENGTH pre) s1 ==>
       lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
         (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)) /\
    (!s. P (phi_prefix_length pre) s) /\
    state_equiv N s1 s2 ==>
    lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==>
                lookup_var x s1 = lookup_var x s2) pre`
    by (simp[EVERY_MEM] >> metis_tac[state_equiv_lookup]) >>
  `s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_def] >>
  assume_tac (Q.SPEC `N` state_equiv_execution_equiv_valid_state_rel) >>
  `!s. eval_phis s (pre ++ t1) = eval_phis s pre /\
       phi_prefix_length (pre ++ t1) = phi_prefix_length pre /\
       eval_phis s (pre ++ t2) = eval_phis s pre /\
       phi_prefix_length (pre ++ t2) = phi_prefix_length pre`
    by metis_tac[eval_phis_append_non_phi] >>
  simp[run_block_def] >>
  qspecl_then [`s1`, `pre`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[]
  >- (drule_all eval_phis_agreement >> strip_tac >> simp[] >>
      `state_equiv N s' s2'` by metis_tac[eval_phis_preserves_R_ok] >>
      qspecl_then [`N`, `P`, `pre`, `t1`, `t2`, `bb1`, `bb2`, `fuel`, `ctx`]
        mp_tac exec_block_common_prefix >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then [`LENGTH pre - phi_prefix_length pre`,
        `s' with vs_inst_idx := phi_prefix_length pre`,
        `s2' with vs_inst_idx := phi_prefix_length pre`] mp_tac) >>
      simp[state_equiv_inst_idx, phi_prefix_length_le]) >>
  drule_all eval_phis_error_agreement >> strip_tac >> simp[lift_result_def]
QED

(* ===== The three accepted forms of a block ===== *)

Theorem run_block_unchanged[local]:
  (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
            x NOTIN N) /\
  state_equiv N s1 s2 ==>
  lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
    (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  strip_tac >>
  irule (Q.SPECL [`N`, `\i s. T`, `bb.bb_instructions`, `[]`, `[]`, `bb`, `bb`,
                  `fuel`, `ctx`, `s1`, `s2`] run_block_common_prefix) >>
  simp[] >> rpt strip_tac >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  gvs[get_instruction_def, lift_result_def, state_equiv_def] >>
  metis_tac[]
QED

(* Rewrite 1: jnz v a b ~> jnz x b a, where v = iszero x earlier. *)
Theorem run_block_iszero_operand[local]:
  !N pre t a b v x bb1 bb2 fuel ctx s1 s2.
  bb1.bb_instructions = pre ++ [t] /\
  bb2.bb_instructions = pre ++ [t with inst_operands := [x; Label b; Label a]] /\
  t.inst_opcode = JNZ /\ t.inst_operands = [Var v; Label a; Label b] /\
  bo_iszero_src v (REVERSE pre) = SOME x /\
  (!inst y. MEM inst (pre ++ [t]) /\ MEM (Var y) inst.inst_operands ==>
            y NOTIN N) /\
  state_equiv N s1 s2 ==>
  lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
    (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  rpt gen_tac >> strip_tac >> drule bo_iszero_src_REVERSE >> strip_tac >>
  map_every assume_tac
    [lookup_var_set_inst_idx, lookup_var_update_var_same,
     lookup_var_update_var_other, jump_to_set_inst_idx,
     GEN_ALL bool_to_word_neq_0w] >>
  `!y. x = Var y ==> y NOTIN N`
    by (rw[] >> first_x_assum irule >> qexists_tac `EL k pre` >>
        simp[EL_MEM]) >>
  `!inst y. MEM inst pre /\ MEM (Var y) inst.inst_operands ==> y NOTIN N`
    by metis_tac[MEM_APPEND] >>
  MATCH_MP_TAC (Q.SPECL [`N`,
    `\i s. k < i ==> ?xv. eval_operand x s = SOME xv /\
                          lookup_var v s = SOME (bool_to_word (xv = 0w))`,
    `pre`, `[t]`, `[t with inst_operands := [x; Label b; Label a]]`,
    `bb1`, `bb2`, `fuel`, `ctx`, `s1`, `s2`] run_block_common_prefix) >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (* the invariant is kept along the prefix *)
     (rpt gen_tac >> BETA_TAC >> strip_tac >> strip_tac >>
      Cases_on `i = k`
      >- (pop_assum SUBST_ALL_TAC >>
          `step_inst fuel ctx (EL k pre) s =
             case eval_operand x s of
               SOME w => OK (update_var v (bool_to_word (w = 0w)) s)
             | NONE => Error "undefined operand"`
            by (irule step_inst_iszero >> simp[]) >>
          gvs[AllCaseEqs()] >> qexists_tac `w` >>
          Cases_on `x` >> gvs[eval_operand_def]) >>
      `k < i` by simp[] >>
      qpat_x_assum `k < i ==> _` mp_tac >> simp[] >> strip_tac >>
      qpat_x_assum `!j. k < j /\ _ ==> _` (qspec_then `i` mp_tac) >>
      simp[] >> strip_tac >>
      `!y. ~MEM y (EL i pre).inst_outputs ==> lookup_var y s' = lookup_var y s`
        by metis_tac[step_preserves_non_output_vars] >>
      qexists_tac `xv` >>
      Cases_on `x` >> gvs[eval_operand_def, MEM_MAP])
  >- (* the two jnz agree on the label *)
     (qx_genl_tac [`u1`, `u2`] >> BETA_TAC >> strip_tac >>
      `k < LENGTH pre` by simp[] >> gvs[] >>
      `u2.vs_inst_idx = LENGTH pre` by fs[state_equiv_def] >>
      `eval_operand x u2 = SOME xv` by metis_tac[eval_operand_equiv] >>
      `!u. step_inst fuel ctx t u =
             case eval_operand (Var v) u of
               SOME w => OK (jump_to (if w <> 0w then a else b) u)
             | NONE => Error "undefined condition"`
        by (gen_tac >> irule step_inst_jnz >> simp[]) >>
      `!u. step_inst fuel ctx (t with inst_operands := [x; Label b; Label a]) u =
             case eval_operand x u of
               SOME w => OK (jump_to (if w <> 0w then b else a) u)
             | NONE => Error "undefined condition"`
        by (gen_tac >> irule step_inst_jnz >> simp[]) >>
      ONCE_REWRITE_TAC [exec_block_def] >>
      simp[get_instruction_def, EL_prefix_append,
           eval_operand_def, is_terminator_def] >>
      Cases_on `xv = 0w` >> simp[] >>
      irule terminator_ok_related >> irule jump_to_preserves >> simp[])
  >- (* the invariant holds at the end of the PHIs *)
     (BETA_TAC >> `phi_prefix_length pre <= k` suffices_by simp[] >>
      irule phi_prefix_length_non_phi >> simp[]) >>
  simp[]
QED

(* Rewrite 2: jnz c a b ~> tmp = iszero c; jnz tmp b a, with tmp in N. *)
Theorem run_block_insert_iszero[local]:
  !N pre t a b c iz tmp bb1 bb2 fuel ctx s1 s2.
  bb1.bb_instructions = pre ++ [t] /\
  bb2.bb_instructions =
    pre ++ [iz; t with inst_operands := [Var tmp; Label b; Label a]] /\
  t.inst_opcode = JNZ /\ t.inst_operands = [c; Label a; Label b] /\
  iz.inst_opcode = ISZERO /\ iz.inst_operands = [c] /\
  iz.inst_outputs = [tmp] /\ tmp IN N /\
  (!inst y. MEM inst (pre ++ [t]) /\ MEM (Var y) inst.inst_operands ==>
            y NOTIN N) /\
  state_equiv N s1 s2 ==>
  lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
    (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  map_every assume_tac
    [lookup_var_set_inst_idx, lookup_var_update_var_same,
     lookup_var_update_var_other, jump_to_set_inst_idx,
     GEN_ALL bool_to_word_neq_0w] >>
  `!inst y. MEM inst pre /\ MEM (Var y) inst.inst_operands ==> y NOTIN N`
    by metis_tac[MEM_APPEND] >>
  MATCH_MP_TAC (Q.SPECL [`N`, `\i s. T`, `pre`, `[t]`,
    `[iz; t with inst_operands := [Var tmp; Label b; Label a]]`,
    `bb1`, `bb2`, `fuel`, `ctx`, `s1`, `s2`] run_block_common_prefix) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`u1`, `u2`] >> strip_tac >>
  `u2.vs_inst_idx = LENGTH pre` by fs[state_equiv_def] >>
  `eval_operand c u2 = eval_operand c u1`
    by (irule (GSYM eval_operand_equiv) >> qexists_tac `N` >> rw[] >>
        qpat_x_assum `!inst y. MEM inst (pre ++ [t]) /\ _ ==> _` irule >>
        qexists_tac `t` >> simp[]) >>
  `!u. step_inst fuel ctx t u =
         case eval_operand c u of
           SOME w => OK (jump_to (if w <> 0w then a else b) u)
         | NONE => Error "undefined condition"`
    by (gen_tac >> irule step_inst_jnz >> simp[]) >>
  `!u. step_inst fuel ctx (t with inst_operands := [Var tmp; Label b; Label a]) u =
         case eval_operand (Var tmp) u of
           SOME w => OK (jump_to (if w <> 0w then b else a) u)
         | NONE => Error "undefined condition"`
    by (gen_tac >> irule step_inst_jnz >> simp[]) >>
  `!u. step_inst fuel ctx iz u =
         case eval_operand c u of
           SOME w => OK (update_var tmp (bool_to_word (w = 0w)) u)
         | NONE => Error "undefined operand"`
    by (gen_tac >> irule step_inst_iszero >> simp[]) >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  simp[get_instruction_def, EL_prefix_append, is_terminator_def] >>
  Cases_on `eval_operand c u1` >> simp[lift_result_def] >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  simp[get_instruction_def, EL_prefix_append,
       eval_operand_def, is_terminator_def] >>
  rename1 `eval_operand c u1 = SOME w` >>
  Cases_on `w = 0w` >> simp[] >>
  irule terminator_ok_related >> irule jump_to_preserves >>
  irule state_equiv_update_right >> simp[]
QED

(* ===== One checked block ===== *)

Theorem REVERSE_EQ_CONS[local]:
  REVERSE l = h::t <=> l = REVERSE t ++ [h]
Proof
  metis_tac[REVERSE_REVERSE, REVERSE_DEF]
QED

Theorem check_branch_opt_block_label[local]:
  check_branch_opt_block vars bb bb' ==> bb'.bb_label = bb.bb_label
Proof
  rw[check_branch_opt_block_def] >> simp[]
QED

(* What an accepted block pair looks like. *)
Theorem check_branch_opt_block_cases[local]:
  check_branch_opt_block vars bb bb' ==>
  bb' = bb \/
  (?pre t a b v x.
     bb.bb_instructions = pre ++ [t] /\
     bb'.bb_instructions = pre ++ [t with inst_operands := [x; Label b; Label a]] /\
     t.inst_opcode = JNZ /\ t.inst_operands = [Var v; Label a; Label b] /\
     bo_iszero_src v (REVERSE pre) = SOME x) \/
  (?pre t a b c iz tmp.
     bb.bb_instructions = pre ++ [t] /\
     bb'.bb_instructions =
       pre ++ [iz; t with inst_operands := [Var tmp; Label b; Label a]] /\
     t.inst_opcode = JNZ /\ t.inst_operands = [c; Label a; Label b] /\
     iz.inst_opcode = ISZERO /\ iz.inst_operands = [c] /\
     iz.inst_outputs = [tmp] /\ ~MEM tmp vars)
Proof
  rw[check_branch_opt_block_def] >> simp[] >>
  gvs[TypeBase.AllCasePreds(), REVERSE_EQ_CONS] >>
  metis_tac[REVERSE_REVERSE]
QED

Theorem check_branch_opt_block_sound[local]:
  check_branch_opt_block vars bb bb' /\
  (!x. MEM x (block_ir_vars bb) ==> x NOTIN N) /\
  (!x. MEM x (block_ir_vars bb') /\ ~MEM x vars ==> x IN N) /\
  state_equiv N s1 s2 ==>
  lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
    (run_block fuel ctx bb s1) (run_block fuel ctx bb' s2)
Proof
  strip_tac >>
  `!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
            x NOTIN N`
    by (rpt strip_tac >>
        `MEM x (block_ir_vars bb)` suffices_by metis_tac[] >>
        simp[block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS,
             inst_ir_vars_def] >>
        metis_tac[operand_var_in_inst_uses]) >>
  drule check_branch_opt_block_cases >> strip_tac
  >- (gvs[] >> irule run_block_unchanged >> metis_tac[])
  >- (MATCH_MP_TAC (Q.SPECL [`N`, `pre`, `t`, `a`, `b`, `v`, `x`, `bb`, `bb'`,
                             `fuel`, `ctx`, `s1`, `s2`] run_block_iszero_operand) >>
      simp[] >>
      qpat_x_assum `bb.bb_instructions = _` (fn th => fs[th]) >>
      metis_tac[]) >>
  `tmp IN N`
    by (first_x_assum irule >>
        simp[block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS,
             inst_ir_vars_def]) >>
  MATCH_MP_TAC (Q.SPECL [`N`, `pre`, `t`, `a`, `b`, `c`, `iz`, `tmp`, `bb`, `bb'`,
                         `fuel`, `ctx`, `s1`, `s2`] run_block_insert_iszero) >>
  simp[] >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => fs[th]) >>
  metis_tac[]
QED

(* ===== The function ===== *)

Theorem lookup_block_LIST_REL[local]:
  !bs bs' R l. LIST_REL R bs bs' /\
    (!bb bb'. R bb bb' ==> bb'.bb_label = bb.bb_label) ==>
    (lookup_block l bs' = NONE <=> lookup_block l bs = NONE) /\
    !bb. lookup_block l bs = SOME bb ==>
      ?bb'. lookup_block l bs' = SOME bb' /\ R bb bb' /\
            MEM bb bs /\ MEM bb' bs'
Proof
  Induct >> rpt gen_tac >> Cases_on `bs'` >>
  simp[lookup_block_def, FIND_thm] >> strip_tac >>
  first_x_assum (qspecl_then [`t`, `R`, `l`] mp_tac) >>
  simp[lookup_block_def] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem check_branch_opt_fn_blocks[local]:
  check_branch_opt_fn fn fn' ==>
  LIST_REL (check_branch_opt_block (fn_ir_vars fn)) fn.fn_blocks fn'.fn_blocks
Proof
  metis_tac[check_branch_opt_fn_def]
QED

Theorem check_branch_opt_fn_run_blocks:
  !fuel fn fn' ctx s1 s2.
    check_branch_opt_fn fn fn' /\
    state_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)) s1 s2 ==>
    lift_result
      (state_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)))
      (execution_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)))
      (execution_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)))
      (run_blocks fuel ctx fn s1) (run_blocks fuel ctx fn' s2)
Proof
  Induct
  >- (ONCE_REWRITE_TAC [run_blocks_def] >> simp[lift_result_def]) >>
  rpt strip_tac >> simp[run_blocks_unfold] >>
  qabbrev_tac `N = set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)` >>
  `s2.vs_current_bb = s1.vs_current_bb` by fs[state_equiv_def] >>
  drule check_branch_opt_fn_blocks >> strip_tac >>
  qspecl_then [`fn.fn_blocks`, `fn'.fn_blocks`,
    `check_branch_opt_block (fn_ir_vars fn)`, `s1.vs_current_bb`]
    mp_tac lookup_block_LIST_REL >>
  impl_tac >- metis_tac[check_branch_opt_block_label] >>
  strip_tac >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >>
  gvs[lift_result_def] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  `lift_result (state_equiv N) (execution_equiv N) (execution_equiv N)
     (run_block fuel ctx x s1) (run_block fuel ctx bb' s2)`
    by (drule_then irule check_branch_opt_block_sound >> simp[] >>
        fs[Abbr `N`, fn_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        metis_tac[]) >>
  Cases_on `run_block fuel ctx x s1` >>
  Cases_on `run_block fuel ctx bb' s2` >> gvs[lift_result_def] >>
  imp_res_tac state_equiv_halted >>
  rw[lift_result_def, state_equiv_implies_execution_equiv] >>
  first_x_assum irule >> simp[]
QED

Theorem check_branch_opt_fn_run_function:
  !fn fn' s fuel ctx.
    check_branch_opt_fn fn fn' ==>
    lift_result
      (state_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)))
      (execution_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)))
      (execution_equiv (set (fn_ir_vars fn') DIFF set (fn_ir_vars fn)))
      (run_function fuel ctx fn s) (run_function fuel ctx fn' s)
Proof
  rpt strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn`
    by (drule check_branch_opt_fn_blocks >>
        simp[fn_entry_label_def, entry_block_def] >>
        Cases_on `fn.fn_blocks` >> rw[] >> gvs[] >>
        metis_tac[check_branch_opt_block_label]) >>
  simp[run_function_def] >> CASE_TAC >> simp[lift_result_def] >>
  irule check_branch_opt_fn_run_blocks >> simp[state_equiv_refl]
QED
