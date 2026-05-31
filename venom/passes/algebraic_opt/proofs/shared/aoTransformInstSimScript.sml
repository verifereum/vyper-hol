(*
 * Algebraic Optimization — per-instruction transform simulation.
 *
 * Composes resolve + producer + peephole simulations into a single
 * per-instruction lift_result simulation (ao_transform_inst_sim_inst).
 * Transform-only facts: no chain invariants. The loop-robust per-block
 * sim supplies H_resolve / H_range / H_fresh.
 *
 * TOP-LEVEL: ao_transform_inst_sim_inst
 *)
Theory aoTransformInstSim
Ancestors
  algebraicOptDefs aoPeepholeSim aoResolveSim aoWf
  passSimulationProps passSimulationDefs
  venomExecSemantics venomExecProofs venomState venomInst venomWf
  stateEquiv stateEquivProps execEquivProps
Libs
  fcpLib

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


(* Per-instruction sim with per-instruction H_fresh.
   Unlike ao_transform_inst_sim, only needs fresh vars for THIS inst. *)
Theorem ao_transform_inst_sim_inst:
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

val _ = export_theory();
