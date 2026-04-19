Theory mem2varCorrectness
Ancestors
  mem2varProofs mem2varBlockSim
  mem2varDefs mem2varBlockSimHelpers
  passSimulationDefs passSimulationProps
  stateEquiv
  venomExecSemantics venomState venomWf
  venomMemDefs venomExecProofs venomInst
  pointerConfinedDefs memLocDefs
  finite_map list pred_set rich_list
  While

(* run_blocks ignores vs_inst_idx: it resets to 0 before each block *)
Theorem run_blocks_inst_idx_irrel[local]:
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

(* lift_result weakening: R1 ==> R2 everywhere *)
Theorem lift_result_weaken[local]:
  !R1 R2 r1 r2.
    (!s1 s2. R1 s1 s2 ==> R2 s1 s2) /\
    lift_result R1 R2 R2 r1 r2 ==>
    lift_result R2 R2 R2 r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def]
QED

(* pvars_set for the current block — derivable from state alone *)
Definition m2v_pvars_at_current_def:
  m2v_pvars_at_current fn s <=>
    !bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb ==>
      m2v_pvars_set fn bb 0 s
End

(* No block other than entry dominates entry.
   Proof: the singleton path [entry] is a valid fn_path from entry to entry,
   and MEM d [entry] forces d = entry, contradicting d <> entry. *)
Theorem no_strict_dominator_of_entry[local]:
  !fn d entry.
    fn_entry_label fn = SOME entry /\
    fn_dominates fn d entry /\ d <> entry ==> F
Proof
  rpt strip_tac >>
  fs[fn_dominates_def] >>
  first_x_assum (qspec_then `[entry]` mp_tac) >>
  simp[is_fn_path_def] >>
  (impl_tac >- (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL])) >>
  simp[]
QED

(* At the entry block, pvars_set cross-block clause is vacuously true *)
Theorem m2v_pvars_at_current_entry[local]:
  !fn s.
    wf_function fn /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    m2v_pvars_at_current fn s
Proof
  rw[m2v_pvars_at_current_def, m2v_pvars_set_def] >>
  `store_bb.bb_label <> bb.bb_label` by
    (strip_tac >>
     `store_bb = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
     gvs[]) >>
  metis_tac[no_strict_dominator_of_entry]
QED

(* ===== Helpers for m2v_pvars_at_current preservation ===== *)

(* Transformed block is non-empty *)
Theorem m2v_bt_nonempty[local]:
  !fn bb. bb.bb_instructions <> [] ==>
    (m2v_bt fn bb).bb_instructions <> []
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  gvs[m2v_bt_instructions, FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
  first_x_assum (qspec_then `LAST bb.bb_instructions` mp_tac) >>
  simp[MEM_LAST_NOT_NIL] >>
  metis_tac[m2v_rewrite_inst_len_ge1,
            DECIDE ``1n <= n ==> n <> 0``, LENGTH_NIL]
QED

(* m2v_rewrite_inst preserves terminators as LAST element *)
Theorem m2v_rewrite_inst_last_term[local]:
  !fn i. is_terminator i.inst_opcode ==>
    LAST (m2v_rewrite_inst fn i) = i
Proof
  rpt strip_tac >> simp[m2v_rewrite_inst_def] >>
  CASE_TAC >> simp[] >>
  PairCases_on `x` >> simp[m2v_promote_inst_def] >>
  Cases_on `i.inst_opcode` >> gvs[is_terminator_def] >>
  rpt (CASE_TAC >> gvs[])
QED

(* LAST of transformed block = LAST of original (for well-formed blocks) *)
Theorem m2v_bt_last[local]:
  !fn bb. bb_well_formed bb ==>
    LAST (m2v_bt fn bb).bb_instructions = LAST bb.bb_instructions
Proof
  rpt strip_tac >> gvs[bb_well_formed_def] >>
  simp[m2v_bt_instructions] >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  `insts = FRONT insts ++ [LAST insts]`
    by metis_tac[APPEND_FRONT_LAST] >>
  qabbrev_tac `t = LAST insts` >>
  `m2v_rewrite_inst fn t <> []` by
    metis_tac[m2v_rewrite_inst_len_ge1,
              DECIDE ``1n <= n ==> n <> 0``, LENGTH_NIL] >>
  once_asm_rewrite_tac[] >>
  simp[MAP_APPEND, FLAT_APPEND, LAST_APPEND_NOT_NIL] >>
  irule m2v_rewrite_inst_last_term >> simp[Abbr `t`]
QED

(* bb_succs preserved by m2v_bt *)
Theorem m2v_bt_succs[local]:
  !fn bb. bb_well_formed bb ==>
    bb_succs (m2v_bt fn bb) = bb_succs bb
Proof
  rpt strip_tac >> simp[bb_succs_def] >>
  `(m2v_bt fn bb).bb_instructions <> []`
    by (irule m2v_bt_nonempty >> gvs[bb_well_formed_def]) >>
  `LAST (m2v_bt fn bb).bb_instructions = LAST bb.bb_instructions`
    by (irule m2v_bt_last >> simp[]) >>
  gvs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `(m2v_bt fn bb).bb_instructions` >> gvs[]
QED

(* m2v_promote_inst preserves inst_wf *)
Theorem m2v_promote_inst_inst_wf[local]:
  !pvar ao sz i.
    inst_wf i ==> EVERY inst_wf (m2v_promote_inst pvar ao sz i)
Proof
  rpt strip_tac >> simp[m2v_promote_inst_def] >>
  rpt (CASE_TAC >> gvs[inst_wf_def])
QED

(* EVERY inst_wf preserved by m2v_bt *)
Theorem m2v_bt_inst_wf[local]:
  !fn bb. EVERY inst_wf bb.bb_instructions ==>
    EVERY inst_wf (m2v_bt fn bb).bb_instructions
Proof
  rpt strip_tac >>
  simp[m2v_bt_instructions, EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM ri (m2v_rewrite_inst fn inst)` >>
  `inst_wf inst` by metis_tac[EVERY_MEM] >>
  qpat_x_assum `MEM ri _` mp_tac >>
  simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)` >>
  simp[] >> strip_tac >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  drule m2v_promote_inst_inst_wf >> simp[EVERY_MEM] >>
  metis_tac[]
QED

(* All non-last elements of m2v_rewrite_inst are non-terminators *)
Theorem m2v_rewrite_inst_front_nonterm[local]:
  !fn inst j. j < LENGTH (m2v_rewrite_inst fn inst) - 1 ==>
    ~is_terminator (EL j (m2v_rewrite_inst fn inst)).inst_opcode
Proof
  rpt gen_tac >> simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)` >> simp[] >>
  PairCases_on `x` >> simp[m2v_promote_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  rpt (CASE_TAC >> simp[is_terminator_def])
QED

(* m2v_rewrite_inst on non-terminal gives non-terminal singleton *)
Theorem m2v_rewrite_nonterm_opcode[local]:
  !fn inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (HD (m2v_rewrite_inst fn inst)).inst_opcode
Proof
  rpt gen_tac >> simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)` >> simp[] >>
  PairCases_on `x` >> simp[m2v_promote_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  rpt (CASE_TAC >> simp[is_terminator_def])
QED

(* Length of FLAT MAP when FRONT maps to singletons *)
Theorem flat_map_front_sing_length[local]:
  !f xs. xs <> [] /\ EVERY (\x. LENGTH (f x) = 1) (FRONT xs) ==>
    LENGTH (FLAT (MAP f xs)) = LENGTH xs - 1 + LENGTH (f (LAST xs))
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  Cases_on `xs` >> gvs[FRONT_DEF]
QED

(* Helper: FRONT of well-formed block instructions are all non-terminators *)
Theorem wf_front_nonterm[local]:
  !bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions - 1 ==>
    ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rw[bb_well_formed_def] >>
  spose_not_then assume_tac >>
  `i = PRE (LENGTH bb.bb_instructions)` by
    (first_x_assum irule >> simp[]) >>
  gvs[]
QED

(* FRONT rewrites are singletons — proved via EL-based bb_well_formed *)
Theorem m2v_front_sing[local]:
  !fn bb. bb_well_formed bb ==>
    EVERY (\ri. LENGTH (m2v_rewrite_inst fn ri) = 1) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  simp[EVERY_EL, LENGTH_FRONT] >> rpt strip_tac >>
  rename1 `k < _` >>
  irule m2v_rewrite_inst_len1_nonterm >>
  `EL k (FRONT bb.bb_instructions) = EL k bb.bb_instructions` by
    (irule EL_FRONT >> simp[NULL_EQ, LENGTH_FRONT]) >>
  simp[] >> irule wf_front_nonterm >> gvs[arithmeticTheory.PRE_SUB1]
QED

(* Front of transformed block is non-terminal *)
Theorem m2v_bt_front_nonterm[local]:
  !fn bb. bb_well_formed bb ==>
    !i. i < LENGTH (m2v_bt fn bb).bb_instructions - 1 ==>
      ~is_terminator (EL i (m2v_bt fn bb).bb_instructions).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  mp_tac (Q.SPECL [`fn`, `bb`] m2v_front_sing) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `i < _` >>
  Cases_on `i < LENGTH bb.bb_instructions - 1`
  >- (drule_all FLAT_MAP_FRONT_SING_EL >>
      simp[m2v_bt_instructions] >> strip_tac >>
      drule wf_front_nonterm >> disch_then drule >> strip_tac >>
      metis_tac[m2v_rewrite_nonterm_opcode])
  >> `LENGTH bb.bb_instructions - 1 <= i` by decide_tac
  >> qabbrev_tac `j = i - (LENGTH bb.bb_instructions - 1)`
  >> `i = (LENGTH bb.bb_instructions - 1) + j` by simp[Abbr `j`]
  >> `j < LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions)) - 1` by
       (`LENGTH (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions)) =
          LENGTH bb.bb_instructions - 1 +
          LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions))`
          by (irule flat_map_front_sing_length >> simp[]) >>
        gvs[m2v_bt_instructions])
  >> `EL (LENGTH bb.bb_instructions - 1 + j)
        (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions)) =
      EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions))` by
       (irule FLAT_MAP_FRONT_SING_LAST_EL >> simp[])
  >> `EL i (m2v_bt fn bb).bb_instructions =
      EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions))` by
       gvs[m2v_bt_instructions]
  >> pop_assum SUBST1_TAC
  >> irule m2v_rewrite_inst_front_nonterm >> simp[]
QED

(* m2v_promote_inst never introduces PHI opcodes *)
Theorem m2v_promote_inst_preserves_phi[local]:
  !pvar ao sz inst x. MEM x (m2v_promote_inst pvar ao sz inst) ==>
    x.inst_opcode = PHI ==> inst.inst_opcode = PHI
Proof
  rpt gen_tac >> simp[Once m2v_promote_inst_def] >>
  rpt (CASE_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

(* m2v_rewrite_inst never introduces PHI opcodes *)
Theorem m2v_rewrite_inst_preserves_phi[local]:
  !fn inst x. MEM x (m2v_rewrite_inst fn inst) ==>
    x.inst_opcode = PHI ==> inst.inst_opcode = PHI
Proof
  rpt gen_tac >> simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `x'` >> gvs[] >>
  metis_tac[m2v_promote_inst_preserves_phi]
QED

(* If EL q of transformed block is PHI, q must be in original front range.
   Key idea: last instruction is a terminator ≠ PHI, and m2v_rewrite never
   introduces PHI, so PHI elements can only come from front instructions. *)
Theorem m2v_bt_phi_in_front[local]:
  !fn bb q. bb_well_formed bb /\
    q < LENGTH (m2v_bt fn bb).bb_instructions /\
    (EL q (m2v_bt fn bb).bb_instructions).inst_opcode = PHI /\
    EVERY (\ri. LENGTH (m2v_rewrite_inst fn ri) = 1) (FRONT bb.bb_instructions) ==>
    q < LENGTH bb.bb_instructions - 1
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  `q >= LENGTH bb.bb_instructions - 1` by decide_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode`
    by gvs[bb_well_formed_def] >>
  (* Rewrite transformed block to FLAT form *)
  qabbrev_tac `j = q - (LENGTH bb.bb_instructions - 1)` >>
  `q = (LENGTH bb.bb_instructions - 1) + j` by simp[Abbr `j`] >>
  `j < LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions))` by
    (`LENGTH (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions)) =
       LENGTH bb.bb_instructions - 1 +
       LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions))`
       by (irule flat_map_front_sing_length >> simp[]) >>
     gvs[m2v_bt_instructions]) >>
  `EL (LENGTH bb.bb_instructions - 1 + j)
      (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions)) =
   EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions))` by
    (irule FLAT_MAP_FRONT_SING_LAST_EL >> simp[]) >>
  `EL q (m2v_bt fn bb).bb_instructions =
   EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions))` by
    gvs[m2v_bt_instructions] >>
  (* EL q is PHI, so EL j of rewrite is PHI, so original LAST was PHI *)
  `MEM (EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions)))
       (m2v_rewrite_inst fn (LAST bb.bb_instructions))` by
    (simp[MEM_EL] >> qexists `j` >> simp[]) >>
  `(LAST bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[m2v_rewrite_inst_preserves_phi] >>
  gvs[is_terminator_def]
QED

(* PHI instructions pass through m2v_rewrite_inst unchanged *)
Theorem m2v_rewrite_inst_phi[local]:
  !fn inst. inst.inst_opcode = PHI ==>
    m2v_rewrite_inst fn inst = [inst]
Proof
  rpt strip_tac >> simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)` >> simp[] >>
  PairCases_on `x` >> simp[Once m2v_promote_inst_def]
QED

(* For front-range indices, transformed EL = original EL (for 1-to-1 front) *)
Theorem m2v_bt_front_el[local]:
  !fn bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions - 1 ==>
    EL i (m2v_bt fn bb).bb_instructions =
    HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  simp[m2v_bt_instructions] >>
  irule FLAT_MAP_FRONT_SING_EL >> simp[] >>
  irule m2v_front_sing >> simp[]
QED

(* PHI in transformed front-range element ↔ PHI in original element *)
Theorem m2v_bt_front_el_phi[local]:
  !fn bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions - 1 ==>
    ((EL i (m2v_bt fn bb).bb_instructions).inst_opcode = PHI <=>
     (EL i bb.bb_instructions).inst_opcode = PHI)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- ((* backward: transformed PHI → original PHI *)
      `EL i (m2v_bt fn bb).bb_instructions =
       HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))` by
        (irule m2v_bt_front_el >> simp[]) >>
      `~is_terminator (EL i bb.bb_instructions).inst_opcode` by
        (irule wf_front_nonterm >> simp[]) >>
      `m2v_rewrite_inst fn (EL i bb.bb_instructions) =
       [HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))]` by
        (mp_tac (Q.SPECL [`fn`, `EL i bb.bb_instructions`]
                   m2v_rewrite_inst_len1_nonterm) >> simp[] >>
         Cases_on `m2v_rewrite_inst fn (EL i bb.bb_instructions)` >> simp[] >>
         Cases_on `t` >> simp[]) >>
      metis_tac[m2v_rewrite_inst_preserves_phi, MEM])
  >> ((* forward: original PHI → transformed PHI *)
      `EL i (m2v_bt fn bb).bb_instructions =
       HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))` by
        (irule m2v_bt_front_el >> simp[]) >>
      gvs[m2v_rewrite_inst_phi])
QED

(* m2v_bt preserves bb_well_formed *)
Theorem m2v_bt_well_formed[local]:
  !fn bb. bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions ==>
    bb_well_formed (m2v_bt fn bb)
Proof
  rpt strip_tac >> simp[bb_well_formed_def] >> rpt conj_tac
  >- (irule m2v_bt_nonempty >> gvs[bb_well_formed_def])
  >- (drule m2v_bt_last >> simp[] >> gvs[bb_well_formed_def])
  >- ((* Only-last-is-terminator: contrapositive of m2v_bt_front_nonterm *)
      rpt strip_tac >>
      drule m2v_bt_front_nonterm >> strip_tac >>
      spose_not_then assume_tac >>
      `i < LENGTH (m2v_bt fn bb).bb_instructions - 1` by decide_tac >>
      metis_tac[])
  >> ((* PHI-first: use m2v_bt_front_el_phi to transfer between original/transformed *)
      qx_gen_tac `p` >> qx_gen_tac `q` >> strip_tac >>
      (* Both p, q in front range of original *)
      `EVERY (\ri. LENGTH (m2v_rewrite_inst fn ri) = 1)
             (FRONT bb.bb_instructions)` by
        (irule m2v_front_sing >> simp[]) >>
      `q < LENGTH bb.bb_instructions - 1` by
        (drule_all m2v_bt_phi_in_front >> simp[]) >>
      `p < LENGTH bb.bb_instructions - 1` by decide_tac >>
      (* q is PHI in original (backward via m2v_bt_front_el_phi) *)
      `(EL q bb.bb_instructions).inst_opcode = PHI` by
        metis_tac[m2v_bt_front_el_phi] >>
      (* p is PHI in original (bb_well_formed PHI-first) *)
      `(EL p bb.bb_instructions).inst_opcode = PHI` by
        (qpat_x_assum `bb_well_formed _`
           (strip_assume_tac o REWRITE_RULE[bb_well_formed_def]) >>
         first_x_assum (qspecl_then [`p`,`q`] mp_tac) >> simp[]) >>
      (* p is PHI in transformed (forward via m2v_bt_front_el_phi) *)
      metis_tac[m2v_bt_front_el_phi])
QED

(* Helper: any non-terminal instruction's output is defined after exec_block.
   Requires front-nonterm condition so we know terminators only occur at end. *)
Theorem exec_block_nonterm_output_defined[local]:
  !n fuel ctx bb s s' k v.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    exec_block fuel ctx bb s = OK s' /\
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions - 1 /\
    MEM v (EL k bb.bb_instructions).inst_outputs ==>
    IS_SOME (lookup_var v s')
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  simp[] >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >>
  rename1 `step_inst _ _ _ _ = OK s1` >>
  `~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by
    (`s.vs_inst_idx < LENGTH bb.bb_instructions - 1` by decide_tac >>
     metis_tac[]) >>
  simp[] >> strip_tac >>
  (* Now: exec_block from SUC idx on s1 = OK s' *)
  Cases_on `s.vs_inst_idx = k`
  >- ((* k = idx: v in outputs of inst k, step_inst adds to FDOM,
        exec_block_lookup_mono preserves to s'. *)
      irule exec_block_lookup_mono >>
      qexistsl [`bb`,`ctx`,`fuel`,
        `s1 with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[] >>
      (* IS_SOME (lookup_var v s1): v in FDOM via step_inst_fdom *)
      `inst_wf (EL k bb.bb_instructions)` by metis_tac[EVERY_EL] >>
      `FDOM s1.vs_vars = FDOM s.vs_vars UNION
         set (EL k bb.bb_instructions).inst_outputs` by
        metis_tac[step_inst_fdom] >>
      simp[lookup_var_def, FLOOKUP_DEF])
  >> ((* k > idx: use IH *)
      qpat_x_assum `!m. m < n ==> _` (qspec_then
        `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      (impl_tac >- decide_tac) >>
      disch_then (qspecl_then [`fuel`,`ctx`,`bb`,
        `s1 with vs_inst_idx := SUC s.vs_inst_idx`,
        `s'`,`k`,`v`] mp_tac) >>
      simp[])
QED

(* exec_block_output_defined: any output variable of any instruction
   in a block is defined after successful execution *)
Theorem exec_block_output_defined[local]:
  !fuel ctx bb s s' v.
    exec_block fuel ctx bb s = OK s' /\ s.vs_inst_idx = 0 /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM inst bb.bb_instructions` >>
  qpat_x_assum `MEM inst _`
    (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
  rename1 `n < LENGTH bb.bb_instructions` >> gvs[] >>
  Cases_on `n < LENGTH bb.bb_instructions - 1`
  >- (irule exec_block_nonterm_output_defined >>
      qexistsl [`bb`,`ctx`,`fuel`,`n`,
        `LENGTH bb.bb_instructions`,`s`] >> simp[] >>
      metis_tac[wf_front_nonterm])
  >> `bb.bb_instructions <> []` by gvs[bb_well_formed_def]
  >> `n = LENGTH bb.bb_instructions - 1` by decide_tac
  >> `inst_wf (EL n bb.bb_instructions)` by metis_tac[EVERY_EL]
  >> `is_terminator (EL n bb.bb_instructions).inst_opcode` by
       (gvs[bb_well_formed_def, LAST_EL, arithmeticTheory.PRE_SUB1])
  >> drule_all terminator_no_outputs >> strip_tac >> gvs[]
QED

(* pointer_use_vars preserves initial variables *)
Theorem pointer_use_vars_initial[local]:
  !fn vars x. MEM x vars ==> MEM x (pointer_use_vars fn vars)
Proof
  rpt strip_tac >>
  simp[pointer_use_vars_def] >>
  qmatch_goalsub_abbrev_tac `OWHILE ISL f (INL vars)` >>
  Cases_on `OWHILE ISL f (INL vars)` >> simp[] >>
  rename1 `SOME result` >>
  Cases_on `result` >> simp[] >>
  rename1 `SOME (INR final)` >>
  mp_tac (OWHILE_INV_IND
    |> INST_TYPE [alpha |-> ``:string list + string list``]
    |> Q.INST [`P` |-> `\v. case v of INL l => MEM x l | INR l => MEM x l`]
    |> Q.SPECL [`ISL`, `f`, `INL vars`]) >>
  simp[] >> disch_then irule >>
  rpt strip_tac >> Cases_on `x'` >> gvs[Abbr `f`] >>
  gvs[pointer_use_step_step_def, LET_THM] >>
  CASE_TAC >> gvs[]
QED

(* alloca_roots is finite *)
Theorem alloca_roots_finite[local]:
  !fn. FINITE (alloca_roots fn)
Proof
  rpt strip_tac >> simp[alloca_roots_def] >>
  irule SUBSET_FINITE >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  conj_tac >- simp[FINITE_LIST_TO_SET] >>
  simp[SUBSET_DEF, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> qexists `inst` >> simp[] >>
  Cases_on `inst.inst_outputs` >> gvs[inst_output_def] >>
  Cases_on `t` >> gvs[inst_output_def]
QED

(* promo_list ao is in pointer_derived_vars *)
Theorem m2v_promo_list_ao_in_derived[local]:
  !fn ao pvar sz.
    MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
    ao IN pointer_derived_vars fn (alloca_roots fn)
Proof
  rpt strip_tac >>
  drule m2v_promo_list_is_alloca >> strip_tac >>
  simp[pointer_derived_vars_def] >>
  irule pointer_use_vars_initial >>
  simp[MEM_SET_TO_LIST, alloca_roots_finite, alloca_roots_def] >>
  qexists `inst` >> simp[inst_output_def]
QED

(* FIND returns the unique matching entry when predicate matches exactly one *)
Theorem FIND_unique_pred[local]:
  !P l x.
    MEM x l /\ P x /\
    (!y. MEM y l /\ P y ==> y = x) ==>
    FIND P l = SOME x
Proof
  Induct_on `l` >> simp[FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `x = h` >> gvs[] >>
  Cases_on `P h` >> gvs[FIND_thm]
QED

(* pointer_confined forces promo vars into MSTORE offset position *)
Theorem pointer_confined_mstore_offset[local]:
  !fn bb inst v.
    alloca_pointer_confined fn /\
    inst_wf inst /\ inst.inst_opcode = MSTORE /\
    MEM inst bb.bb_instructions /\ MEM bb fn.fn_blocks /\
    MEM (Var v) inst.inst_operands /\
    v IN pointer_derived_vars fn (alloca_roots fn) ==>
    Var v = HD inst.inst_operands
Proof
  rpt strip_tac >>
  gvs[alloca_pointer_confined_def, pointer_confined_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[] >> strip_tac
  >- (gvs[mem_write_ops_def, is_immutable_op_def, inst_wf_def] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[])
  >- gvs[mem_read_ops_def, is_immutable_op_def]
  >- gvs[is_pointer_preserving_op_def]
QED

(* FIND on promo_list returns the unique matching entry when only one
   alloca pointer appears in the operands *)
Theorem m2v_find_unique_match[local]:
  !fn inst ao pvar sz bb.
    ssa_form fn /\ alloca_pointer_confined fn /\
    inst_wf inst /\ inst.inst_opcode = MSTORE /\
    MEM inst bb.bb_instructions /\ MEM bb fn.fn_blocks /\
    MEM (Var ao) inst.inst_operands /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
    FIND (\(ao',_0,_1). MEM (Var ao') inst.inst_operands)
         (m2v_promo_list fn) = SOME (ao, pvar, sz)
Proof
  rpt strip_tac >>
  irule FIND_unique_pred >> simp[] >>
  rpt strip_tac >>
  PairCases_on `y` >> gvs[] >> rename1 `MEM (ao', pvar', sz') _` >>
  `ao' IN pointer_derived_vars fn (alloca_roots fn)` by
    (irule m2v_promo_list_ao_in_derived >> metis_tac[]) >>
  `ao IN pointer_derived_vars fn (alloca_roots fn)` by
    (irule m2v_promo_list_ao_in_derived >> metis_tac[]) >>
  mp_tac (Q.SPECL [`fn`, `bb`, `inst`, `ao'`] pointer_confined_mstore_offset) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`fn`, `bb`, `inst`, `ao`] pointer_confined_mstore_offset) >>
  simp[] >> strip_tac >>
  `Var ao' = Var ao` by metis_tac[] >>
  gvs[] >> metis_tac[m2v_promo_list_ao_unique]
QED

(* m2v_promote_inst on MSTORE with matching offset and sz=32 *)
Theorem m2v_promote_inst_mstore[local]:
  !pvar ao val_op inst.
    inst.inst_opcode = MSTORE /\
    inst.inst_operands = [Var ao; val_op] ==>
    m2v_promote_inst pvar ao 32 inst =
      [inst with <|inst_opcode := ASSIGN;
                   inst_operands := [val_op];
                   inst_outputs := [pvar]|>]
Proof
  rpt strip_tac >> simp[Once m2v_promote_inst_def]
QED

(* When bb has MSTORE to a promoted alloca ao, the transformed block
   has pvar in some instruction's outputs *)
Theorem m2v_bt_has_pvar_output[local]:
  !fn bb store_inst ao pvar sz.
    ssa_form fn /\ alloca_pointer_confined fn /\
    inst_wf store_inst /\
    MEM bb fn.fn_blocks /\
    MEM store_inst bb.bb_instructions /\
    store_inst.inst_opcode = MSTORE /\
    MEM (Var ao) store_inst.inst_operands /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\ sz = 32 ==>
    MEM pvar (FLAT (MAP (\i. i.inst_outputs) (m2v_bt fn bb).bb_instructions))
Proof
  rpt strip_tac
  >> `FIND (\(ao',_0,_1). MEM (Var ao') store_inst.inst_operands)
        (m2v_promo_list fn) = SOME (ao, pvar, 32)` by
    (irule m2v_find_unique_match >> metis_tac[])
  >> `ao IN pointer_derived_vars fn (alloca_roots fn)` by
    (irule m2v_promo_list_ao_in_derived >> metis_tac[])
  >> mp_tac (Q.SPECL [`fn`, `bb`, `store_inst`, `ao`]
       pointer_confined_mstore_offset) >> simp[] >> strip_tac
  >> `?val_op. store_inst.inst_operands = [Var ao; val_op]` by
       (qpat_x_assum `inst_wf _` mp_tac >> simp[Once inst_wf_def] >>
        Cases_on `store_inst.inst_operands` >> gvs[] >>
        Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[])
  >> simp[m2v_bt_instructions, MEM_FLAT, MEM_MAP]
  >> qexists `[pvar]` >> simp[]
  >> qexists `store_inst with
       <|inst_opcode := ASSIGN;
         inst_operands := [val_op]; inst_outputs := [pvar]|>`
  >> simp[]
  >> qexists `m2v_rewrite_inst fn store_inst`
  >> conj_tac
  >- (qexists `store_inst` >> simp[m2v_rewrite_inst_def])
  >> drule_all m2v_promote_inst_mstore >> simp[m2v_rewrite_inst_def]
QED

(* Successful execution of a well-formed block lands in a successor *)
Theorem bb_wf_in_succs[local]:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  s.vs_inst_idx = 0 /\ exec_block fuel ctx bb s = OK s' ==>
  MEM s'.vs_current_bb (bb_succs bb)
Proof
  strip_tac >>
  drule_at (Pos last) exec_block_current_bb_in_succs >> simp[] >>
  qpat_x_assum `bb_well_formed _`
    (strip_assume_tac o REWRITE_RULE[bb_well_formed_def]) >>
  disch_then irule >> simp[] >>
  rpt strip_tac >>
  `i = PRE (LENGTH bb.bb_instructions)` by
    (first_x_assum irule >> simp[]) >>
  gvs[]
QED

(* m2v_pvars_at_current preserved across block execution *)
Theorem m2v_pvars_at_current_preserved[local]:
  !fn bb fuel ctx s1 s2 s1' s2'.
    wf_function fn /\ fn_inst_wf fn /\
    ssa_form fn /\ alloca_pointer_confined fn /\
    MEM bb fn.fn_blocks /\
    bb.bb_label = s2.vs_current_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s2.vs_inst_idx = 0 /\ s1.vs_inst_idx = 0 /\
    fn_reachable fn s1.vs_current_bb /\
    exec_block fuel ctx bb s1 = OK s1' /\
    exec_block fuel ctx (m2v_bt fn bb) s2 = OK s2' /\
    ~s1'.vs_halted /\
    s1'.vs_current_bb = s2'.vs_current_bb /\
    m2v_pvars_at_current fn s2 ==>
    m2v_pvars_at_current fn s2'
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `EVERY inst_wf bb.bb_instructions` by metis_tac[fn_inst_wf_every_bb] >>
  `bb_well_formed (m2v_bt fn bb)` by
    metis_tac[m2v_bt_well_formed] >>
  (* successor of original block *)
  qpat_assum `exec_block _ _ bb _ = _`
     (assume_tac o MATCH_MP (bb_wf_in_succs |> pp (Pos last))) >>
  gvs[] >>
  `fn_cfg_edge fn bb.bb_label s2'.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> qexists `bb` >> simp[]) >>
  simp[m2v_pvars_at_current_def, m2v_pvars_set_def] >>
  rpt strip_tac >>
  Cases_on `store_bb = bb` >> gvs[]
  >- (* store_bb = bb: pvar is output of transformed block *)
    (`inst_wf store_inst` by metis_tac[EVERY_MEM] >>
     `MEM pvar (FLAT (MAP (\i. i.inst_outputs)
       (m2v_bt fn bb).bb_instructions))` by
      metis_tac[m2v_bt_has_pvar_output] >>
     `EVERY inst_wf (m2v_bt fn bb).bb_instructions` by
      metis_tac[m2v_bt_inst_wf] >>
     metis_tac[exec_block_output_defined])
  >> (* store_bb ≠ bb: dominates bb, pvar already defined *)
  `store_bb.bb_label <> s2'.vs_current_bb` by
    metis_tac[same_label_same_block] >>
  `fn_dominates fn store_bb.bb_label bb.bb_label` by
    metis_tac[fn_dominates_predecessor] >>
  qpat_x_assum `m2v_pvars_at_current _ _`
     (mp_tac o REWRITE_RULE[m2v_pvars_at_current_def]) >>
  disch_then (qspec_then `bb` mp_tac) >> simp[] >>
  rewrite_tac[m2v_pvars_set_def] >>
  disch_then (qspecl_then [`ao`, `pvar`, `32`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`store_bb`, `store_inst`] mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY inst_wf (m2v_bt fn bb).bb_instructions` by
    metis_tac[m2v_bt_inst_wf] >>
  metis_tac[exec_block_lookup_mono]
QED

(* NAS (nonpromoted access safety) preserved by exec_block, given
   per-step NAS preservation for all instructions in the block.
   Induction on remaining instructions (LENGTH - inst_idx). *)
Theorem nas_preserved_exec_block[local]:
  !fuel ctx bb s s' fn.
    exec_block fuel ctx bb s = OK s' /\
    m2v_nonpromoted_access_safe fn s /\
    (!inst fuel' ctx' sa sb.
      MEM inst bb.bb_instructions /\
      m2v_nonpromoted_access_safe fn sa /\
      step_inst fuel' ctx' inst sa = OK sb ==>
      m2v_nonpromoted_access_safe fn sb) ==>
    m2v_nonpromoted_access_safe fn s'
Proof
  completeInduct_on
    `if s.vs_inst_idx < LENGTH bb.bb_instructions
     then LENGTH bb.bb_instructions - s.vs_inst_idx else 0` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `step_inst _ _ inst _ = OK s2` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   MEM inst bb.bb_instructions` by
    (qpat_x_assum `get_instruction _ _ = SOME _` mp_tac >>
     simp[get_instruction_def, MEM_EL] >>
     rw[] >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  `m2v_nonpromoted_access_safe fn s2` by metis_tac[] >>
  gvs[] >>
  (* Apply IH: specialize with measure, then state, then remaining args *)
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then
    [`s2 with vs_inst_idx := SUC s.vs_inst_idx`, `bb`] mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`fuel`, `ctx`, `s'`, `fn`] mp_tac) >>
  simp[] >> disch_then irule >>
  qpat_x_assum `get_instruction _ _ = SOME _` mp_tac >>
  simp[get_instruction_def] >> metis_tac[]
QED

(* Main correctness theorem: mem-to-register promotion preserves
   function execution. States agree on all non-fresh variables and
   all observable fields (memory, storage, accounts, logs, etc.).
   Either the original errors, or both results are related by
   m2v_equiv through OK/Halt/Revert outcomes. *)
Theorem m2v_transform_function_correct:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    ssa_form fn /\
    m2v_promotable_wf fn /\
    m2v_fresh_names_disjoint fn /\
    m2v_fresh_undef fn s /\
    alloca_inv s /\
    s.vs_allocas = FEMPTY /\
    m2v_nonpromoted_access_safe fn s /\
    (* NAS preserved by any step in fn *)
    (!inst fuel' ctx' s' s''.
      MEM inst (fn_insts fn) /\
      m2v_nonpromoted_access_safe fn s' /\
      step_inst fuel' ctx' inst s' = OK s'' ==>
      m2v_nonpromoted_access_safe fn s'') /\
    (* nao bounded per-step *)
    (!inst fuel' ctx' s' s''.
      MEM inst (fn_insts fn) /\
      s'.vs_alloca_next < dimword (:256) /\
      step_inst fuel' ctx' inst s' = OK s'' ==>
      s''.vs_alloca_next < dimword (:256)) /\
    (* nao bounded throughout execution *)
    (!bb fuel' ctx' s' s''.
      MEM bb fn.fn_blocks /\
      s'.vs_alloca_next < dimword (:256) /\
      exec_block fuel' ctx' bb s' = OK s'' ==>
      s''.vs_alloca_next < dimword (:256)) /\
    alloca_pointer_confined fn /\
    all_mem_via_pointer fn (alloca_roots fn) /\
    m2v_promo_sizes_bounded fn /\
    m2v_return_size_bounded fn /\
    s.vs_alloca_next < dimword (:256) /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE)
      bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> MEMTOP)
      bb.bb_instructions) fn.fn_blocks /\
    alloca_bridge fn s /\
    fn_reachable fn s.vs_current_bb /\
    m2v_pvars_at_current fn s ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (m2v_equiv (m2v_fresh_vars fn))
               (m2v_equiv (m2v_fresh_vars fn))
               (m2v_equiv (m2v_fresh_vars fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (m2v_transform_function fn) s)
Proof
  rpt strip_tac
  >> ONCE_REWRITE_TAC[run_blocks_inst_idx_irrel]
  >> ONCE_REWRITE_TAC[m2v_transform_eq_fmt]
  >> qsuff_tac
       `(?e. run_blocks fuel ctx fn (s with vs_inst_idx := 0) = Error e) \/
        lift_result (\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                             m2v_ao_undef_sync fn s1 s2 /\
                             s1.vs_alloca_next = s2.vs_alloca_next)
                    (m2v_equiv (m2v_fresh_vars fn))
                    (m2v_equiv (m2v_fresh_vars fn))
          (run_blocks fuel ctx fn (s with vs_inst_idx := 0))
          (run_blocks fuel ctx (function_map_transform (m2v_bt fn) fn)
             (s with vs_inst_idx := 0))`
  >- (disch_then (fn th =>
        DISJ_CASES_TAC th
        >- (DISJ1_TAC >> gvs[])
        >> (DISJ2_TAC >> irule lift_result_weaken >>
            qexists `\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                             m2v_ao_undef_sync fn s1 s2 /\
                             s1.vs_alloca_next = s2.vs_alloca_next` >>
            simp[] >> metis_tac[m2v_inv_implies_equiv])))
  >> irule (SRULE [] block_sim_function_with_pred2_bb)
  >> BETA_TAC >> simp[m2v_bt_preserves_label]
  >> conj_tac >- (rpt strip_tac >> gvs[] >>
       metis_tac[m2v_inv_implies_equiv])
  >> conj_tac >- (rpt strip_tac >> gvs[] >>
       metis_tac[m2v_inv_control_flow])
  (* predicate: original-side invariants + fn_reachable + pvars_at_current *)
  >> qexists `\s1 s2. m2v_fresh_undef fn s1 /\ alloca_inv s1 /\
       s1.vs_alloca_next < dimword (:256) /\
       m2v_nonpromoted_access_safe fn s1 /\
       alloca_bridge fn s1 /\
       fn_reachable fn s1.vs_current_bb /\
       m2v_pvars_at_current fn s2`
  >> BETA_TAC >> rpt conj_tac
  (* P preserved across blocks *)
  >- (qx_gen_tac `bk` >> qx_gen_tac `fl` >> qx_gen_tac `cx` >>
      qx_gen_tac `sa` >> qx_gen_tac `sb` >>
      qx_gen_tac `sa'` >> qx_gen_tac `sb'` >>
      rpt strip_tac >> rpt conj_tac
      >- (irule m2v_fresh_undef_preserved_block >> metis_tac[])
      >- metis_tac[venomMemProofsTheory.alloca_inv_exec_block_proof]
      >- (first_x_assum irule >> metis_tac[])
      >- suspend "nas"
      >- suspend "bridge"
      >- suspend "reach"
      >> suspend "pvars")
  (* per-block simulation *)
  >- suspend "blocksim"
  (* P s s ==> R_ok s s *)
  >- (rpt strip_tac >> gvs[] >> rpt conj_tac
      >- (irule m2v_inv_refl >> simp[])
      >- (irule m2v_non32_ok_refl >> simp[])
      >- (irule m2v_ao_undef_sync_refl >>
          simp[vs_inst_idx_update_transparent_export])
      >> simp[])
  (* P (s with vs_inst_idx := 0) (s with vs_inst_idx := 0) *)
  >> simp[vs_inst_idx_update_transparent_export] >>
  qpat_x_assum `m2v_pvars_at_current _ _`
    (mp_tac o REWRITE_RULE[m2v_pvars_at_current_def, m2v_pvars_set_def,
                           lookup_var_def]) >>
  simp[m2v_pvars_at_current_def, m2v_pvars_set_def, lookup_var_def]
QED

Resume m2v_transform_function_correct[nas]:
  match_mp_tac nas_preserved_exec_block >>
  qexistsl [`fl`, `cx`, `bk`, `sa`] >> simp[] >>
  metis_tac[MEM_fn_insts]
QED

Resume m2v_transform_function_correct[bridge]:
  irule alloca_bridge_exec_block >>
  qpat_x_assum `EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) _) _`
    mp_tac >>
  simp[EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> simp[] >>
  metis_tac[]
QED

Resume m2v_transform_function_correct[reach]:
  irule fn_reachable_step >>
  qexists `sa.vs_current_bb` >> simp[] >>
  `bb_well_formed bk` by metis_tac[wf_function_bb_well_formed] >>
  `EVERY inst_wf bk.bb_instructions` by
    metis_tac[fn_inst_wf_every_bb] >>
  simp[fn_cfg_edge_def] >> qexists `bk` >> simp[] >>
  qpat_assum `exec_block _ _ bk _ = _`
    (assume_tac o MATCH_MP (bb_wf_in_succs |> pp (Pos last))) >>
  gvs[]
QED

Resume m2v_transform_function_correct[pvars]:
  `sa.vs_current_bb = sb.vs_current_bb /\
    sa'.vs_current_bb = sb'.vs_current_bb /\
    sb.vs_inst_idx = 0` by
    metis_tac[m2v_inv_control_flow, m2v_inv_def, m2v_equiv_def] >>
  match_mp_tac m2v_pvars_at_current_preserved >>
  qexistsl [`bk`, `fl`, `cx`, `sa`, `sb`, `sa'`] >> simp[]
QED

Resume m2v_transform_function_correct[blocksim]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `MEM bk fn.fn_blocks` >>
  rename1 `exec_block fl cx bk sa = _` >>
  rename1 `m2v_pvars_at_current fn sb` >>
  `bk.bb_label = sb.vs_current_bb` by
    metis_tac[m2v_inv_control_flow] >>
  `m2v_pvars_set fn bk 0 sb` by (
    qpat_x_assum `m2v_pvars_at_current _ _`
      (mp_tac o REWRITE_RULE[m2v_pvars_at_current_def]) >>
    disch_then (qspec_then `bk` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`fn`] m2v_per_block_sim) >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `bk` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fl`, `cx`, `sa`, `sb`] mp_tac) >>
  disch_then irule >> simp[] >>
  (* nao per-step: direct from hypothesis *)
  conj_tac >- (first_assum ACCEPT_TAC) >>
  (* NAS per-step: bridge from fn_insts to EL *)
  rpt strip_tac >>
  qpat_x_assum `!inst fuel' ctx' s' s''. MEM _ _ /\
    m2v_nonpromoted_access_safe _ _ /\ _ ==> _` irule >>
  simp[] >> goal_assum (drule_at Any) >>
  simp[] >> irule MEM_fn_insts >>
  qexists `bk` >> simp[MEM_EL] >>
  metis_tac[]
QED

Finalise m2v_transform_function_correct

(* ===== Obligations (out of scope) ===== *)

(* Structural property of the transform, not semantic correctness.
   Needed for pipeline composition. Requires showing m2v_bt preserves
   ALL_DISTINCT inst_ids and output uniqueness. *)
Theorem m2v_preserves_ssa_form:
  !fn. ssa_form fn ==> ssa_form (m2v_transform_function fn)
Proof
  cheat
QED

(* Structural property — m2v_bt preserves bb_well_formed (proved locally
   above), label structure, and block membership. *)
Theorem m2v_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (m2v_transform_function fn)
Proof
  cheat
QED

(* m2v_equiv implies observable_equiv — needed for pipeline composition *)
Theorem m2v_equiv_implies_observable:
  !vars s1 s2. m2v_equiv vars s1 s2 ==> observable_equiv s1 s2
Proof
  rw[m2v_equiv_def, observable_equiv_def]
QED

(* m2v_equiv implies revert_equiv — needed for R_abort in pipeline *)
Theorem m2v_equiv_implies_revert:
  !vars s1 s2. m2v_equiv vars s1 s2 ==> revert_equiv s1 s2
Proof
  rw[m2v_equiv_def, revert_equiv_def]
QED
