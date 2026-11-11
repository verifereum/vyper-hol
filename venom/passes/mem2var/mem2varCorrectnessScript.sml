Theory mem2varCorrectness
Ancestors
  mem2varProofs mem2varBlockSim
  mem2varDefs mem2varBlockSimHelpers mem2varFrame
  passSimulationDefs passSimulationProps
  stateEquiv
  venomExecSemantics venomState venomWf
  venomMemDefs venomMemProps venomExecProofs venomInst
  pointerConfinedDefs memLocDefs instIdxIndep
  irSupply
  finite_map list pred_set rich_list
  While
Libs
  pairLib mem2varFrameLib

val _ = augment_srw_ss [mem2varFrameLib.frame_ss];

(* eval_phis/run_block ignore the entry state's vs_inst_idx: PHIs read operands
   and run_block overwrites vs_inst_idx with phi_prefix_length before exec_block. *)
Triviality eval_one_phi_inst_idx:
  !inst s n.
    eval_one_phi (s with vs_inst_idx := n) inst = eval_one_phi s inst
Proof
  simp[eval_one_phi_def, eval_op_inst_idx]
QED

Triviality eval_phis_inst_idx:
  !insts s n.
    eval_phis (s with vs_inst_idx := n) insts =
    exec_result_map (\s'. s' with vs_inst_idx := n) (eval_phis s insts)
Proof
  Induct >> simp[eval_phis_def, exec_result_map_def, eval_one_phi_inst_idx] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> gvs[eval_one_phi_inst_idx]
  >- simp[exec_result_map_def] >>
  Q.SPEC_THEN `x` STRIP_ASSUME_TAC pairTheory.pair_CASES >>
  Cases_on `eval_phis s insts` >>
  gvs[exec_result_map_def, update_var_def]
QED

Triviality run_block_inst_idx_irrel:
  !fuel ctx bb s.
    run_block fuel ctx bb s =
    run_block fuel ctx bb (s with vs_inst_idx := 0)
Proof
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[eval_phis_inst_idx] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[exec_result_map_def]
QED

(* run_blocks ignores vs_inst_idx: it resets before each block *)
Theorem run_blocks_inst_idx_irrel[local]:
  !fuel ctx fn s.
    run_blocks fuel ctx fn s =
    run_blocks fuel ctx fn (s with vs_inst_idx := 0)
Proof
  Induct_on `fuel` >> rpt gen_tac
  >- (simp[run_blocks_def]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[run_blocks_unfold])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[run_blocks_unfold])) >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (simp_tac (srw_ss()) [] >>
      qpat_x_assum `lookup_block s.vs_current_bb fn.fn_blocks = NONE`
        (fn th => REWRITE_TAC [th]) >>
      simp_tac std_ss []) >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME x`
    (fn th => REWRITE_TAC [th]) >>
  PURE_ONCE_REWRITE_TAC [GSYM run_block_inst_idx_irrel] >>
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

(* All non-last elements of m2v_rewrite_inst are non-terminators *)
Theorem m2v_rewrite_inst_front_nonterm[local]:
  !fn inst j. j < LENGTH (m2v_rewrite_inst fn inst) - 1 ==>
    ~is_terminator (EL j (m2v_rewrite_inst fn inst)).inst_opcode
Proof
  rpt gen_tac >> simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)` >> simp[] >>
  PairCases_on `x` >> simp[m2v_promote_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def]
  >- (rpt (CASE_TAC >> simp[is_terminator_def]))
  >- (rpt (CASE_TAC >> simp[is_terminator_def]))
  >- (rpt (CASE_TAC >> simp[is_terminator_def]))
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
      metis_tac[m2v_rewrite_nonterm])
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

(* Project to opcodes before splitting the result spine: instruction equality
   would expand all record fields, none of which matter for PHI preservation.
   Cache the small rewrite set instead of rebuilding the ambient simpset. *)
val m2v_phi_ss = std_ss ++ rewrites
  [listTheory.MAP, listTheory.MEM, listTheory.list_case_def, LET_THM,
   instruction_accfupds, instruction_accessors,
   SIMP_CONV (srw_ss()) [] ``ASSIGN = PHI``,
   SIMP_CONV (srw_ss()) [] ``MSTORE = PHI``,
   SIMP_CONV (srw_ss()) [] ``PHI = MLOAD``,
   SIMP_CONV (srw_ss()) [] ``PHI = RETURN``];

(* m2v_promote_inst never introduces PHI opcodes *)
Theorem m2v_promote_inst_preserves_phi[local]:
  !pvar ao sz inst x. MEM x (m2v_promote_inst pvar ao sz inst) ==>
    x.inst_opcode = PHI ==> inst.inst_opcode = PHI
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  qsuff_tac
    `~MEM PHI (MAP (\i. i.inst_opcode) (m2v_promote_inst pvar ao sz inst))`
  >- (simp[MEM_MAP] >> metis_tac[]) >>
  PURE_REWRITE_TAC [m2v_promote_inst_def] >>
  rpt (BasicProvers.PURE_TOP_CASE_TAC >> asm_simp_tac m2v_phi_ss [])
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
  !fn bb. bb_well_formed bb ==>
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

(* Output variables of instructions in a list appear in the flattened output list *)
Triviality mem_flat_map_inst_outputs:
  !inst insts x.
    MEM inst insts /\ MEM x inst.inst_outputs ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct_on `insts` >> simp[] >> metis_tac[]
QED

(* Evaluating PHI nodes preserves fresh variable undefinedness *)
Triviality eval_phis_m2v_fresh_undef:
  !fn bb s s'.
    eval_phis s bb.bb_instructions = OK s' /\
    MEM bb fn.fn_blocks /\
    m2v_fresh_names_disjoint fn /\
    m2v_fresh_undef fn s ==>
    m2v_fresh_undef fn s'
Proof
  rw[m2v_fresh_undef_def, lookup_var_def] >>
  rename1 `fresh IN m2v_fresh_vars fn` >>
  `FLOOKUP s'.vs_vars fresh = FLOOKUP s.vs_vars fresh` by (
    irule eval_phis_flookup_not_phi_output >>
    qexists_tac `bb.bb_instructions` >> simp[] >>
    rpt strip_tac >>
    `~MEM fresh (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by (
      mp_tac (Q.SPECL [`fn`, `bb`, `fresh`]
        m2v_fresh_not_in_block_outputs) >> simp[]) >>
    CCONTR_TAC >>
    `MEM fresh (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by (
      irule mem_flat_map_inst_outputs >>
      qexists_tac `inst` >> simp[]) >>
    fs[]) >>
  gvs[m2v_fresh_undef_def, lookup_var_def]
QED

(* Fresh variable undefinedness is independent of instruction index *)
Triviality m2v_fresh_undef_inst_idx:
  !fn s n.
    m2v_fresh_undef fn (s with vs_inst_idx := n) =
    m2v_fresh_undef fn s
Proof
  simp[m2v_fresh_undef_def, lookup_var_def]
QED

(* run_block preserves the alloca_next field bound *)
Triviality run_block_alloca_next_bound:
  !fn bb fuel ctx s s'.
    run_block fuel ctx bb s = OK s' /\
    MEM bb fn.fn_blocks /\
    s.vs_alloca_next < dimword (:256) /\
    (!bb fuel ctx s s'.
      MEM bb fn.fn_blocks /\
      s.vs_alloca_next < dimword (:256) /\
      exec_block fuel ctx bb s = OK s' ==>
      s'.vs_alloca_next < dimword (:256)) ==>
    s'.vs_alloca_next < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (qpat_x_assum `?s_phi. eval_phis s bb.bb_instructions = OK s_phi`
        (qx_choose_then `s_phi` assume_tac) >>
      ASM_REWRITE_TAC[] >> strip_tac >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      drule eval_phis_preserves_alloca_fields >> strip_tac >>
      first_x_assum (qspecl_then [`bb`, `fuel`, `ctx`,
        `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `s'`] mp_tac) >>
      impl_tac >- simp[] >>
      DISCH_THEN ACCEPT_TAC) >>
  qpat_x_assum `?e. eval_phis s bb.bb_instructions = Error e`
    strip_assume_tac >>
  ASM_REWRITE_TAC[] >> simp[]
QED

(* run_block preserves fresh variable undefinedness *)
Triviality m2v_fresh_undef_preserved_run_block:
  !fuel ctx bb s s' fn.
    run_block fuel ctx bb s = OK s' /\
    MEM bb fn.fn_blocks /\
    m2v_fresh_names_disjoint fn /\
    m2v_fresh_undef fn s ==>
    m2v_fresh_undef fn s'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (qpat_x_assum `?s_phi. eval_phis s bb.bb_instructions = OK s_phi`
        (qx_choose_then `s_phi` assume_tac) >>
      ASM_REWRITE_TAC[] >> strip_tac >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      `m2v_fresh_undef fn s_phi` by (
        mp_tac (Q.SPECL [`fn`, `bb`, `s`, `s_phi`] eval_phis_m2v_fresh_undef) >>
        impl_tac >- simp[] >>
        DISCH_THEN ACCEPT_TAC) >>
      `m2v_fresh_undef fn
         (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
        simp[m2v_fresh_undef_inst_idx] >>
      MATCH_MP_TAC (Q.SPECL [`fuel`, `ctx`, `bb`,
        `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `s'`, `fn`]
        m2v_fresh_undef_preserved_block) >>
      rpt conj_tac
      >- qpat_x_assum `run_block_non_phis fuel ctx bb
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s'`
           ACCEPT_TAC
      >- qpat_x_assum `MEM bb fn.fn_blocks` ACCEPT_TAC
      >- qpat_x_assum `m2v_fresh_names_disjoint fn` ACCEPT_TAC
      >- qpat_x_assum `m2v_fresh_undef fn
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
           ACCEPT_TAC) >>
  qpat_x_assum `?e. eval_phis s bb.bb_instructions = Error e`
    strip_assume_tac >>
  ASM_REWRITE_TAC[] >> simp[]
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
    (* NAS preserved by full block execution, including PHI prefixes *)
    (!bb fuel' ctx' s' s''.
      MEM bb fn.fn_blocks /\
      m2v_nonpromoted_access_safe fn s' /\
      run_block fuel' ctx' bb s' = OK s'' ==>
      m2v_nonpromoted_access_safe fn s'') /\
    (* alloca_next bounded per-step *)
    (!inst fuel' ctx' s' s''.
      MEM inst (fn_insts fn) /\
      s'.vs_alloca_next < dimword (:256) /\
      step_inst fuel' ctx' inst s' = OK s'' ==>
      s''.vs_alloca_next < dimword (:256)) /\
    (* alloca_next bounded throughout execution *)
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
    EVERY (\bb. EVERY (\i. i.inst_opcode <> MSIZE)
      bb.bb_instructions) fn.fn_blocks /\
    alloca_bridge fn s /\
    (!bb fuel' ctx' s' s''.
      MEM bb fn.fn_blocks /\
      alloca_bridge fn s' /\
      run_block fuel' ctx' bb s' = OK s'' ==>
      alloca_bridge fn s'') /\
    fn_reachable fn s.vs_current_bb /\
    m2v_pvars_at_current fn s /\
    (!bb fuel' ctx' s1 s2 s1' s2'.
      wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
      alloca_pointer_confined fn /\ MEM bb fn.fn_blocks /\
      bb.bb_label = s2.vs_current_bb /\
      s1.vs_current_bb = s2.vs_current_bb /\
      fn_reachable fn s1.vs_current_bb /\
      run_block fuel' ctx' bb s1 = OK s1' /\
      run_block fuel' ctx' (m2v_bt fn bb) s2 = OK s2' /\
      ~s1'.vs_halted /\ s1'.vs_current_bb = s2'.vs_current_bb /\
      m2v_pvars_at_current fn s2 ==>
      m2v_pvars_at_current fn s2') /\
    (!bb fuel' ctx' s1 s2.
      wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
      m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
      m2v_promo_sizes_bounded fn /\ m2v_return_size_bounded fn /\
      alloca_pointer_confined fn /\ all_mem_via_pointer fn (alloca_roots fn) /\
      EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions) fn.fn_blocks /\
      EVERY (\bb. EVERY (\i. i.inst_opcode <> MSIZE) bb.bb_instructions) fn.fn_blocks /\
      MEM bb fn.fn_blocks /\
      m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
      m2v_ao_undef_sync fn s1 s2 /\ m2v_fresh_undef fn s1 /\
      alloca_inv s1 /\ alloca_bridge fn s1 /\
      s1.vs_alloca_next < dimword (:256) /\
      m2v_nonpromoted_access_safe fn s1 /\
      s1.vs_alloca_next = s2.vs_alloca_next /\
      m2v_pvars_at_current fn s2 ==>
      (?e. run_block fuel' ctx' bb s1 = Error e) \/
      lift_result (\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                           m2v_ao_undef_sync fn s1 s2 /\
                           s1.vs_alloca_next = s2.vs_alloca_next)
                  (m2v_equiv (m2v_fresh_vars fn))
                  (m2v_equiv (m2v_fresh_vars fn))
        (run_block fuel' ctx' bb s1)
        (run_block fuel' ctx' (m2v_bt fn bb) s2)) ==>
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
  >> BETA_TAC
  >> conj_tac >- (rpt strip_tac >> irule m2v_bt_preserves_label)
  >> conj_tac >- (rpt strip_tac >> gvs[] >>
       metis_tac[m2v_inv_implies_equiv])
  >> conj_tac >- (rpt strip_tac >> gvs[] >>
       metis_tac[m2v_inv_control_flow])
  (* predicate: original-side invariants + fn_reachable + pvars_at_current *)
  >> conj_tac
  >- (qexists `\s1 s2. m2v_fresh_undef fn s1 /\ alloca_inv s1 /\
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
      >- (mp_tac (Q.SPECL [`fl`, `cx`, `bk`, `sa`, `sa'`, `fn`]
            m2v_fresh_undef_preserved_run_block) >>
          impl_tac >- simp[] >>
          DISCH_THEN ACCEPT_TAC)
      >- (mp_tac (Q.SPECL [`fl`, `cx`, `bk`, `sa`, `sa'`]
            venomMemPropsTheory.alloca_inv_run_block) >>
          impl_tac >- simp[] >>
          DISCH_THEN ACCEPT_TAC)
      >- (mp_tac (Q.SPECL [`fn`, `bk`, `fl`, `cx`, `sa`, `sa'`]
            run_block_alloca_next_bound) >>
          impl_tac >- (
            simp[] >>
            qpat_x_assum `!bb fuel' ctx' s' s''.
              MEM bb fn.fn_blocks /\ s'.vs_alloca_next < dimword (:256) /\
              run_block_non_phis fuel' ctx' bb s' = OK s'' ==>
              s''.vs_alloca_next < dimword (:256)` ACCEPT_TAC) >>
          DISCH_THEN ACCEPT_TAC)
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
  simp[m2v_pvars_at_current_def, m2v_pvars_set_def, lookup_var_def])
  >- simp[]
QED

Resume m2v_transform_function_correct[nas]:
  qpat_x_assum `!bb fuel' ctx' s' s''.
    MEM bb fn.fn_blocks /\ m2v_nonpromoted_access_safe fn s' /\
    run_block fuel' ctx' bb s' = OK s'' ==>
    m2v_nonpromoted_access_safe fn s''`
    (qspecl_then [`bk`, `fl`, `cx`, `sa`, `sa'`] mp_tac) >>
  simp[]
QED

Resume m2v_transform_function_correct[bridge]:
  qpat_x_assum `!bb fuel' ctx' s' s''.
    MEM bb fn.fn_blocks /\ alloca_bridge fn s' /\
    run_block fuel' ctx' bb s' = OK s'' ==>
    alloca_bridge fn s''`
    (qspecl_then [`bk`, `fl`, `cx`, `sa`, `sa'`] mp_tac) >>
  simp[]
QED

Resume m2v_transform_function_correct[reach]:
  irule fn_reachable_step >>
  qexists `sa.vs_current_bb` >> simp[] >>
  `bb_well_formed bk` by metis_tac[wf_function_bb_well_formed] >>
  `EVERY inst_wf bk.bb_instructions` by
    metis_tac[fn_inst_wf_every_bb] >>
  simp[fn_cfg_edge_def] >> qexists `bk` >> simp[] >>
  mp_tac (Q.SPECL [`fl`, `cx`, `bk`, `sa`, `sa'`]
    venomExecPropsTheory.run_block_current_bb_in_succs) >>
  impl_tac >- (
    qpat_x_assum `bb_well_formed bk`
      (strip_assume_tac o REWRITE_RULE[bb_well_formed_def]) >>
    rpt conj_tac
    >- simp[]
    >- (rpt strip_tac >>
        `i = PRE (LENGTH bk.bb_instructions)` by
          (first_x_assum irule >> simp[]) >>
        qpat_x_assum `i = PRE _` SUBST_ALL_TAC >>
        qpat_x_assum `PRE _ < _ - 1` mp_tac >> simp[])
    >- simp[]
    >- simp[]) >>
  simp[]
QED

Resume m2v_transform_function_correct[pvars]:
  `sa.vs_current_bb = sb.vs_current_bb /\
    sa'.vs_current_bb = sb'.vs_current_bb` by
    metis_tac[m2v_inv_control_flow] >>
  qpat_x_assum `!bb fuel' ctx' s1 s2 s1' s2'.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    alloca_pointer_confined fn /\ MEM bb fn.fn_blocks /\
    bb.bb_label = s2.vs_current_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    fn_reachable fn s1.vs_current_bb /\
    run_block fuel' ctx' bb s1 = OK s1' /\
    run_block fuel' ctx' (m2v_bt fn bb) s2 = OK s2' /\
    ~s1'.vs_halted /\ s1'.vs_current_bb = s2'.vs_current_bb /\
    m2v_pvars_at_current fn s2 ==>
    m2v_pvars_at_current fn s2'`
    (qspecl_then [`bk`, `fl`, `cx`, `sa`, `sb`, `sa'`, `sb'`] mp_tac) >>
  simp[]
QED

Resume m2v_transform_function_correct[blocksim]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `MEM bk fn.fn_blocks` >>
  rename1 `m2v_pvars_at_current fn s2` >>
  qpat_x_assum `!bb fuel' ctx' s1 s2. _`
    (qspecl_then [`bk`, `fuel`, `ctx`, `s1`, `s2`] mp_tac) >>
  simp[]
QED

Finalise m2v_transform_function_correct

(* ===== Structural obligation: supply-aware transform keeps wf_function =====

   m2v_transform_function_supply rewrites exactly like m2v_bt up to inst_ids,
   and the only new id (the mstore before a promoted return) comes from the
   supply, above every id of the input function. *)

Overload m2v_erase[local] = ``\i:instruction. i with inst_id := 0``
Overload m2v_ids[local] = ``MAP (\i:instruction. i.inst_id)``
Overload m2v_bids[local] =
  ``\bbs. FLAT (MAP (\bb. MAP (\i:instruction. i.inst_id) bb.bb_instructions) bbs)``

Theorem m2v_promote_inst_ids[local]:
  !pvar ao sz i.
    (?x. m2v_promote_inst pvar ao sz i = [x] /\ x.inst_id = i.inst_id) \/
    (?y. m2v_promote_inst pvar ao sz i = [y; i])
Proof
  rpt gen_tac >> simp[m2v_promote_inst_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem m2v_rewrite_inst_supply_cases[local]:
  !fn s i outs s'.
    m2v_rewrite_inst_supply (m2v_promo_list fn) s i = (outs, s') ==>
    (m2v_rewrite_inst fn i = outs /\ s' = s /\
     ?x. outs = [x] /\ x.inst_id = i.inst_id) \/
    (?y. m2v_rewrite_inst fn i = [y; i] /\
         outs = [y with inst_id := s.irs_next_inst; i] /\
         s'.irs_next_inst = SUC s.irs_next_inst)
Proof
  rpt gen_tac >> simp[m2v_rewrite_inst_supply_def, m2v_rewrite_inst_def] >>
  CASE_TAC >> simp[]
  >- (strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[m2v_promote_inst_supply_def] >>
  qspecl_then [`x1`, `x0`, `x2`, `i`] strip_assume_tac m2v_promote_inst_ids >>
  simp[fresh_inst_id_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem m2v_rewrite_insts_supply_props[local]:
  !insts fn s outs s'.
    m2v_rewrite_insts_supply (m2v_promo_list fn) s insts = (outs, s') ==>
    MAP m2v_erase outs =
      MAP m2v_erase (FLAT (MAP (m2v_rewrite_inst fn) insts)) /\
    s.irs_next_inst <= s'.irs_next_inst /\
    (!x. MEM x (m2v_ids outs) ==>
         MEM x (m2v_ids insts) \/
         s.irs_next_inst <= x /\ x < s'.irs_next_inst) /\
    (ALL_DISTINCT (m2v_ids insts) /\
     EVERY (\x. x < s.irs_next_inst) (m2v_ids insts) ==>
     ALL_DISTINCT (m2v_ids outs))
Proof
  Induct >> simp[m2v_rewrite_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `m2v_rewrite_inst_supply (m2v_promo_list fn) s h` >>
  Cases_on `m2v_rewrite_insts_supply (m2v_promo_list fn) r insts` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule m2v_rewrite_inst_supply_cases >> strip_tac >> gvs[]
  >- (rpt strip_tac >> gvs[MEM_MAP, EVERY_MEM] >>
      qpat_x_assum `!x. (?i. _ /\ MEM i q') ==> _`
        (qspec_then `i.inst_id` mp_tac) >>
      (impl_tac >- (qexists `i` >> simp[])) >>
      strip_tac >> gvs[] >> metis_tac[])
  >> conj_tac
  >- (rpt strip_tac >> gvs[MEM_MAP, PULL_EXISTS] >>
      qpat_x_assum `!i. MEM i q' ==> _` (drule_then strip_assume_tac) >>
      gvs[] >> metis_tac[])
  >> strip_tac >>
  `ALL_DISTINCT (m2v_ids q')` by
    (first_x_assum irule >> gvs[MEM_MAP, PULL_EXISTS, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> simp[]) >>
  gvs[MEM_MAP, PULL_EXISTS, EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i q' ==> _` (drule_then strip_assume_tac) >>
  gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem m2v_erase_block[local]:
  !b1 b2.
    MAP m2v_erase b1.bb_instructions = MAP m2v_erase b2.bb_instructions ==>
    (bb_well_formed b1 <=> bb_well_formed b2) /\ bb_succs b1 = bb_succs b2
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH b1.bb_instructions = LENGTH b2.bb_instructions`
    by metis_tac[LENGTH_MAP] >>
  `!i. i < LENGTH b1.bb_instructions ==>
       (EL i b1.bb_instructions).inst_opcode =
         (EL i b2.bb_instructions).inst_opcode /\
       get_successors (EL i b1.bb_instructions) =
         get_successors (EL i b2.bb_instructions)` by
    (rpt gen_tac >> strip_tac >>
     `m2v_erase (EL i b1.bb_instructions) =
      m2v_erase (EL i b2.bb_instructions)` by metis_tac[EL_MAP] >>
     gvs[instruction_component_equality, get_successors_def]) >>
  Cases_on `b1.bb_instructions = []`
  >- gvs[bb_well_formed_def, bb_succs_def] >>
  `b2.bb_instructions <> []` by (strip_tac >> gvs[]) >>
  `0 < LENGTH b1.bb_instructions` by (Cases_on `b1.bb_instructions` >> gvs[]) >>
  `LAST b1.bb_instructions = EL (PRE (LENGTH b1.bb_instructions)) b1.bb_instructions /\
   LAST b2.bb_instructions = EL (PRE (LENGTH b1.bb_instructions)) b2.bb_instructions`
    by simp[LAST_EL] >>
  `PRE (LENGTH b1.bb_instructions) < LENGTH b1.bb_instructions` by simp[] >>
  conj_tac
  >- (simp[bb_well_formed_def] >> metis_tac[DECIDE ``i < j /\ j < n ==> i < n:num``])
  >> simp[bb_succs_def] >>
  Cases_on `b1.bb_instructions` >> Cases_on `b2.bb_instructions` >> gvs[] >>
  metis_tac[]
QED

Theorem m2v_rewrite_blocks_supply_props[local]:
  !bbs fn s bbs' s'.
    m2v_rewrite_blocks_supply (m2v_promo_list fn) s bbs = (bbs', s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs /\
    LIST_REL (\bb bb'. MAP m2v_erase bb'.bb_instructions =
                       MAP m2v_erase (m2v_bt fn bb).bb_instructions) bbs bbs' /\
    s.irs_next_inst <= s'.irs_next_inst /\
    (!x. MEM x (m2v_bids bbs') ==>
         MEM x (m2v_bids bbs) \/
         s.irs_next_inst <= x /\ x < s'.irs_next_inst) /\
    (ALL_DISTINCT (m2v_bids bbs) /\
     EVERY (\x. x < s.irs_next_inst) (m2v_bids bbs) ==>
     ALL_DISTINCT (m2v_bids bbs'))
Proof
  Induct >> simp[m2v_rewrite_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `m2v_rewrite_insts_supply (m2v_promo_list fn) s h.bb_instructions` >>
  Cases_on `m2v_rewrite_blocks_supply (m2v_promo_list fn) r bbs` >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule m2v_rewrite_insts_supply_props >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  gvs[m2v_bt_instructions] >>
  conj_tac
  >- (rpt strip_tac >> res_tac >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
                arithmeticTheory.LESS_EQ_TRANS]) >>
  strip_tac >> gvs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
  `ALL_DISTINCT (m2v_bids q')` by
    (qpat_x_assum `_ ==> ALL_DISTINCT (m2v_bids q')` irule >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!x. MEM x (m2v_ids q) ==> _` drule >>
  qpat_x_assum `!x. MEM x (m2v_bids q') ==> _` drule >>
  rpt strip_tac >> gvs[] >> res_tac >> gvs[]
QED

(* Mem2Var runs between two MakeSSA passes and emits several assigns to one
   promoted variable, so it has no ssa_form obligation. *)
Theorem m2v_preserves_wf_function:
  !s fn.
    wf_function fn /\ EVERY (\id. id < s.irs_next_inst) (fn_ir_inst_ids fn) ==>
    wf_function (FST (m2v_transform_function_supply s fn))
Proof
  rpt strip_tac >> simp[m2v_transform_function_supply_def] >>
  Cases_on `m2v_rewrite_blocks_supply (m2v_promo_list fn) s fn.fn_blocks` >>
  simp[] >>
  drule m2v_rewrite_blocks_supply_props >> strip_tac >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def,
      fn_succs_closed_def, fn_inst_ids_distinct_def] >>
  rpt conj_tac
  >- (strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[LIST_REL_EL_EQN, MEM_EL] >>
      first_x_assum drule >> strip_tac >>
      drule m2v_erase_block >> strip_tac >> simp[] >>
      irule m2v_bt_well_formed >> metis_tac[MEM_EL])
  >- (rpt strip_tac >> gvs[LIST_REL_EL_EQN, MEM_EL] >>
      first_x_assum drule >> strip_tac >>
      drule m2v_erase_block >> strip_tac >>
      `bb_well_formed (EL n fn.fn_blocks)` by metis_tac[MEM_EL] >>
      `bb_succs (m2v_bt fn (EL n fn.fn_blocks)) = bb_succs (EL n fn.fn_blocks)`
        by (irule m2v_bt_succs >> simp[]) >>
      gvs[] >> metis_tac[MEM_EL])
  >> first_x_assum irule >>
  gvs[fn_ir_inst_ids_def, block_ir_inst_ids_def,
      EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
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
