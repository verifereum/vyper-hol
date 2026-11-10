Theory mem2varCorrectness
Ancestors
  mem2varProofs mem2varReach mem2varInvariant mem2varBlockSim
  ptrDiscipline ptrSafeRun unitTransformDefs
  mem2varDefs mem2varBlockSimHelpers mem2varFrame
  passSimulationDefs passSimulationProps
  stateEquiv
  venomExecSemantics venomState venomWf
  venomMemDefs venomMemProps venomExecProofs venomInst
  pointerConfinedDefs memLocDefs instIdxIndep
  irSupply analysisSimProofsBase venomWfProps
  finite_map list pred_set rich_list
  While
Libs
  pairLib mem2varFrameLib

val _ = augment_srw_ss [mem2varFrameLib.frame_ss];

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

(* Output variables of instructions in a list appear in the flattened output list *)
Triviality mem_flat_map_inst_outputs:
  !inst insts x.
    MEM inst insts /\ MEM x inst.inst_outputs ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct_on `insts` >> simp[] >> metis_tac[]
QED

Theorem m2v_promote_inst_wf[local]:
  !inst pvar ao sz. inst_wf inst ==>
    EVERY inst_wf (m2v_promote_inst pvar ao sz inst)
Proof
  rpt strip_tac >> rw[m2v_promote_inst_def] >>
  rpt (CASE_TAC >> gvs[]) >> gvs[inst_wf_def]
QED

Theorem m2v_rewrite_inst_wf[local]:
  !fn inst. inst_wf inst ==> EVERY inst_wf (m2v_rewrite_inst fn inst)
Proof
  rpt strip_tac >> simp[m2v_rewrite_inst_def] >>
  CASE_TAC >> simp[] >> PairCases_on `x` >>
  simp[m2v_promote_inst_wf]
QED

Theorem m2v_bt_inst_wf[local]:
  !fn bb. fn_inst_wf fn /\ MEM bb fn.fn_blocks ==>
    EVERY inst_wf (m2v_bt fn bb).bb_instructions
Proof
  rpt strip_tac >> simp[m2v_bt_instructions, EVERY_FLAT, EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `inst_wf x` by metis_tac[fn_inst_wf_MEM, MEM_fn_insts] >>
  drule m2v_rewrite_inst_wf >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem m2v_rewrite_promoted_store[local]:
  !fn bb inst ao pvar.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = MSTORE /\
    MEM (ao,pvar,32) (m2v_promo_list fn) /\
    MEM (Var ao) inst.inst_operands ==>
    ?val_op. m2v_rewrite_inst fn inst =
      [inst with <|inst_opcode := ASSIGN; inst_operands := [val_op];
                   inst_outputs := [pvar]|>]
Proof
  rpt strip_tac >>
  `?val_op. inst.inst_operands = [Var ao; val_op]` by
    metis_tac[m2v_pointer_confined_mstore_ao_is_offset] >>
  simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(a,_,_). MEM (Var a) inst.inst_operands)
                (m2v_promo_list fn)`
  >- (gvs[FIND_NONE_EVERY, EVERY_MEM] >>
      first_x_assum (qspec_then `(ao,pvar,32)` mp_tac) >> simp[]) >>
  PairCases_on `x` >>
  `MEM (x0,x1,x2) (m2v_promo_list fn) /\
   MEM (Var x0) inst.inst_operands` by
    (conj_tac
     >- metis_tac[venomExecProofsTheory.FIND_MEM] >>
     drule venomExecProofsTheory.FIND_P >> simp[]) >>
  `?v. inst.inst_operands = [Var x0; v]` by
    metis_tac[m2v_pointer_confined_mstore_ao_is_offset] >>
  `x0 = ao` by gvs[] >>
  `x1 = pvar /\ x2 = 32` by metis_tac[m2v_promo_list_ao_unique] >>
  gvs[m2v_promote_inst_def] >> metis_tac[]
QED

Theorem m2v_promoted_store_output[local]:
  !fn bb inst ao pvar.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = MSTORE /\
    MEM (ao,pvar,32) (m2v_promo_list fn) /\
    MEM (Var ao) inst.inst_operands ==>
    ?j. j < LENGTH (m2v_bt fn bb).bb_instructions /\
        phi_prefix_length (m2v_bt fn bb).bb_instructions <= j /\
        ~is_terminator (EL j (m2v_bt fn bb).bb_instructions).inst_opcode /\
        MEM pvar (EL j (m2v_bt fn bb).bb_instructions).inst_outputs
Proof
  rpt strip_tac >> drule_all m2v_rewrite_promoted_store >> strip_tac >>
  `?out. MEM out (m2v_bt fn bb).bb_instructions /\
         out.inst_opcode = ASSIGN /\ out.inst_outputs = [pvar]` by
    (qexists_tac `inst with <|inst_opcode := ASSIGN;
        inst_operands := [val_op]; inst_outputs := [pvar]|>` >>
     simp[m2v_bt_instructions, MEM_FLAT, MEM_MAP] >>
     qexists_tac `m2v_rewrite_inst fn inst` >> simp[] >>
     metis_tac[]) >>
  drule (iffLR MEM_EL) >> strip_tac >>
  qexists_tac `n` >> simp[] >>
  `phi_prefix_length (m2v_bt fn bb).bb_instructions <= n` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPEC `(m2v_bt fn bb).bb_instructions` phi_prefix_all_phi) >>
     rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `out` mp_tac) >>
     simp[] >>
     `n < phi_prefix_length (m2v_bt fn bb).bb_instructions` by decide_tac >>
     simp[MEM_EL] >> qexists_tac `n` >> simp[EL_TAKE, LENGTH_TAKE_EQ]) >>
  qpat_x_assum `out = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[is_terminator_def]
QED

Theorem m2v_run_block_defined_preserved[local]:
  !fn bb fuel ctx s t pvar.
    wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    run_block fuel ctx (m2v_bt fn bb) s = OK t /\
    IS_SOME (lookup_var pvar s) ==>
    IS_SOME (lookup_var pvar t)
Proof
  rpt strip_tac >>
  `bb_well_formed (m2v_bt fn bb)` by
    metis_tac[wf_function_def, m2v_bt_well_formed] >>
  `EVERY inst_wf (m2v_bt fn bb).bb_instructions` by
    metis_tac[m2v_bt_inst_wf] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `(m2v_bt fn bb).bb_instructions`]
    eval_phis_ok_or_error_defs)
  >- (pop_assum strip_assume_tac >> simp[] >> strip_tac >>
      drule exec_block_lookup_mono >> simp[] >>
      disch_then irule >>
      drule eval_phis_vars_grow >>
      gvs[lookup_var_def, FLOOKUP_DEF, SUBSET_DEF] >>
      Cases_on `pvar IN FDOM s.vs_vars` >> gvs[] >>
      strip_tac >>
      `pvar IN FDOM s'.vs_vars` by metis_tac[] >> simp[]) >>
  pop_assum strip_assume_tac >> simp[]
QED

Theorem m2v_run_block_store_defined[local]:
  !fn bb inst ao pvar fuel ctx s t.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MSTORE /\
    MEM (ao,pvar,32) (m2v_promo_list fn) /\
    MEM (Var ao) inst.inst_operands /\
    run_block fuel ctx (m2v_bt fn bb) s = OK t ==>
    IS_SOME (lookup_var pvar t)
Proof
  rpt strip_tac >>
  `bb_well_formed (m2v_bt fn bb)` by
    metis_tac[wf_function_def, m2v_bt_well_formed] >>
  `EVERY inst_wf (m2v_bt fn bb).bb_instructions` by
    metis_tac[m2v_bt_inst_wf] >>
  drule_all m2v_promoted_store_output >> strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `(m2v_bt fn bb).bb_instructions`]
    eval_phis_ok_or_error_defs)
  >- (pop_assum strip_assume_tac >> simp[] >> strip_tac >>
      `pvar IN FDOM t.vs_vars` by
        (irule exec_block_output_in_fdom_aux >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      simp[lookup_var_def, FLOOKUP_DEF]) >>
  pop_assum strip_assume_tac >> simp[]
QED

(* Promoted variables remain initialized when control crosses a block edge. *)
Theorem m2v_pvars_at_current_successor:
  !fn bb fuel ctx s1 s2 s1' s2'.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    m2v_fresh_names_disjoint fn /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s2.vs_current_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    fn_reachable fn s1.vs_current_bb /\
    run_block fuel ctx bb s1 = OK s1' /\
    run_block fuel ctx (m2v_bt fn bb) s2 = OK s2' /\
    ~s1'.vs_halted /\ s1'.vs_current_bb = s2'.vs_current_bb /\
    m2v_pvars_at_current fn s2 ==>
    m2v_pvars_at_current fn s2'
Proof
  rpt strip_tac >>
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    metis_tac[fn_inst_wf_MEM, MEM_fn_insts, EVERY_MEM] >>
  `MEM s1'.vs_current_bb (bb_succs bb)` by
    (`!i. i < LENGTH bb.bb_instructions - 1 ==>
          ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
       (gvs[bb_well_formed_def] >> rpt strip_tac >>
        qpat_x_assum `!i. _ ==> i = _` (qspec_then `i` mp_tac) >>
        simp[] >> decide_tac) >>
     irule venomExecPropsTheory.run_block_current_bb_in_succs >>
     metis_tac[bb_well_formed_def]) >>
  rw[m2v_pvars_at_current_def] >>
  irule m2v_pvars_set_init >> rpt strip_tac >> gvs[] >>
  `store_bb.bb_label <> bb'.bb_label` by
    metis_tac[same_label_same_block] >>
  `fn_dominates fn store_bb.bb_label bb.bb_label` by
    (irule fn_dominates_predecessor >> conj_tac >- metis_tac[] >>
     qexists_tac `bb'.bb_label` >> simp[fn_cfg_edge_def] >>
     metis_tac[]) >>
  Cases_on `store_bb = bb`
  >- (gvs[] >> irule m2v_run_block_store_defined >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  `IS_SOME (lookup_var pvar s2)` by
    (gvs[m2v_pvars_at_current_def, m2v_pvars_set_def] >> metis_tac[]) >>
  metis_tac[m2v_run_block_defined_preserved]
QED


Theorem m2v_entry_pvars_set[local]:
  !fn bb s. wf_function fn /\ MEM bb fn.fn_blocks /\
    fn_entry_label fn = SOME bb.bb_label ==> m2v_pvars_set fn bb 0 s
Proof
  rpt strip_tac >> irule m2v_pvars_set_init >> rpt strip_tac >>
  `store_bb.bb_label = bb.bb_label` by
    (qpat_x_assum `fn_dominates _ _ _` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum (qspec_then `[bb.bb_label]` mp_tac) >>
     simp[is_fn_path_def]) >>
  metis_tac[same_label_same_block]
QED

Theorem m2v_checked_entry_label[local]:
  !fn fn'. m2v_transform_function_checked fn = SOME fn' ==>
    fn_entry_label fn' = fn_entry_label fn
Proof
  rw[m2v_transform_function_checked_def] >>
  simp[m2v_transform_function_raw_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Theorem m2v_checked_lookup_block[local]:
  !fn fn' lbl. m2v_transform_function_checked fn = SOME fn' ==>
    lookup_block lbl fn'.fn_blocks =
      OPTION_MAP (m2v_bt fn) (lookup_block lbl fn.fn_blocks)
Proof
  rw[m2v_transform_function_checked_def] >>
  `!bbs. lookup_block lbl (MAP (m2v_bt fn) bbs) =
          OPTION_MAP (m2v_bt fn) (lookup_block lbl bbs)` by
    (Induct >> simp[lookup_block_def, FIND_thm, m2v_bt_def] >>
     rw[] >> gvs[lookup_block_def, m2v_bt_def]) >>
  first_x_assum (qspec_then `fn.fn_blocks` mp_tac) >>
  simp[m2v_transform_function_raw_def, lambdify m2v_bt_def]
QED

Theorem m2v_initial_fresh_undef[local]:
  !fn s. o1_initial_state_ok s ==> m2v_fresh_undef fn s
Proof
  simp[o1_initial_state_ok_def, m2v_fresh_undef_def, lookup_var_def]
QED

(* Initial empty environments make synchronization obligations vacuous. *)
Theorem m2v_initial_inv_noix[local]:
  !fn s. o1_initial_state_ok s ==> m2v_inv_noix fn s s
Proof
  simp[o1_initial_state_ok_def, m2v_inv_noix_def, lookup_var_def,
       allocas_non_overlapping_def]
QED

(* Rewriting preserves the PHI prefix, including its evaluation errors. *)
Theorem m2v_rewrite_phis[local]:
  !fn insts s.
    phi_prefix_length (FLAT (MAP (m2v_rewrite_inst fn) insts)) =
      phi_prefix_length insts /\
    eval_phis s (FLAT (MAP (m2v_rewrite_inst fn) insts)) =
      eval_phis s insts
Proof
  gen_tac >> Induct >> simp[phi_prefix_length_def, eval_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[m2v_rewrite_inst_phi, phi_prefix_length_def, eval_phis_def] >>
      Cases_on `eval_one_phi s h` >> simp[] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `eval_phis s insts` >> simp[]) >>
  `m2v_rewrite_inst fn h <> []` by
    metis_tac[m2v_rewrite_inst_len_ge1, LENGTH_NIL,
              DECIDE ``1n <= n ==> n <> 0``] >>
  Cases_on `m2v_rewrite_inst fn h` >> gvs[] >>
  `h'.inst_opcode <> PHI` by
    metis_tac[m2v_rewrite_inst_preserves_phi, MEM] >>
  simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem m2v_one_phi_agrees[local]:
  !fn inst s t.
    m2v_inv_noix fn s t /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) ==>
    eval_one_phi s inst = eval_one_phi t inst
Proof
  rpt strip_tac >>
  `s.vs_prev_bb = t.vs_prev_bb` by
    (gvs[m2v_inv_noix_def]) >>
  simp[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t.vs_prev_bb` >> simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  `MEM x' inst.inst_operands` by metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
  `eval_operand x' s = eval_operand x' t` by
    metis_tac[m2v_inv_noix_eval_agrees] >> simp[]
QED

Theorem m2v_phi_update[local]:
  !fn inst out value s t.
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
    MEM out inst.inst_outputs /\
    m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
    m2v_ao_undef_sync fn s t ==>
    m2v_inv_noix fn (update_var out value s) (update_var out value t) /\
    m2v_non32_ok fn (update_var out value s) (update_var out value t) /\
    m2v_ao_undef_sync fn (update_var out value s) (update_var out value t)
Proof
  rpt gen_tac >> strip_tac >>
  `out NOTIN m2v_fresh_vars fn /\
   !pv sz. ~MEM (out,pv,sz) (m2v_promo_list fn)` by
    (irule m2v_output_safe >> simp[] >>
     qexists_tac `inst` >> simp[is_alloca_op_def]) >>
  conj_tac
  >- (irule m2v_inv_noix_update_var >> simp[]) >>
  `!ao pv sz. MEM (ao,pv,sz) (m2v_promo_list fn) ==> pv <> out` by
    metis_tac[m2v_promo_list_in_fresh_vars] >>
  gvs[m2v_non32_ok_def, m2v_ao_undef_sync_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem m2v_eval_phis[local]:
  !insts fn s t s'.
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    EVERY (\i. MEM i (fn_insts fn)) insts /\
    m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
    m2v_ao_undef_sync fn s t /\ eval_phis s insts = OK s' ==>
    ?t'. eval_phis t insts = OK t' /\
      m2v_inv_noix fn s' t' /\ m2v_non32_ok fn s' t' /\
      m2v_ao_undef_sync fn s' t'
Proof
  Induct >> rpt gen_tac >> simp[eval_phis_def] >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  gvs[EVERY_DEF] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
  >- (`eval_one_phi s h = eval_one_phi t h` by
        metis_tac[m2v_one_phi_agrees] >>
      Cases_on `eval_one_phi s h` >> gvs[] >>
      PairCases_on `x` >> gvs[] >>
      Cases_on `eval_phis s insts` >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `update_var x0 x1 t'` >>
      qpat_x_assum `SOME _ = eval_one_phi _ _` (assume_tac o SYM) >>
      simp[] >>
      irule m2v_phi_update >> simp[] >>
      qexists_tac `h` >> simp[] >>
      metis_tac[eval_one_phi_output_mem]) >>
  metis_tac[]
QED

Theorem m2v_phis_pvars[local]:
  !fn bb s s'.
    m2v_fresh_names_disjoint fn /\ MEM bb fn.fn_blocks /\
    m2v_pvars_set fn bb 0 s /\
    eval_phis s bb.bb_instructions = OK s' ==>
    m2v_pvars_set fn bb (phi_prefix_length bb.bb_instructions) s'
Proof
  rpt gen_tac >> strip_tac >>
  `!ao pv sz. MEM (ao,pv,sz) (m2v_promo_list fn) ==>
      lookup_var pv s' = lookup_var pv s` by
    (rpt strip_tac >> simp[lookup_var_def] >>
     irule eval_phis_flookup_not_phi_output >>
     qexists_tac `bb.bb_instructions` >> simp[] >>
     metis_tac[m2v_promo_list_in_fresh_vars,
               m2v_fresh_not_in_block_outputs, mem_flat_map_inst_outputs]) >>
  rw[m2v_pvars_set_def]
  >- (gvs[m2v_pvars_set_def] >> metis_tac[]) >>
  `(EL j bb.bb_instructions).inst_opcode = PHI` by
    (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
     rewrite_tac[EVERY_EL] >> disch_then (qspec_then `j` mp_tac) >>
     simp[LENGTH_TAKE_EQ, EL_TAKE, phi_prefix_length_le]) >> gvs[]
QED

Theorem m2v_phi_entry_package[local]:
  !fn bb s t s'.
    wf_ssa fn /\ m2v_fresh_names_disjoint fn /\ MEM bb fn.fn_blocks /\
    m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
    m2v_ao_undef_sync fn s t /\ m2v_pvars_set fn bb 0 t /\
    eval_phis s bb.bb_instructions = OK s' ==>
    ?t'. eval_phis t (m2v_bt fn bb).bb_instructions = OK t' /\
      m2v_inv_noix fn
        (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (t' with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
      m2v_non32_ok fn
        (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (t' with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
      m2v_ao_undef_sync fn
        (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (t' with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
      m2v_pvars_set fn bb (phi_prefix_length bb.bb_instructions)
        (t' with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[MEM_fn_insts]) >>
  drule_all m2v_eval_phis >> strip_tac >>
  qexists_tac `t'` >>
  simp[m2v_bt_instructions, m2v_rewrite_phis] >>
  conj_tac >- metis_tac[m2v_inv_noix_update_idx] >>
  conj_tac >- (gvs[m2v_non32_ok_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (gvs[m2v_ao_undef_sync_def, lookup_var_def] >> metis_tac[]) >>
  irule m2v_pvars_set_update_idx >>
  irule m2v_phis_pvars >> metis_tac[]
QED

(* A runner boundary carries reachability of successful post-PHI entries,
   not reachability of arbitrary pre-PHI states. The root vs stays fixed
   through the fuel induction and every block continuation. *)
Theorem m2v_run_blocks_correct[local]:
  !fuel ctx name fn vs fn' s t.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\
    ptr_discipline vs.vs_alloca_next ctx vs /\ raw_unit_memory_ok ctx vs /\
    m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
    m2v_return_size_bounded fn /\
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
    m2v_transform_function_checked fn = SOME fn' /\
    m2v_inv_noix fn s t /\ m2v_non32_ok fn s t /\
    m2v_ao_undef_sync fn s t /\ m2v_pvars_at_current fn t /\
    fn_reachable fn s.vs_current_bb /\
    (!u inst. enters_block fn s u /\ active_inst fn inst u ==>
      ?G tn. frame_reachable vs ctx [] [] G tn fn inst u) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (m2v_public_rel fn) (m2v_public_rel fn) (m2v_public_rel fn)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' t)
Proof
  Induct_on `fuel` >> rpt gen_tac >> strip_tac
  >- simp[run_blocks_def] >>
  `s.vs_current_bb = t.vs_current_bb` by gvs[m2v_inv_noix_def] >>
  `lookup_block t.vs_current_bb fn'.fn_blocks =
    OPTION_MAP (m2v_bt fn) (lookup_block s.vs_current_bb fn.fn_blocks)` by
    metis_tac[m2v_checked_lookup_block] >>
  once_rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `m2v_pvars_set fn bb 0 t` by
    metis_tac[m2v_pvars_at_current_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    metis_tac[fn_inst_wf_MEM, MEM_fn_insts, EVERY_MEM] >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`]
    eval_phis_ok_or_error_defs)
  >- (pop_assum strip_assume_tac >>
      rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      drule_all m2v_phi_entry_package >> strip_tac >>
      rename1 `eval_phis t (m2v_bt fn bb).bb_instructions = OK tp` >>
      simp[run_block_def, m2v_bt_instructions, m2v_rewrite_phis] >>
      Cases_on `get_instruction bb (phi_prefix_length bb.bb_instructions)`
      >- (simp[Once exec_block_def]) >>
      rename1 `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME inst` >>
      suspend "block") >>
  pop_assum strip_assume_tac >> simp[run_block_def]
QED

Resume m2v_run_blocks_correct[block]:
  qmatch_asmsub_abbrev_tac `m2v_inv_noix fn a b` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb a.vs_inst_idx = SOME inst` by
    (simp[Abbr `a`] >> metis_tac[]) >>
  `active_inst fn inst a` by
    (irule contextCodegenRelPropsTheory.lookup_instruction_active >> metis_tac[]) >>
  `enters_block fn s a` by
    (simp[contextCodegenRelTheory.enters_block_def, Abbr `a`] >> metis_tac[]) >>
  `?G tn. frame_reachable vs ctx [] [] G tn fn inst a` by metis_tac[] >>
  `m2v_promo_sizes_bounded fn` by
    gvs[m2v_transform_function_checked_def, AllCaseEqs()] >>
  `(?e. exec_block fuel ctx bb a = Error e) \/
   lift_result
     (\u v. m2v_inv_noix fn u v /\ m2v_non32_ok fn u v /\
             m2v_ao_undef_sync fn u v)
     (m2v_public_rel fn) (m2v_public_rel fn)
     (exec_block fuel ctx bb a) (exec_block fuel ctx (m2v_bt fn bb) b)` by
    (irule m2v_per_block_sim >> simp[Abbr `a`, Abbr `b`] >> metis_tac[]) >>
  gvs[] >>
  Cases_on `exec_block fuel ctx bb a` >>
  Cases_on `exec_block fuel ctx (m2v_bt fn bb) b` >>
  gvs[lift_result_def] >>
  rename1 `exec_block fuel ctx bb a = OK u` >>
  rename1 `exec_block fuel ctx (m2v_bt fn bb) b = OK v` >>
  `u.vs_halted = v.vs_halted /\ u.vs_current_bb = v.vs_current_bb` by
    gvs[m2v_inv_noix_def] >>
  Cases_on `v.vs_halted`
  >- (simp[lift_result_def] >>
      gvs[m2v_public_rel_def, m2v_inv_noix_def, m2v_equiv_def]) >>
  simp[] >> suspend "continue"
QED
Resume m2v_run_blocks_correct[continue]:
  `run_block fuel ctx bb s = OK u /\
   run_block fuel ctx (m2v_bt fn bb) t = OK v` by
    simp[run_block_def, m2v_bt_instructions, m2v_rewrite_phis,
         Abbr `a`, Abbr `b`] >>
  `m2v_pvars_at_current fn v` by
    (irule m2v_pvars_at_current_successor >> metis_tac[]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `MEM u.vs_current_bb (bb_succs bb)` by
    (irule venomExecPropsTheory.run_block_current_bb_in_succs >>
     metis_tac[wf_front_nonterm, bb_well_formed_def]) >>
  `fn_reachable fn u.vs_current_bb` by
    (irule fn_reachable_step >>
     qexists_tac `s.vs_current_bb` >>
     simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_fn_insts]) >>
  `!z j. enters_block fn u z /\ active_inst fn j z ==>
      ?G' tn'. frame_reachable vs ctx [] [] G' tn' fn j z` by
    (rpt strip_tac >> irule frame_reachable_exec_block_successor >>
     metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED
Finalise m2v_run_blocks_correct

(* Entry reachability supplies the source allocation and access invariants.
   Block continuation keeps promoted-variable initialization; terminal
   results expose only the public memory relation. *)
Theorem m2v_transform_function_correct:
  !fuel ctx name fn vs fn'.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\
    ptr_discipline vs.vs_alloca_next ctx vs /\
    raw_unit_memory_ok ctx vs /\
    m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
    m2v_return_size_bounded fn /\
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
    m2v_transform_function_checked fn = SOME fn' ==>
    (?e. run_function fuel ctx fn (vs with vs_prev_bb := NONE) = Error e) \/
    lift_result (m2v_public_rel fn) (m2v_public_rel fn) (m2v_public_rel fn)
      (run_function fuel ctx fn (vs with vs_prev_bb := NONE))
      (run_function fuel ctx fn' (vs with vs_prev_bb := NONE))
Proof
  rpt gen_tac >> strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn` by
    metis_tac[m2v_checked_entry_label] >>
  simp[run_function_def] >>
  Cases_on `fn_entry_label fn` >- simp[] >> simp[] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qmatch_goalsub_abbrev_tac `run_blocks fuel ctx fn cs` >>
  `o1_initial_state_ok cs` by gvs[o1_initial_state_ok_def, Abbr `cs`] >>
  `m2v_inv_noix fn cs cs` by metis_tac[m2v_initial_inv_noix] >>
  `m2v_fresh_undef fn cs` by metis_tac[m2v_initial_fresh_undef] >>
  `m2v_non32_ok fn cs cs /\ m2v_ao_undef_sync fn cs cs` by
    metis_tac[m2v_non32_ok_refl, m2v_ao_undef_sync_refl] >>
  `m2v_pvars_at_current fn cs` by
    (rw[m2v_pvars_at_current_def] >> irule m2v_entry_pvars_set >>
     gvs[Abbr `cs`]) >>
  `fn_reachable fn cs.vs_current_bb` by
    (simp[fn_reachable_def, Abbr `cs`] >> metis_tac[relationTheory.RTC_REFL]) >>
  `!u inst. enters_block fn cs u /\ active_inst fn inst u ==>
      ?G tn. frame_reachable vs ctx [] [] G tn fn inst u` by
    (rpt strip_tac >> qexistsl [`FEMPTY`, `entry_taint`] >>
     irule frame_reachable_entry >> simp[] >>
     gvs[Abbr `cs`]) >>
  irule m2v_run_blocks_correct >> metis_tac[]
QED

(* ===== Structural obligation: supply-aware transform keeps wf_function =====

   m2v_transform_function_supply_raw rewrites exactly like m2v_bt up to inst_ids,
   and the only new id (the mstore before a promoted return) comes from the
   supply, above every id of the input function. This independent structural
   result is retained for the supply-aware compiler pipeline. The semantic
   wrapper above uses the checked transform directly and needs no transformed
   instruction-ID distinctness premise. *)

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
    wf_function (FST (m2v_transform_function_supply_raw s fn))
Proof
  rpt strip_tac >> simp[m2v_transform_function_supply_raw_def] >>
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
