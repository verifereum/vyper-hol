Theory algebraicOptChainProofs
Ancestors
  algebraicOptMainShapeProofs algebraicOptDefs venomInst venomExecSemantics
Libs
  listTheory arithmeticTheory

Definition ao_chain_edges_def:
  ao_chain_edges insts chn <=>
    !j. SUC j < LENGTH chn ==>
      ?prod y. MEM prod insts /\ prod.inst_opcode = ISZERO /\
        prod.inst_operands = [EL j chn] /\ prod.inst_outputs = [y] /\
        EL (SUC j) chn = Var y
End

Theorem ao_chain_edges_mono:
  (!i. MEM i xs ==> MEM i ys) /\ ao_chain_edges xs chn ==>
  ao_chain_edges ys chn
Proof
  simp[ao_chain_edges_def] >> metis_tac[]
QED

Theorem ao_chain_edges_singleton[simp]:
  ao_chain_edges insts [op]
Proof
  simp[ao_chain_edges_def]
QED

Theorem ao_chain_edges_snoc:
  chn <> [] /\ LAST chn = inp /\ ao_chain_edges insts chn /\
  MEM prod insts /\ prod.inst_opcode = ISZERO /\
  prod.inst_operands = [inp] /\ prod.inst_outputs = [y] ==>
  ao_chain_edges insts (SNOC (Var y) chn)
Proof
  strip_tac >> simp[ao_chain_edges_def, LENGTH_SNOC] >>
  rpt strip_tac >>
  Cases_on `SUC j < LENGTH chn`
  >- (simp[EL_SNOC] >> fs[ao_chain_edges_def] >> metis_tac[]) >>
  `SUC j = LENGTH chn` by decide_tac >>
  `j < LENGTH chn` by decide_tac >>
  simp[EL_SNOC, EL_LENGTH_SNOC] >>
  `EL j chn = LAST chn` by
    (Cases_on `chn` >> gvs[LAST_EL] >> decide_tac) >>
  metis_tac[]
QED

Theorem ao_chain_extend_lookup:
  (!v chn. ALOOKUP targets v = SOME chn ==>
     chn <> [] /\ LAST chn = Var v /\ ao_chain_edges insts chn) /\
  MEM prod insts /\ prod.inst_opcode = ISZERO /\
  prod.inst_operands = [inp] /\ prod.inst_outputs = [y] ==>
  ao_chain_edges insts (SNOC (Var y)
    (case inp of Var v => (case ALOOKUP targets v of
       SOME chn => chn | NONE => [inp]) | _ => [inp]))
Proof
  strip_tac >> irule ao_chain_edges_snoc >> simp[] >>
  Cases_on `inp` >> simp[]
  >- metis_tac[]
  >- (Cases_on `ALOOKUP targets s` >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ao_compute_iszero_step_witnesses:
  (!v chn. ALOOKUP targets v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges insts chn) ==>
  !v chn. ALOOKUP (ao_compute_iszero_step targets inst) v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges (inst::insts) chn
Proof
  strip_tac >>
  `!v chn. ALOOKUP targets v = SOME chn ==>
     chn <> [] /\ LAST chn = Var v /\ ao_chain_edges (inst::insts) chn` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
     irule ao_chain_edges_mono >> qexists_tac `insts` >> simp[]) >>
  reverse (Cases_on `inst.inst_opcode = ISZERO`)
  >- (simp[ao_compute_iszero_step_def] >> metis_tac[]) >>
  simp[ao_compute_iszero_step_def] >>
  Cases_on `inst.inst_operands` >> simp[]
  >- metis_tac[] >>
  Cases_on `t` >> simp[]
  >- (Cases_on `inst.inst_outputs` >> simp[]
      >- metis_tac[] >>
      Cases_on `t` >> simp[]
      >- (rpt strip_tac >> gvs[AllCaseEqs()] >>
          metis_tac[ao_chain_extend_lookup, MEM]) >>
      metis_tac[]) >>
  Cases_on `inst.inst_outputs` >> simp[]
  >- metis_tac[] >>
  Cases_on `t` >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_step_witnesses_in:
  MEM inst all_insts /\
  (!v chn. ALOOKUP targets v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn) ==>
  !v chn. ALOOKUP (ao_compute_iszero_step targets inst) v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn
Proof
  strip_tac >> drule ao_compute_iszero_step_witnesses >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  irule ao_chain_edges_mono >> qexists_tac `inst::all_insts` >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_fold_witnesses:
  !insts targets.
  EVERY (\i. MEM i all_insts) insts /\
  (!v chn. ALOOKUP targets v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn) ==>
  !v chn. ALOOKUP (FOLDL ao_compute_iszero_step targets insts) v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn
Proof
  Induct
  >- (simp[] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  match_mp_tac ao_compute_iszero_step_witnesses_in >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_targets_witnesses:
  ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn ==>
  chn <> [] /\ LAST chn = Var v /\ ao_chain_edges insts chn
Proof
  mp_tac (Q.SPECL [`insts`, `[]`]
    (Q.INST [`all_insts` |-> `insts`] ao_compute_iszero_fold_witnesses)) >>
  simp[EVERY_MEM, ao_compute_iszero_targets_def] >> metis_tac[]
QED

Theorem ao_compute_iszero_targets_endpoint:
  ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn ==>
  chn <> [] /\ LAST chn = Var v
Proof
  metis_tac[ao_compute_iszero_targets_witnesses]
QED

Theorem ao_compute_iszero_targets_adjacent:
  ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn /\
  SUC j < LENGTH chn ==>
  ?prod y. MEM prod insts /\ prod.inst_opcode = ISZERO /\
    prod.inst_operands = [EL j chn] /\ prod.inst_outputs = [y] /\
    EL (SUC j) chn = Var y
Proof
  metis_tac[ao_compute_iszero_targets_witnesses, ao_chain_edges_def]
QED

Definition ao_word_chain_def:
  ao_word_chain (ws : bytes32 list) <=>
    !j. SUC j < LENGTH ws ==>
      EL (SUC j) ws = (if EL j ws = 0w then 1w else 0w)
End

Theorem ao_word_chain_value:
  !j. ao_word_chain ws /\ j < LENGTH ws ==>
  EL j ws =
    if j = 0 then HD ws
    else if j MOD 2 = 0 then (if HD ws = 0w then 0w else 1w)
    else (if HD ws = 0w then 1w else 0w)
Proof
  Induct
  >- simp[] >>
  rpt strip_tac >>
  `j < LENGTH ws` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  `EL (SUC j) ws = (if EL j ws = 0w then 1w else 0w)` by
    metis_tac[ao_word_chain_def] >>
  Cases_on `j = 0` >> gvs[] >>
  Cases_on `j MOD 2 = 0`
  >- (`SUC j MOD 2 <> 0` by (rewrite_tac[ADD1] >> once_rewrite_tac[GSYM MOD_PLUS] >> simp[]) >>
      Cases_on `HD ws = 0w` >> gvs[]) >>
  `j MOD 2 < 2` by simp[] >>
  `j MOD 2 = 1` by decide_tac >>
  `SUC j MOD 2 = 0` by
    (rewrite_tac[ADD1] >> once_rewrite_tac[GSYM MOD_PLUS] >> simp[]) >>
  Cases_on `HD ws = 0w` >> gvs[]
QED

Theorem ao_word_chain_same_parity:
  ao_word_chain ws /\ i < LENGTH ws /\ j < LENGTH ws /\
  i MOD 2 = j MOD 2 /\ 0 < i /\ 0 < j ==>
  EL i ws = EL j ws
Proof
  strip_tac >>
  qspec_then `i` mp_tac ao_word_chain_value >>
  qspec_then `j` mp_tac ao_word_chain_value >> simp[]
QED

Theorem ao_word_chain_truth_parity:
  ao_word_chain ws /\ i < LENGTH ws /\ j < LENGTH ws /\
  i MOD 2 = j MOD 2 ==>
  (EL i ws = 0w <=> EL j ws = 0w)
Proof
  strip_tac >>
  qspec_then `i` mp_tac ao_word_chain_value >>
  qspec_then `j` mp_tac ao_word_chain_value >> simp[] >>
  Cases_on `i = 0` >> Cases_on `j = 0` >>
  Cases_on `HD ws = 0w` >> gvs[]
QED

Theorem ao_word_chain_keep_exact:
  ao_word_chain ws /\ d = LENGTH ws - 1 /\ k = 2 - d MOD 2 /\
  k < d /\ k < LENGTH ws ==>
  EL k ws = LAST ws
Proof
  rpt strip_tac >>
  `d MOD 2 < 2` by simp[] >>
  `0 < LENGTH ws /\ d < LENGTH ws /\ 0 < d /\ 0 < k` by decide_tac >>
  `k MOD 2 = d MOD 2` by
    (Cases_on `d MOD 2 = 0` >> gvs[] >>
     `d MOD 2 = 1` by decide_tac >> gvs[]) >>
  `LAST ws = EL d ws` by (Cases_on `ws` >> gvs[LAST_EL]) >>
  metis_tac[ao_word_chain_same_parity]
QED

Theorem ao_word_chain_keep_truth:
  ao_word_chain ws /\ d = LENGTH ws - 1 /\ k = d MOD 2 /\
  k < d /\ k < LENGTH ws ==>
  (EL k ws = 0w <=> LAST ws = 0w)
Proof
  rpt strip_tac >>
  `0 < LENGTH ws /\ d < LENGTH ws` by decide_tac >>
  `k MOD 2 = d MOD 2` by simp[] >>
  `LAST ws = EL d ws` by (Cases_on `ws` >> gvs[LAST_EL]) >>
  metis_tac[ao_word_chain_truth_parity]
QED

Theorem ao_chain_last_eval:
  chn <> [] /\ LENGTH ws = LENGTH chn /\
  (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) ==>
  eval_operand (LAST chn) s = SOME (LAST ws)
Proof
  strip_tac >>
  `LENGTH chn - 1 < LENGTH chn` by (Cases_on `chn` >> gvs[]) >>
  first_x_assum drule >>
  Cases_on `chn` >> Cases_on `ws` >> gvs[LAST_EL]
QED

Theorem ao_resolve_iszero_op_eval_exact:
  ALOOKUP targets v = SOME chn /\ chn <> [] /\ LAST chn = Var v /\
  LENGTH ws = LENGTH chn /\ ao_word_chain ws /\
  (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
  use_opcode <> JNZ /\ use_opcode <> ASSERT /\ use_opcode <> ASSERT_UNREACHABLE ==>
  eval_operand (ao_resolve_iszero_op targets use_opcode (Var v)) s =
  eval_operand (Var v) s
Proof
  strip_tac >>
  `eval_operand (Var v) s = SOME (LAST ws)` by
    metis_tac[ao_chain_last_eval] >>
  simp[ao_resolve_iszero_op_def] >>
  Cases_on `use_opcode = ISZERO` >> simp[] >>
  reverse (Cases_on `2 - (LENGTH chn - 1) MOD 2 < LENGTH chn - 1 /\
                    2 - (LENGTH chn - 1) MOD 2 < LENGTH chn`)
  >- simp[] >>
  gvs[] >>
  `EL (2 - (LENGTH chn - 1) MOD 2) ws = LAST ws` by
    (irule ao_word_chain_keep_exact >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ao_resolve_iszero_op_eval_truth:
  ALOOKUP targets v = SOME chn /\ chn <> [] /\ LAST chn = Var v /\
  LENGTH ws = LENGTH chn /\ ao_word_chain ws /\
  (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws)) /\
  (use_opcode = JNZ \/ use_opcode = ASSERT \/ use_opcode = ASSERT_UNREACHABLE) ==>
  ?w. eval_operand (ao_resolve_iszero_op targets use_opcode (Var v)) s = SOME w /\
      (w = 0w <=> LAST ws = 0w)
Proof
  strip_tac >>
  `eval_operand (Var v) s = SOME (LAST ws)` by
    metis_tac[ao_chain_last_eval] >>
  simp[ao_resolve_iszero_op_def] >>
  reverse (Cases_on `(LENGTH chn - 1) MOD 2 < LENGTH chn - 1 /\
                    (LENGTH chn - 1) MOD 2 < LENGTH chn`)
  >- simp[] >>
  gvs[] >>
  irule ao_word_chain_keep_truth >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_step_offset:
  !targets inst.
    ao_compute_iszero_step targets (ao_handle_offset_inst inst) =
    ao_compute_iszero_step targets inst
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  gvs[ao_compute_iszero_step_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  rename1 `inst.inst_operands = Label lbl::Lit w::rest` >>
  Cases_on `rest` >> simp[]
QED

Theorem ao_compute_iszero_fold_offset[local]:
  !insts targets.
    FOLDL ao_compute_iszero_step targets (MAP ao_handle_offset_inst insts) =
    FOLDL ao_compute_iszero_step targets insts
Proof
  Induct >> simp[ao_compute_iszero_step_offset]
QED

Theorem ao_compute_iszero_targets_offset:
  !insts. ao_compute_iszero_targets (MAP ao_handle_offset_inst insts) =
          ao_compute_iszero_targets insts
Proof
  simp[ao_compute_iszero_targets_def, ao_compute_iszero_fold_offset]
QED

Theorem ao_compute_iszero_step_min_length[local]:
  (!v chn. ALOOKUP targets v = SOME chn ==> 1 < LENGTH chn) ==>
  !v chn. ALOOKUP (ao_compute_iszero_step targets inst) v = SOME chn ==>
    1 < LENGTH chn
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ISZERO` >> simp[ao_compute_iszero_step_def]
  >- (Cases_on `inst.inst_operands` >> simp[]
      >- metis_tac[] >>
      Cases_on `t` >> simp[]
      >- (Cases_on `inst.inst_outputs` >> simp[]
          >- metis_tac[] >>
          Cases_on `t` >> simp[]
          >- (rpt strip_tac >> gvs[AllCaseEqs(), LENGTH_SNOC]
              >- (Cases_on `h` >> simp[] >>
                  Cases_on `ALOOKUP targets s` >> simp[] >>
                  first_x_assum drule >> decide_tac) >>
              metis_tac[]) >> metis_tac[]) >>
      Cases_on `inst.inst_outputs` >> simp[]
      >- metis_tac[] >>
      Cases_on `t` >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ao_compute_iszero_fold_min_length[local]:
  !insts targets.
    (!v chn. ALOOKUP targets v = SOME chn ==> 1 < LENGTH chn) ==>
    !v chn. ALOOKUP (FOLDL ao_compute_iszero_step targets insts) v = SOME chn ==>
      1 < LENGTH chn
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  metis_tac[ao_compute_iszero_step_min_length]
QED

Theorem ao_compute_iszero_targets_min_length:
  !insts v chn. ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn ==>
    1 < LENGTH chn
Proof
  gen_tac >>
  qspecl_then [`insts`, `[]`] mp_tac ao_compute_iszero_fold_min_length >>
  simp[ao_compute_iszero_targets_def]
QED
