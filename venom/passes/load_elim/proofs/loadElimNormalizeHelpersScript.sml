Theory loadElimNormalizeHelpers
Ancestors
  dfgDefs venomState finite_map pred_set

Definition le_chain_valid_def:
  le_chain_valid (dfg : dfg_analysis) visited (Var v) s =
    (if MEM v visited then T
     else case FLOOKUP dfg.dfg_defs v of
       SOME inst =>
         if inst.inst_opcode = ASSIGN then
           (case inst.inst_operands of
              [src] => lookup_var v s = eval_operand src s /\
                       le_chain_valid dfg (v :: visited) src s
            | _ => T)
         else T
     | NONE => T) /\
  le_chain_valid dfg visited op s = T
Termination
  WF_REL_TAC `measure (\(dfg, visited, op, s).
    CARD (FDOM dfg.dfg_defs DIFF set visited))` >>
  rw[Excl "CARD_DIFF"] >>
  irule pred_setTheory.CARD_PSUBSET >> conj_tac
  >- simp[pred_setTheory.FINITE_DIFF, finite_mapTheory.FDOM_FINITE] >>
  simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF,
       pred_setTheory.EXTENSION] >>
  qexists_tac `v` >> fs[finite_mapTheory.FLOOKUP_DEF]
End

Theorem le_chain_valid_frame:
  !dfg visited op s t.
    (!v. lookup_var v t = lookup_var v s) /\
    t.vs_labels = s.vs_labels ==>
    (le_chain_valid dfg visited op t = le_chain_valid dfg visited op s)
Proof
  ho_match_mp_tac normalize_operand_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Ntimes le_chain_valid_def 2] >>
      Cases_on `MEM dfg' visited` >> simp[] >>
      Cases_on `FLOOKUP dfg.dfg_defs dfg'` >> simp[] >>
      rename1 `FLOOKUP _ _ = SOME inst` >>
      Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
      Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `t'` >> simp[] >>
      `eval_operand h t = eval_operand h s` by
        (Cases_on `h` >> simp[eval_operand_def]) >>
      metis_tac[]) >>
  simp[le_chain_valid_def]
QED

Theorem le_chain_valid_eval:
  !dfg visited op s. le_chain_valid dfg visited op s ==>
    eval_operand (normalize_operand dfg visited op) s = eval_operand op s
Proof
  ho_match_mp_tac normalize_operand_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      simp[Once normalize_operand_def, Once le_chain_valid_def] >>
      IF_CASES_TAC >- simp[] >>
      Cases_on `FLOOKUP dfg.dfg_defs dfg'` >> simp[] >>
      rename1 `FLOOKUP _ _ = SOME inst` >>
      IF_CASES_TAC >- (
        Cases_on `inst.inst_operands` >> simp[] >>
        Cases_on `t` >> simp[] >>
        rpt strip_tac >>
        first_x_assum (qspecl_then [`inst`, `h`, `[]`] mp_tac) >>
        simp[eval_operand_def]) >>
      simp[]) >>
  simp[normalize_operand_def, le_chain_valid_def]
QED
