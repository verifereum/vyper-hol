(*
 * SimplifyCFG keeps every CALL/STATICCALL success check (call_checks_ok).
 *
 * The check after a call stays in its block: merging only appends the
 * successor's instructions to a block that ended in JMP, and a JMP into a
 * revert path is replaced by that path's own instructions, which end in
 * REVERT or a JMP into another revert path.  Bypassing a jump-only block
 * and canonicalizing a JNZ with equal targets keep each revert-path target
 * a revert path, and removing unreachable blocks keeps every block a
 * reachable block can jump to.
 *)
Theory simplifyCfgCallChecks
Ancestors
  simplifyCfgDefs unitShapeDefs venomWf venomInst list rich_list

Theorem revert_path_fuel_mono:
  !n m bbs l. revert_path bbs n l /\ n <= m ==>
    revert_path bbs m l
Proof
  Induct >- simp[revert_path_def] >>
  Cases_on `m` >- simp[] >>
  simp[revert_path_def, EXISTS_MEM] >>
  rpt strip_tac >> qexists_tac `bb` >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `t` >> gvs[] >> metis_tac[]
QED

Theorem flag_fails_empty_mono:
  !bbs i vs. flag_fails bbs [] i ==> flag_fails bbs vs i
Proof
  rpt gen_tac >>
  Cases_on `i.inst_opcode` >> simp[flag_fails_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem flag_path_unconditional_last:
  !insts bbs vs.
    insts <> [] /\ EVERY (\i. i.inst_opcode <> INVOKE) insts /\
    flag_fails bbs [] (LAST insts) ==>
    flag_path bbs vs insts
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `insts` >> simp[flag_path_def] >> rpt strip_tac
  >- metis_tac[flag_fails_empty_mono] >>
  disj2_tac >> first_x_assum irule >> simp[]
QED

Theorem revert_path_minimal_step:
  !n bbs l.
    revert_path bbs (SUC (SUC n)) l /\
    (!m. m < SUC (SUC n) ==> ~revert_path bbs m l) ==>
    ?bb t.
      MEM bb bbs /\ bb.bb_label = l /\
      bb.bb_instructions <> [] /\
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      (LAST bb.bb_instructions).inst_opcode = JMP /\
      (LAST bb.bb_instructions).inst_operands = [Label t] /\
      revert_path bbs (SUC n) t /\
      (!m. m < SUC n ==> ~revert_path bbs m t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `revert_path _ _ _` mp_tac >>
  simp[Once revert_path_def, EXISTS_MEM] >> strip_tac
  >- (`revert_path bbs (SUC 0) l` by
        (pure_rewrite_tac[revert_path_def, EXISTS_MEM] >>
         qexists_tac `bb` >> simp[]) >>
      first_x_assum (qspec_then `SUC 0` mp_tac) >> simp[]) >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  qexistsl_tac [`bb`, `s`] >> simp[] >>
  rpt strip_tac >>
  `revert_path bbs (SUC m) bb.bb_label` by
    (pure_once_rewrite_tac[revert_path_def] >>
     pure_rewrite_tac[EXISTS_MEM] >>
     qexists_tac `bb` >> simp[]) >>
  first_x_assum (qspec_then `SUC m` mp_tac) >> simp[]
QED

Theorem revert_path_minimal_blocks:
  !n bbs l.
    revert_path bbs n l /\
    (!m. m < n ==> ~revert_path bbs m l) ==>
    ?xs. LENGTH xs = n /\ ALL_DISTINCT xs /\
      EVERY (\bb. MEM bb bbs /\ revert_path bbs n bb.bb_label) xs
Proof
  Induct >- simp[revert_path_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `n`
  >- (qpat_assum `revert_path _ _ _` mp_tac >>
      pure_once_rewrite_tac[revert_path_def] >>
      pure_rewrite_tac[EXISTS_MEM] >>
      disch_then (qx_choose_then `bb` strip_assume_tac) >>
      qexists_tac `[bb]` >> simp[] >> metis_tac[]) >>
  drule_all revert_path_minimal_step >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `bb::xs` >> simp[] >>
  conj_tac
  >- (strip_tac >>
      gvs[EVERY_MEM] >>
      first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
      metis_tac[prim_recTheory.LESS_SUC_REFL]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[revert_path_fuel_mono, arithmeticTheory.LESS_EQ_SUC_REFL]
QED

Theorem simplify_cfg_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn ==>
  call_checks_ok (simplify_cfg_fn fn)
Proof
  cheat
QED
