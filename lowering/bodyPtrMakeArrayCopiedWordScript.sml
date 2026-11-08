(* A copied external word may carry taint.  These endpoints deliberately
   retain that taint, rather than asserting clean padding or initialization. *)
Theory bodyPtrMakeArrayCopiedWord
Ancestors
  bodyPtrMakeArrayCopyStep typedCopyPtr fragGasPathPtr fragGasPath
  venomExecSemantics venomState valueEncodingProps ptrDiscipline ptrSafeRun

Theorem external_word_store_path:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK (update_var tmp w s) /\
  eval_operand src s = SOME key /\ tmp <> dst /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst sid MSTORE [Var dst; Var tmp] []) /\
  sm = ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  Gm = step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s) /\
  tnm = step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG Gm (mk_inst sid MSTORE [Var dst; Var tmp] [])
      (mstore (w2n a) w sm))
    (step_taint (mk_inst sid MSTORE [Var dst; Var tmp] []) sm
      (mstore (w2n a) w sm) tnm)
    (OK ((mstore (w2n a) w sm) with vs_inst_idx := SUC sm.vs_inst_idx))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tnm (OK sm)` by
    (gvs[] >> irule external_load_ptr_path >> simp[] >> metis_tac[]) >>
  `ptr_covers Gm tnm dst sm 32` by
    (gvs[] >> irule external_load_old_coverage >> simp[] >> metis_tac[]) >>
  `lookup_var dst sm = SOME a /\ eval_operand (Var tmp) sm = SOME w /\
   ~sm.vs_halted /\
   lookup_block sm.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb sm.vs_inst_idx =
     SOME (mk_inst sid MSTORE [Var dst; Var tmp] [])` by
    gvs[lookup_var_def, update_var_def, eval_operand_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  `gas_path_ptr D 0 ctx fn PG Gm tnm sm 0
    (step_prov PG Gm (mk_inst sid MSTORE [Var dst; Var tmp] [])
      (mstore (w2n a) w sm))
    (step_taint (mk_inst sid MSTORE [Var dst; Var tmp] []) sm
      (mstore (w2n a) w sm) tnm)
    (OK ((mstore (w2n a) w sm) with vs_inst_idx := SUC sm.vs_inst_idx))` by
    (irule mstore_raw_ptr_path >> simp[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem external_word_store_frame:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME key /\ tmp <> dst /\
  lookup_var dst s = SOME a /\
  sm = ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  Gm = step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s) /\
  tnm = step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn /\
  Gf = step_prov PG Gm (mk_inst sid MSTORE [Var dst; Var tmp] [])
    (mstore (w2n a) w sm) /\
  tnf = step_taint (mk_inst sid MSTORE [Var dst; Var tmp] []) sm
    (mstore (w2n a) w sm) tnm /\
  sf = ((mstore (w2n a) w sm) with vs_inst_idx := SUC sm.vs_inst_idx) ==>
  Gf = DRESTRICT G (COMPL {tmp}) /\
  tnf.t_mem =
    (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}) UNION
    {w2n a + k | k IN
      (if opc = SLOAD then key_taint tn.t_stor key
       else if opc = TLOAD then key_taint tn.t_trans key else {})} /\
  mem_word_at (w2n a) sf.vs_memory = w /\
  lookup_var dst sf = SOME a /\
  sf.vs_current_bb = s.vs_current_bb /\
  sf.vs_inst_idx = s.vs_inst_idx + 2 /\
  (!p n. tmp <> p /\ ptr_covers G tn p s n ==>
    ptr_covers Gf tnf p sf n) /\
  (!i. i < w2n a \/ w2n a + 32 <= i ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
    sf.vs_memory s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var dst sm = SOME a /\ eval_operand (Var tmp) sm = SOME w` by
    gvs[lookup_var_def, update_var_def, eval_operand_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tnm`, `sid`, `PG`, `Gm`] strip_assume_tac) >>
  `Gm = DRESTRICT G (COMPL {tmp}) /\
   tnm.t_mem = tn.t_mem /\
   op_taint tnm (Var tmp) =
     (if opc = SLOAD then key_taint tn.t_stor key
      else if opc = TLOAD then key_taint tn.t_trans key else {})` by
    metis_tac[external_load_ghost_frame, external_load_output_ghost] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qpat_x_assum `_.t_mem = _ DIFF _ UNION _` mp_tac >> simp[]) >>
  conj_tac >- (simp[] >> metis_tac[mstore_mem_word_at_same]) >>
  conj_tac >- gvs[mstore_def, lookup_var_def, update_var_def,
                  finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- gvs[mstore_def, update_var_def] >>
  conj_tac >- gvs[mstore_def] >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_assum `Gf = _` SUBST1_TAC >> qpat_assum `tnf = _` SUBST1_TAC >>
     qpat_assum `sf = _` SUBST1_TAC >>
     irule mstore_raw_old_coverage >> simp[] >>
     `ptr_covers Gm tnm p sm n` suffices_by metis_tac[] >>
     gvs[] >> irule external_load_old_coverage >> simp[] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> qpat_assum `tnf = _` SUBST1_TAC >>
     qpat_assum `tnm.t_mem = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule mstore_raw_outside_taint >> simp[] >>
     gvs[key_taint_def] >> rpt strip_tac >> gvs[]) >>
  `sm.vs_memory = s.vs_memory` by simp[update_var_def] >>
  `sf.vs_memory = (mstore (w2n a) w sm).vs_memory` by simp[] >>
  metis_tac[mstore_memory_frame]
QED
