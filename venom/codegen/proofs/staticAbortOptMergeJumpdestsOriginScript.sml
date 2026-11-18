Theory staticAbortOptMergeJumpdestsOrigin
Ancestors
  asmOptMergeJumpdests asmSplice asmSymBridge asmToBytecodeProofs
  spillWordBounds asmSymSem asmOptimizer asmWf asmSem symbolResolve
  words indexedLists rich_list list finite_map

(* Re-execute the actual producer, rather than relabelling a concrete word.
   The inverse lookup is partial: the stub's reference can name data. *)
Theorem merge_rename_reference_step:
  !p pre x y next third tail i l.
    let L = \r. SND (compute_label_offsets r) in
    let B = build_offset_to_pc in
    let I = EL i p in
    let q = MAP (rename_push_label x y) p in
    let a = if I = AsmPushLabel x then y else l in
    let delta = case I of AsmPushOfst _ d => d | _ => 0 in
    p = pre ++ [AsmLabel x; next; third] ++ tail /\
    ((next = AsmLabel y /\ y <> x) \/
     (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
    asm_static_wf p /\ i < LENGTH p /\
    (I = AsmPushLabel l \/ (?d. I = AsmPushOfst l d) \/ I = AsmDataLabel l) ==>
    ?off.
      FLOOKUP (L q) a = SOME off /\ FLOOKUP (L p) a = SOME off /\
      off < dimword(:256) /\ FLOOKUP (B q) off = FLOOKUP (B p) off /\
      (EL i q = AsmPushLabel a \/ EL i q = AsmPushOfst a delta) /\
      (I = AsmPushLabel x /\ next = AsmLabel y ==>
       FLOOKUP (B q) off = SOME (LENGTH pre + 1)) /\
      (!s. s.as_pc = i ==>
        asm_steps (L q) (B q) q 1 s =
          AsmOK (s with <|as_pc := i+1;
                          as_stack := (n2w (off+delta):bytes32)::s.as_stack|>))
Proof
  rpt gen_tac >> rewrite_tac[LET_THM] >> BETA_TAC >>
  DISCH_THEN (CONJUNCTS_THEN2 (mk_asm "site") (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  qabbrev_tac `q = MAP (rename_push_label x y) p` >>
  qabbrev_tac `a = if EL i p = AsmPushLabel x then y else l` >>
  (* Both maps fold over unchanged layout information. *)
  `compute_label_offsets q = compute_label_offsets p` by
    (simp[Abbr `q`, compute_label_offsets_def, FOLDL_MAP] >>
     irule FOLDL_CONG >> simp[] >> qx_gen_tac `inst` >> qx_gen_tac `acc` >> disch_tac >>
     PairCases_on `acc` >> Cases_on `inst` >>
     simp[rename_push_label_def, asm_inst_size_def] >> IF_CASES_TAC >> simp[asm_inst_size_def]) >>
  `build_offset_to_pc q = build_offset_to_pc p` by
    (`MAPi (\j inst. (j,inst)) q =
      MAP (\(j,inst). (j,rename_push_label x y inst)) (MAPi (\j inst. (j,inst)) p)` by
       simp[LIST_EQ_REWRITE, Abbr `q`, EL_MAP] >>
     rewrite_tac[build_offset_to_pc_def] >>
     qpat_assum `MAPi _ q = MAP _ _` (fn th => rewrite_tac[th, FOLDL_MAP]) >> AP_TERM_TAC >>
     irule FOLDL_CONG >> simp[] >> qx_gen_tac `ji` >> qx_gen_tac `acc` >> disch_tac >>
     PairCases_on `acc` >> PairCases_on `ji` >> Cases_on `ji1` >>
     simp[rename_push_label_def, asm_inst_size_def] >> IF_CASES_TAC >> simp[asm_inst_size_def]) >>
  `a IN FDOM (SND (compute_label_offsets p))` by
    (simp[compute_label_offsets_def, clo_step_eq] >> irule clo_FDOM >>
     `MEM (AsmLabel a) p \/ MEM (AsmDataHeader a) p` suffices_by simp[] >>
     `MEM l (asm_label_refs p)` by
       (simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        qexists `EL i p` >>
        `MEM (EL i p) p` by metis_tac[MEM_EL] >>
        qpat_assum `EL i p = _ \/ _` STRIP_ASSUME_TAC >> simp[]) >>
     `(MEM (AsmLabel y) p \/ MEM y (asm_label_refs p))` suffices_by
       (simp[Abbr `a`] >> fs[asm_static_wf_def] >> metis_tac[]) >>
     qpat_assum `(next = _ /\ _) \/ _` STRIP_ASSUME_TAC
     >- asm "site" (fn th => simp[th]) >>
     disj2_tac >> simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexists `AsmPushLabel y` >> asm "site" (fn th => simp[th])) >>
  `?off. FLOOKUP (SND (compute_label_offsets p)) a = SOME off` by simp[FLOOKUP_DEF] >>
  `off < dimword(:256)` by
    (`LENGTH (encode_num_bytes off) <= symbol_size` by
       (fs[asm_static_wf_def, asm_encoding_wf_def, pairTheory.UNCURRY] >>
        qpat_assum `!lbl off. FLOOKUP _ lbl = SOME off ==> _` drule >> simp[]) >>
     drule encode_num_bytes_length_bound >>
     simp[symbol_size_def, dimword_def] >> decide_tac) >>
  `~(EL i p = AsmDataLabel l)` by
    (strip_tac >> `MEM (AsmDataLabel l) p` by metis_tac[EL_MEM] >>
     drule (cj 4 (iffLR asm_static_wf_def)) >> disch_then (qspec_then `l` mp_tac) >> simp[]) >>
  `i < LENGTH q /\ EL i q = rename_push_label x y (EL i p)` by simp[Abbr `q`, EL_MAP] >>
  `!s. s.as_pc = i ==>
     asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q 1 s =
       AsmOK (s with <|as_pc := i+1;
         as_stack := n2w (off + (case EL i p of AsmPushOfst _ d => d | _ => 0)) :: s.as_stack|>)` by
    (asm_x "site" kall_tac >> qpat_x_assum `(next = _ /\ _) \/ _` kall_tac >>
     rpt strip_tac >> qpat_x_assum `EL i p = _ \/ _` STRIP_ASSUME_TAC >>
     rewrite_tac[numLib.num_CONV ``1:num``] >>
     Cases_on `EL i p = AsmPushLabel x` >>
     gvs[Abbr `a`, asm_steps_def, rename_push_label_def, asm_step_def, asm_next_def]) >>
  `(EL i p = AsmPushLabel x /\ next = AsmLabel y ==>
    FLOOKUP (build_offset_to_pc q) off = SOME (LENGTH pre+1))` by
    (strip_tac >>
     asm "site" (assume_tac o ONCE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
     `asm_labels_unique p` by (drule (cj 1 (iffLR asm_static_wf_def)) >> simp[]) >>
     `~MEM (AsmLabel y) pre` by
       (irule asm_labels_unique_append_not_mem >>
        qexists `[AsmLabel x;next;third] ++ tail` >>
        conj_tac >- metis_tac[] >> simp[]) >>
     `x <> y` by (qpat_assum `(next = _ /\ _) \/ _` STRIP_ASSUME_TAC >> fs[]) >>
     `INDEX_OF (AsmLabel y) p = SOME (LENGTH pre+1)` by
       simp[INDEX_OF_APPEND, INDEX_OF_CONS, APPEND_ASSOC] >>
     `a = y` by simp[Abbr `a`] >>
     drule_all asm_static_wf_code_label >> metis_tac[optionTheory.SOME_11]) >>
  `(EL i q = AsmPushLabel a \/ EL i q = AsmPushOfst a
    (case EL i p of AsmPushOfst _ d => d | _ => 0))` by
    (asm_x "site" kall_tac >> qpat_x_assum `(next = _ /\ _) \/ _` kall_tac >>
     qpat_x_assum `EL i p = _ \/ _` STRIP_ASSUME_TAC >>
     Cases_on `EL i p = AsmPushLabel x` >> gvs[Abbr `a`, rename_push_label_def]) >>
  qexists `off` >> simp[]
  >> (gvs[])
QED
