Theory staticAbortOptMergeJumpdestsLayout
Ancestors
  asmOptMergeJumpdests asmSymBridge asmSymSem asmOptimizer asmWf asmIR
  fnPlanPlaceRevertPostamble asmSymOwnStep
  asmToBytecodeProofs asmEncodeParse codegenEncodingWf codegenRel
  symbolResolve words finite_map list rich_list arithmetic

(* Without a data header, every write is at a positive-size code label.
   Hence even the last binding written is strictly below the final offset. *)
Theorem header_free_lookup_below_end[local]:
  !p. (!a. ~MEM (AsmDataHeader a) p) ==>
      !l off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off ==>
              off < FST (compute_label_offsets p)
Proof
  ho_match_mp_tac SNOC_INDUCT >>
  conj_tac >- simp[compute_label_offsets_def] >>
  rpt gen_tac >> strip_tac >>
  simp[compute_label_offsets_snoc] >>
  Cases_on `x` >> simp[FLOOKUP_UPDATE, asm_inst_size_def] >>
  rw[] >> gvs[AllCaseEqs()] >> res_tac >>
  metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_ADD, ADD_COMM]
QED

(* Walk the offset fold from the end. Writes after j are strictly above
   its offset. At j, only its own name can be written at that offset. *)
Theorem lookup_at_code_label_names_it[local]:
  !p. asm_data_at_end p ==>
      !j a l. j < LENGTH p /\ EL j p = AsmLabel a /\
        FLOOKUP (SND (compute_label_offsets p)) l =
          SOME (asm_pc_to_offset p j) ==> l = a
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
  rename1 `asm_data_at_end (SNOC x p)` >>
  rename1 `EL j (SNOC x p) = AsmLabel a` >>
  Cases_on `j < LENGTH p`
  >- (
    `asm_data_at_end p` by (
      rw[asm_data_at_end_def] >>
      qpat_x_assum `asm_data_at_end (SNOC x p)`
        (qspec_then `i` mp_tac o REWRITE_RULE [asm_data_at_end_def]) >>
      simp[EL_SNOC] >> Cases_on `EL i p` >> simp[] >>
      metis_tac[EL_SNOC, prim_recTheory.LESS_SUC]) >>
    `EL j p = AsmLabel a` by fs[EL_SNOC] >>
    `asm_pc_to_offset (SNOC x p) j = asm_pc_to_offset p j` by
      simp[asm_pc_to_offset_def, TAKE_SNOC] >>
    `asm_pc_to_offset p (SUC j) = asm_pc_to_offset p j + 1` by
      simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
    `asm_pc_to_offset p (SUC j) <= asm_pc_to_offset p (LENGTH p)` by
      (irule asm_pc_to_offset_weak_mono >> simp[]) >>
    `asm_pc_to_offset p j < FST (compute_label_offsets p)` by
      fs[asm_pc_to_offset_def, compute_label_offsets_bound] >>
    `FLOOKUP (SND (compute_label_offsets p)) l =
       SOME (asm_pc_to_offset p j)` by (
      qpat_x_assum `FLOOKUP (SND (compute_label_offsets (SNOC x p))) l = _` mp_tac >>
      Cases_on `x` >> simp[compute_label_offsets_snoc, FLOOKUP_UPDATE] >>
      rw[] >> gvs[]) >>
    metis_tac[]) >>
  `j = LENGTH p` by decide_tac >> gvs[EL_LENGTH_SNOC] >>
  `!b. ~MEM (AsmDataHeader b) p` by (
    simp[MEM_EL, PULL_EXISTS] >> rpt strip_tac >>
    rename1 `AsmDataHeader b = EL n p` >>
    `EL n (SNOC (AsmLabel a) p) = AsmDataHeader b` by metis_tac[EL_SNOC] >>
    qpat_x_assum `asm_data_at_end (SNOC (AsmLabel a) p)`
      (qspec_then `n` mp_tac o REWRITE_RULE [asm_data_at_end_def]) >>
    (impl_tac >- simp[]) >>
    qpat_assum `EL n (SNOC (AsmLabel a) p) = AsmDataHeader b`
      (pure_rewrite_tac o single) >>
    disch_then (qspec_then `LENGTH p` mp_tac o SRULE []) >>
    simp[EL_LENGTH_SNOC, is_data_inst_def]) >>
  `asm_pc_to_offset (SNOC (AsmLabel a) p) (LENGTH p) =
     FST (compute_label_offsets p)` by
    simp[asm_pc_to_offset_def, TAKE_SNOC, compute_label_offsets_bound] >>
  Cases_on `l = a` >> simp[] >>
  fs[compute_label_offsets_snoc, FLOOKUP_UPDATE] >>
  drule header_free_lookup_below_end >> disch_then drule >> simp[]
QED

(* A row tag with a resolved jump offset names a code label. *)
Theorem canonical_jump_binding_relocated:
  asm_static_wf p /\
  FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME j ==>
  FLOOKUP (lo_reloc p installed) l = SOME off
Proof
  strip_tac >>
  drule offset_to_pc_reverse >> strip_tac >>
  drule offset_to_pc_label >> strip_tac >>
  `asm_data_at_end p` by fs[asm_static_wf_def] >>
  `EL j p = AsmLabel l` by metis_tac[lookup_at_code_label_names_it] >>
  `MEM (AsmLabel l) p` by metis_tac[EL_MEM] >>
  mp_tac (Q.SPECL [`p`, `installed`] lo_reloc_code_labels_agree) >>
  simp[code_labels_agree_def]
QED

Theorem canonical_named_code_label[local]:
  asm_static_wf p ==>
  ((?off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
          off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j) <=>
   INDEX_OF (AsmLabel l) p = SOME j)
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (
    drule offset_to_pc_reverse >> strip_tac >>
    drule offset_to_pc_label >> strip_tac >>
    `asm_data_at_end p` by fs[asm_static_wf_def] >>
    `EL j p = AsmLabel l` by metis_tac[lookup_at_code_label_names_it] >>
    `MEM (AsmLabel l) p` by metis_tac[EL_MEM] >>
    Cases_on `INDEX_OF (AsmLabel l) p` >- gvs[INDEX_OF_eq_NONE] >>
    drule_all asm_static_wf_code_label >> strip_tac >> gvs[]) >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  qexists `off` >> simp[] >>
  `65536 < dimword(:256)` by simp[dimword_def] >> decide_tac
QED

Theorem merge_rename_named_layout:
  !p x y q. q = MAP (rename_push_label x y) p ==>
  !C. C = (\r l j. ?off.
    FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j) ==>
  ((?pre third tail. y <> x /\ p = pre ++ [AsmLabel x; AsmLabel y; third] ++ tail) \/
   (?pre tail. p = pre ++ [AsmLabel x; AsmPushLabel y; AsmOp "JUMP"] ++ tail)) /\
  asm_static_wf p ==>
  !l j. (C p l j <=> INDEX_OF (AsmLabel l) p = SOME j) /\
        (C q l j <=> INDEX_OF (AsmLabel l) p = SOME j)
Proof
  simp[] >> rpt gen_tac >> disch_tac >>
  `asm_static_wf p` by fs[] >>
  `asm_static_wf (MAP (rename_push_label x y) p)` by (
    irule rename_static_wf >> simp[] >>
    qpat_x_assum `_ /\ asm_static_wf p` strip_assume_tac >>
    gvs[asm_label_refs_def]) >>
  simp[canonical_named_code_label, index_of_label_rename]
QED
