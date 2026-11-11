(*
 * The canonical data environment of an assembly program
 *
 * The bridge between the label-symbolic and the concrete assembly runs
 * (asmSymBridge) takes a data environment that matches the concrete code
 * (asm_data_env_ok): each data label the symbolic run reads maps to the
 * code from that label's offset on. asm_data_env is that environment,
 * read off the code at each data header's offset.
 *
 * The finalizer's contract keeps the data section (asm_refines requires
 * FILTER is_data_inst equal), and asm_static_wf puts the data section
 * after all the code. So for code assemble p ++ x, the environment from
 * each header is the data section's own bytes onward, plus x: it depends
 * only on the data section, and one environment serves both the program
 * and its optimized form.
 *
 * TOP-LEVEL:
 *   asm_data_env                 - the code from each data header's offset
 *   asm_data_env_ok_asm_data_env - it matches the code it was read from
 *   asm_data_split               - code, then a data section
 *   asm_data_env_data_section    - on assembled code, it depends only on
 *                                  the data section
 *   asm_data_env_agree           - programs with the same data section
 *                                  have the same environment
 *)

Theory asmDataEnv
Ancestors
  asmSymBridge asmSplice asmSymSem asmWf symbolResolve asmToBytecodeProofs
  codegenEncodingWf list rich_list finite_map pred_set

(* ===== The environment ===== *)

(* TOP-LEVEL: the code from each data header's offset on. *)
Definition asm_data_env_def:
  asm_data_env p (code : byte list) =
    (λoff. DROP off code) o_f
      DRESTRICT (SND (compute_label_offsets p)) {l | MEM (AsmDataHeader l) p}
End

(* TOP-LEVEL *)
Theorem asm_data_env_ok_asm_data_env:
  asm_data_env_ok p (asm_data_env p code) code
Proof
  rw[asm_data_env_ok_def, sym_data_label_def, asm_data_env_def,
     FDOM_DRESTRICT, FLOOKUP_DEF, DRESTRICT_DEF]
QED

(* ===== The data section ===== *)

(* TOP-LEVEL: a program with its data at the end, starting at a header,
   is its code followed by its data section. *)
Theorem asm_data_split:
  ∀p. asm_data_at_end p ∧
      (∀i. i < LENGTH p ∧ is_data_inst (EL i p) ⇒
           ∃j l. j ≤ i ∧ EL j p = AsmDataHeader l) ⇒
      ∃n. EVERY (λi. ¬is_data_inst i) (TAKE n p) ∧
          EVERY is_data_inst (DROP n p)
Proof
  Induct >- simp[] >>
  gen_tac >> pure_rewrite_tac[data_discipline_cons] >>
  Cases_on `h` >> simp[is_data_inst_def] >> strip_tac
  >~ [`TAKE _ (AsmDataHeader _ :: _)`] >- (qexists_tac `0` >> simp[is_data_inst_def]) >>
  first_x_assum (drule_all_then (qx_choose_then `m` strip_assume_tac)) >>
  qexists_tac `SUC m` >> simp[is_data_inst_def]
QED

(* ===== Label offsets past a prefix ===== *)

Overload clo_step[local] =
  ``λ(pc:num,labels:string|->num) inst.
      (pc + asm_inst_size inst,
       case inst of
         AsmLabel lbl => labels |+ (lbl, pc)
       | AsmDataHeader lbl' => labels |+ (lbl', pc)
       | _ => labels)``

(* Helper: a label of d is at the same distance from wherever d starts. *)
Theorem clo_label_offset_shift[local]:
  ∀d l. MEM (AsmLabel l) d ∨ MEM (AsmDataHeader l) d ⇒
    ∃k. ∀acc. FLOOKUP (SND (FOLDL clo_step acc d)) l = SOME (FST acc + k)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `MEM (AsmLabel l) d ∨ MEM (AsmDataHeader l) d`
  >- (first_x_assum drule >> strip_tac >>
      qexists_tac `asm_inst_size h + k` >>
      simp[pairTheory.FORALL_PROD]) >>
  qexists_tac `0` >>
  `h = AsmLabel l ∨ h = AsmDataHeader l` by gvs[] >>
  gvs[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  irule EQ_TRANS >> irule_at Any clo_preserves_label >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >> metis_tac[MEM_EL]
QED

Theorem compute_label_offsets_append[local]:
  compute_label_offsets (c ++ d) = FOLDL clo_step (compute_label_offsets c) d
Proof
  simp[compute_label_offsets_def, clo_step_eq, FOLDL_APPEND]
QED

(* ===== Assembled code ===== *)

Theorem assemble_flat[local]:
  assemble p = FLAT (MAP (encode_inst (SND (compute_label_offsets p))) p)
Proof
  simp[assemble_def] >> pairarg_tac >> simp[]
QED

(* Helper: data encodes the same under any label offsets, without
   AsmDataLabel. *)
Theorem encode_data_offsets[local]:
  ∀d o1 o2. EVERY is_data_inst d ∧ (∀l. ¬MEM (AsmDataLabel l) d) ⇒
            MAP (encode_inst o1) d = MAP (encode_inst o2) d
Proof
  Induct >> simp[] >> Cases >> simp[is_data_inst_def, encode_inst_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `s` mp_tac) >> simp[]
QED

Theorem encode_code_length[local]:
  ∀c offs. (∀i. MEM i c ⇒ encoding_wf_inst i offs) ⇒
           LENGTH (FLAT (MAP (encode_inst offs) c)) =
           SUM (MAP asm_inst_size c)
Proof
  Induct >> simp[DISJ_IMP_THM, FORALL_AND_THM, ewi_length]
QED

(* Helper: the environment of code followed by data, on its assembled
   code, is the data section's. *)
Theorem asm_data_env_append[local]:
  EVERY (λi. ¬is_data_inst i) c ∧ EVERY is_data_inst d ∧
  (∀l. ¬MEM (AsmDataLabel l) d) ∧
  (∀i. MEM i c ⇒ encoding_wf_inst i (SND (compute_label_offsets (c ++ d)))) ⇒
  asm_data_env (c ++ d) (assemble (c ++ d) ++ x) =
  asm_data_env d (assemble d ++ x)
Proof
  strip_tac >>
  `∀l. ¬MEM (AsmDataHeader l) c` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_data_inst_def]) >>
  `LENGTH (FLAT (MAP (encode_inst (SND (compute_label_offsets (c ++ d)))) c)) =
   FST (compute_label_offsets c)` by
    (qspecl_then [`c`, `SND (compute_label_offsets (c ++ d))`] mp_tac
       encode_code_length >>
     simp[compute_label_offsets_bound]) >>
  `assemble (c ++ d) =
   FLAT (MAP (encode_inst (SND (compute_label_offsets (c ++ d)))) c) ++
   assemble d` by
    (`MAP (encode_inst (SND (compute_label_offsets (c ++ d)))) d =
      MAP (encode_inst (SND (compute_label_offsets d))) d` by
       simp[encode_data_offsets] >>
     simp[assemble_flat]) >>
  simp[fmap_eq_flookup, asm_data_env_def, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  qx_gen_tac `l` >> Cases_on `MEM (AsmDataHeader l) d` >> simp[] >>
  `∃k. ∀acc. FLOOKUP (SND (FOLDL clo_step acc d)) l = SOME (FST acc + k)` by
    simp[clo_label_offset_shift] >>
  `FLOOKUP (SND (compute_label_offsets d)) l = SOME k` by
    simp[compute_label_offsets_def, clo_step_eq] >>
  `FLOOKUP (SND (compute_label_offsets (c ++ d))) l =
   SOME (FST (compute_label_offsets c) + k)` by
    simp[compute_label_offsets_append] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

(* TOP-LEVEL: on assembled code, the environment depends only on the data
   section. *)
Theorem asm_data_env_data_section:
  asm_static_wf p ⇒
  asm_data_env p (assemble p ++ x) =
  asm_data_env (FILTER is_data_inst p) (assemble (FILTER is_data_inst p) ++ x)
Proof
  strip_tac >>
  `∃c d. p = c ++ d ∧ EVERY (λi. ¬is_data_inst i) c ∧
         EVERY is_data_inst d` by
    (qspec_then `p` mp_tac asm_data_split >>
     impl_tac >- gvs[asm_static_wf_def] >> strip_tac >>
     qexistsl_tac [`TAKE n p`, `DROP n p`] >> simp[]) >>
  gvs[] >>
  `FILTER is_data_inst c = [] ∧ FILTER is_data_inst d = d` by
    simp[FILTER_EQ_NIL, FILTER_EQ_ID] >>
  simp[FILTER_APPEND] >> irule asm_data_env_append >>
  gvs[asm_static_wf_def, FORALL_AND_THM] >> rpt strip_tac >>
  gvs[MEM_EL] >>
  qspecl_then [`c ++ d`, `n`] mp_tac asm_encoding_wf_el >>
  simp[EL_APPEND1]
QED

(* TOP-LEVEL: programs with the same data section have the same
   environment on their assembled code followed by the same bytes. *)
Theorem asm_data_env_agree:
  asm_static_wf p ∧ asm_static_wf p' ∧
  FILTER is_data_inst p' = FILTER is_data_inst p ⇒
  asm_data_env p (assemble p ++ x) = asm_data_env p' (assemble p' ++ x)
Proof
  rpt strip_tac >> simp[asm_data_env_data_section]
QED
