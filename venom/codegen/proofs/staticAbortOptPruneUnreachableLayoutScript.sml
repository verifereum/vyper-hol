Theory staticAbortOptPruneUnreachableLayout
Ancestors
  asmOptPruneUnreachable asmSplice asmSymBridge asmEncodeParse
  asmToBytecodeProofs codegenEncodingWf asmSymSem asmOptimizer asmWf
  codegenRel symbolResolve vyperArith finite_map list rich_list words

(* A successful lookup comes from a write at an instruction boundary. *)
Theorem label_lookup_written_at[local]:
  !p l old. FLOOKUP (SND (compute_label_offsets p)) l = SOME old ==>
    ?j. j < LENGTH p /\ asm_pc_to_offset p j = old /\
        (EL j p = AsmLabel l \/ EL j p = AsmDataHeader l)
Proof
  ho_match_mp_tac SNOC_INDUCT >>
  conj_tac >- simp[compute_label_offsets_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP (SND (compute_label_offsets (SNOC x p))) l = SOME old` >>
  `FLOOKUP (SND (compute_label_offsets p)) l = SOME old \/
   (old = FST (compute_label_offsets p) /\
    (x = AsmLabel l \/ x = AsmDataHeader l))`
    by (Cases_on `x` >> fs[compute_label_offsets_snoc, FLOOKUP_UPDATE] >>
        gvs[AllCaseEqs()])
  >- (qpat_x_assum `!l old. _` drule >>
      disch_then (qx_choose_then `j` strip_assume_tac) >>
      qexists_tac `j` >>
      fs[SNOC_APPEND, asm_pc_to_offset_def, listTheory.TAKE_APPEND1,
         EL_APPEND_EQN]) >>
  qexists_tac `LENGTH p` >>
  simp[SNOC_APPEND, asm_pc_to_offset_def, listTheory.TAKE_APPEND1,
       EL_APPEND_EQN, compute_label_offsets_bound]
QED

(* A data-header write cannot name the positive-size code label reached
   by the inverse map. Use the forward code-label theorem for the name. *)
Theorem lookup_pair_code_label_index:
  asm_static_wf p /\ FLOOKUP (SND (compute_label_offsets p)) l = SOME old /\
  FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
  INDEX_OF (AsmLabel l) p = SOME dest
Proof
  strip_tac >>
  drule offset_to_pc_reverse >> strip_tac >>
  drule offset_to_pc_label >> disch_then (qx_choose_then `other` assume_tac) >>
  `MEM (AsmLabel l) p` by
    (drule label_lookup_written_at >>
     disch_then (qx_choose_then `j` strip_assume_tac)
     >- (simp[MEM_EL] >> qexists_tac `j` >> simp[]) >>
     Cases_on `j <= dest`
     >- (`asm_data_at_end p` by fs[asm_static_wf_def] >>
         fs[asm_data_at_end_def] >>
         qpat_x_assum `!i. _` (qspec_then `j` mp_tac) >>
         simp[is_data_inst_def] >> disch_then (qspec_then `dest` mp_tac) >>
         simp[is_data_inst_def]) >>
     `asm_pc_to_offset p (SUC dest) <= asm_pc_to_offset p j`
       by (irule asm_pc_to_offset_weak_mono >> decide_tac) >>
     `asm_pc_to_offset p (SUC dest) = old + 1`
       by simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
     decide_tac) >>
  Cases_on `INDEX_OF (AsmLabel l) p` >> fs[INDEX_OF_eq_NONE] >>
  drule_all asm_static_wf_code_label >> strip_tac >> gvs[]
QED

Theorem prune_one_canonical_layout:
  !pre t x tail.
  let p = pre ++ [t;x] ++ tail in
  let q = pre ++ [t] ++ tail in
  let d = LENGTH pre + 1 in
  let r = (\i. if i < d then i else i-1) in
  let R = (\prog l j. j < LENGTH prog /\
    (EL j prog = AsmPushLabel l \/
     (?delta. EL j prog = AsmPushOfst l delta) \/ EL j prog = AsmDataLabel l)) in
  asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p ==>
  (!l old dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME old /\
       FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
     dest < LENGTH p /\ EL dest p = AsmLabel l /\ dest <> d /\
     r dest < LENGTH q /\ EL (r dest) q = AsmLabel l /\
     (?fresh. FLOOKUP (SND (compute_label_offsets q)) l = SOME fresh /\
              fresh < dimword(:256) /\
              FLOOKUP (build_offset_to_pc q) fresh = SOME (r dest))) /\
  (!l origin (pick:string->num).
     R p l origin /\ (origin = d ==> R q l (pick l)) ==>
     R q l (if origin = d then pick l else r origin))
Proof
  rpt gen_tac >> pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, APPEND] >> simp[] >>
  qabbrev_tac `p = pre ++ t :: x :: tail` >>
  qabbrev_tac `q = pre ++ t :: tail` >>
  qabbrev_tac `d = LENGTH pre + 1` >> strip_tac >>
  (* The splice_pc convention at the deleted index itself is irrelevant. *)
  `!i. i <> d ==> splice_pc d 1 0 i = (if i < d then i else i-1)`
    by (rw[splice_pc_def] >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all lookup_pair_code_label_index >> strip_tac >>
      `AsmLabel l <> x` by (strip_tac >> gvs[asm_reachable_marker_def]) >>
      `INDEX_OF (AsmLabel l) q = SOME (if dest < d then dest else dest-1) /\
       dest <> d` by
        (mp_tac (Q.INST [`pfx` |-> `pre ++ [t]`, `pat` |-> `[x]`,
                         `repl` |-> `[]`, `sfx` |-> `tail`]
                    splice_index_of_label) >>
         pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, APPEND] >>
         fs[Abbr `p`, Abbr `q`, Abbr `d`] >>
         strip_tac >>
         qpat_x_assum `!i. INDEX_OF _ _ = SOME i ==> _` (qspec_then `dest` mp_tac) >>
         simp[] >> strip_tac >>
         `dest <> LENGTH pre + 1` by decide_tac >> simp[]) >>
      `asm_static_wf q` by
        (drule_all prune_one_refines >>
         fs[asm_refines_def, Abbr `q`, Abbr `p`]) >>
      drule_all (Q.INST [`p` |-> `q`] asm_static_wf_code_label) >>
      disch_then (qx_choose_then `fresh` strip_assume_tac) >>
      `fresh < dimword(:256)` by
        (irule lt_dimword_256 >> qexists_tac `16` >> simp[]) >>
      fs[INDEX_OF_eq_SOME, Abbr `p`, Abbr `q`]) >>
  rpt gen_tac >> Cases_on `origin = d` >> simp[] >> disch_tac >>
  `origin < LENGTH (pre ++ [t]) \/ LENGTH (pre ++ [t]) + 1 <= origin`
    by (fs[Abbr `d`] >> decide_tac) >>
  `splice_pc d 1 0 origin < LENGTH q /\
   EL (splice_pc d 1 0 origin) q = EL origin p` by
    (mp_tac (Q.INST [`pfx` |-> `pre ++ [t:asm_inst]`, `pat` |-> `[x]`,
                     `repl` |-> `[]`, `sfx` |-> `tail`, `i` |-> `origin`]
                (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
     pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, APPEND] >>
     gns[Abbr `p`, Abbr `q`, Abbr `d`]) >>
  gvs[Abbr `q`]
QED
