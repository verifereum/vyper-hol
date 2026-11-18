Theory staticAbortOptMergeIszeroLayout
Ancestors
  asmSplice asmSymSem asmSymBridge asmOptimizer asmToBytecodeProofs asmEncodeParse
  codegenEncodingWf codegenRel asmWf symbolResolve finite_map arithmetic
  words list

(* A write in the suffix cannot bind a name to an offset strictly below
   the byte size of the prefix. *)
Theorem iszero_lookup_below_prefix[local]:
  !sfx pre l old.
    old < FST (compute_label_offsets pre) /\
    FLOOKUP (SND (compute_label_offsets (pre ++ sfx))) l = SOME old ==>
    FLOOKUP (SND (compute_label_offsets pre)) l = SOME old
Proof
  Induct using SNOC_INDUCT >- simp[] >>
  rpt gen_tac >>
  `FST (compute_label_offsets pre) <= FST (compute_label_offsets (pre ++ sfx))`
    by simp[compute_label_offsets_bound, MAP_APPEND, SUM_APPEND] >>
  rename1 `pre ++ SNOC a sfx` >>
  Cases_on `a` >> simp[compute_label_offsets_snoc, FLOOKUP_UPDATE] >>
  rpt (COND_CASES_TAC >> simp[]) >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem merge_iszero_one_canonical_layout:
  !b. b = LENGTH pre ==>
  !z. z = (if LENGTH pat = 3 then b+1 else b) ==>
  !keep. keep = (\i. i < z \/ z+2 <= i) ==>
  !f. f = (\i. if i < z then i else i-2) ==>
  !R. R = (\prog l i. i < LENGTH prog /\
    (EL i prog = AsmPushLabel l \/ (?d. EL i prog = AsmPushOfst l d) \/
     EL i prog = AsmDataLabel l)) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  asm_static_wf p /\
  ((?x. asm_returns_zero_or_one x /\
        pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
   (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
        repl = [AsmPushLabel l; AsmOp "JUMPI"])) ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  (!l old dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME old /\
       FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
       keep dest /\ dest < LENGTH p /\ EL dest p = AsmLabel l /\
       f dest < LENGTH q /\ EL (f dest) q = AsmLabel l /\
       ?off. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
             off < dimword(:256) /\
             FLOOKUP (build_offset_to_pc q) off = SOME (f dest)) /\
  (!i. keep i /\ i < LENGTH p ==> f i < LENGTH q /\ EL (f i) q = EL i p) /\
  (!l i. R p l i ==> keep i /\ R q l (f i))
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) >>
  BETA_TAC >>
  qabbrev_tac `z = if LENGTH pat = 3 then LENGTH pre+1 else LENGTH pre` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?left right. p = left ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++ right /\
                q = left ++ right /\ z = LENGTH left` by (
    qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac
    >- (qexistsl_tac [`pre ++ [x]`, `tail`] >>
        once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[Abbr `z`]) >>
    qexistsl_tac [`pre`, `[AsmPushLabel l; AsmOp "JUMPI"] ++ tail`] >>
    simp[Abbr `z`]) >>
  qpat_x_assum `p = pre ++ pat ++ tail` kall_tac >>
  qpat_x_assum `q = pre ++ repl ++ tail` kall_tac >>
  qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` kall_tac >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p` by (
    qpat_x_assum `p = _` SUBST_ALL_TAC >> qpat_x_assum `q = _` SUBST_ALL_TAC >>
    mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                    `repl` |-> `[]:asm_inst list`,
                    `pfx` |-> `left`, `sfx` |-> `right`] asm_splice_static_wf) >>
    simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
         asm_inst_size_def]) >>
  `!i. (i < z \/ z+2 <= i) /\ i < LENGTH p ==>
       (if i < z then i else i-2) < LENGTH q /\
       EL (if i < z then i else i-2) q = EL i p` by (
    rpt gen_tac >> strip_tac >>
    mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                    `repl` |-> `[]:asm_inst list`,
                    `pfx` |-> `left`, `sfx` |-> `right`, `i` |-> `i`]
               (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
    `i <= LENGTH left <=> i < z` by decide_tac >>
    (impl_tac >- (gvs[] >> decide_tac)) >>
    simp[splice_pc_def]) >>
  BETA_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "target"
  >> suspend "origin"
QED

Resume merge_iszero_one_canonical_layout[target]:
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac offset_to_pc_reverse >>
  drule_then (qx_choose_then `name` assume_tac) offset_to_pc_label >>
  `old < FST (compute_label_offsets (TAKE (SUC dest) p))` by (
    simp[compute_label_offsets_bound, GSYM asm_pc_to_offset_def] >>
    mp_tac (Q.SPECL [`p`, `dest`] asm_pc_to_offset_suc) >>
    simp[asm_inst_size_def]) >>
  `FLOOKUP (SND (compute_label_offsets (TAKE (SUC dest) p))) l = SOME old` by (
    irule iszero_lookup_below_prefix >> conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `DROP (SUC dest) p` >> rewrite_tac[TAKE_DROP] >>
    first_assum ACCEPT_TAC) >>
  `~MEM (AsmDataHeader l) (TAKE (SUC dest) p)` by (
    `LENGTH (TAKE (SUC dest) p) = SUC dest` by (irule LENGTH_TAKE >> decide_tac) >>
    qpat_assum `LENGTH (TAKE (SUC dest) p) = SUC dest`
      (fn th => rewrite_tac[MEM_EL, th]) >>
    strip_tac >> rename1 `i < SUC dest` >>
    `i < LENGTH p /\ i <= dest` by decide_tac >>
    `EL i (TAKE (SUC dest) p) = EL i p` by (irule EL_TAKE >> decide_tac) >>
    `asm_data_at_end p` by fs[asm_static_wf_def] >>
    qpat_x_assum `asm_data_at_end p`
      (qspec_then `i` mp_tac o REWRITE_RULE[asm_data_at_end_def]) >>
    `EL i p = AsmDataHeader l` by metis_tac[] >>
    qpat_assum `EL i p = AsmDataHeader l` (fn th => simp[NoAsms, th]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `dest` >>
    qpat_assum `EL dest p = AsmLabel name`
      (fn th => simp[NoAsms, th, is_data_inst_def]) >> decide_tac) >>
  `MEM (AsmLabel l) (TAKE (SUC dest) p)` by (
    `!code. ~MEM (AsmLabel l) code /\ ~MEM (AsmDataHeader l) code ==>
       FLOOKUP (SND (compute_label_offsets code)) l = NONE` by (
      POP_ASSUM_LIST (K ALL_TAC) >>
      Induct using SNOC_INDUCT >- simp[compute_label_offsets_def] >>
      rpt gen_tac >> rename1 `SNOC a code` >> Cases_on `a` >>
      simp[compute_label_offsets_snoc, FLOOKUP_UPDATE] >>
      rpt (COND_CASES_TAC >> gvs[])) >>
    metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `MEM (AsmLabel l) p` by metis_tac[MEM_APPEND, TAKE_DROP] >>
  Cases_on `INDEX_OF (AsmLabel l) p` >- gvs[INDEX_OF_eq_NONE] >>
  rename1 `INDEX_OF (AsmLabel l) p = SOME j` >>
  `j = dest` by (drule_all asm_static_wf_code_label >> strip_tac >> gvs[]) >>
  qpat_x_assum `j = dest` SUBST_ALL_TAC >>
  `EL dest p = AsmLabel l` by metis_tac[INDEX_OF_eq_SOME] >>
  `INDEX_OF (AsmLabel l) q = SOME (if dest < z then dest else dest-2) /\
   (dest < z \/ z+2 <= dest)` by (
    mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                    `repl` |-> `[]:asm_inst list`, `l` |-> `l`,
                    `pfx` |-> `left`, `sfx` |-> `right`] splice_index_of_label) >>
    simp[NoAsms] >>
    qpat_assum `p = _` (fn th => rewrite_tac[GSYM th]) >>
    qpat_assum `q = _` (fn th => rewrite_tac[GSYM th]) >>
    qpat_assum `z = LENGTH left` (fn th => rewrite_tac[GSYM th]) >>
    strip_tac >>
    `dest < z \/ z+2 <= dest` by
      (first_x_assum (qspec_then `dest` mp_tac) >> metis_tac[]) >>
    `dest <= z <=> dest < z` by decide_tac >>
    qpat_x_assum `INDEX_OF (AsmLabel l) q = _` mp_tac >>
    qpat_assum `INDEX_OF (AsmLabel l) p = SOME dest`
      (fn th => rewrite_tac[th, optionTheory.OPTION_MAP_DEF, splice_pc_def]) >>
    qpat_assum `dest <= z <=> dest < z` (fn th => rewrite_tac[th]) >>
    simp[NoAsms] >> (simp[])) >>
  `!off:num. off < 65536 ==> off < dimword(:256)` by (
    simp[dimword_def] >> decide_tac) >>
  drule_all (Q.INST [`p` |-> `q`] asm_static_wf_code_label) >> strip_tac >>
  qpat_assum `!i. _ ==> _ < LENGTH q /\ _`
    (qspec_then `dest` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  `EL (if dest < z then dest else dest-2) q = AsmLabel l` by (
    qpat_assum `EL _ q = EL dest p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
  qexists_tac `off` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `!k:num. k < 65536 ==> _` irule >> first_assum ACCEPT_TAC
QED

Resume merge_iszero_one_canonical_layout[origin]:
  rpt gen_tac >> disch_tac >>
  `i < z \/ z+2 <= i` by (
    spose_not_then assume_tac >>
    `i = z \/ i = z+1` by decide_tac >>
    `EL i p = AsmOp "ISZERO"` by (
      qpat_x_assum `p = _` SUBST_ALL_TAC >>
      asm_rewrite_tac[] >> gvs[EL_APPEND_EQN]) >>
    gvs[]) >>
  metis_tac[]
QED

Finalise merge_iszero_one_canonical_layout
