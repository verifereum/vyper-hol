Theory staticAbortOptConditionalJumpsLayout
Ancestors
  staticAbortOptPruneUnreachableLayout asmSplice asmSymBridge asmSymSem
  codegenEncodingWf symbolResolve asmOptimizer asmIR asmSem asmWf
  finite_map rich_list list words arithmetic

Theorem conditional_jump_one_layout:
  let b = LENGTH pre; r = splice_pc (LENGTH pre) 4 3 in
  let C = \s l d. ?off. FLOOKUP (SND (compute_label_offsets s)) l = SOME off /\
                        off < dimword(:256) /\
                        FLOOKUP (build_offset_to_pc s) off = SOME d in
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf p ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  (!l d. C p l d ==>
     INDEX_OF (AsmLabel l) p = SOME d /\ (d < b \/ b+4 <= d) /\
     INDEX_OF (AsmLabel l) q = SOME (r d) /\ C q l (r d)) /\
  (!l. IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)) /\
  (!i. i < LENGTH p /\ (i < b \/ b+4 <= i) ==>
       r i < LENGTH q /\ EL (r i) q = EL i p) /\
  b+3 < LENGTH q /\ EL b q = AsmOp "ISZERO" /\
  EL (b+1) q = AsmPushLabel x /\ EL (b+2) q = AsmOp "JUMPI" /\
  EL (b+3) q = AsmLabel c /\
  (!l i. i < LENGTH p /\
     (EL i p = AsmPushLabel l \/ EL i p = AsmPushOfst l 0 \/ EL i p = AsmDataLabel l) ==>
     ((i < b \/ b+4 <= i) /\ r i < LENGTH q /\ EL (r i) q = EL i p) \/
     (i = b+2 /\ l = x /\ EL (b+1) q = AsmPushLabel x) \/ (i = b /\ l = c))
Proof
  rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  qabbrev_tac `pat = [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x; AsmOp "JUMP"]` >>
  qabbrev_tac `repl = [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"]` >>
  qabbrev_tac `sfx = AsmLabel c::tail` >>
  `p = pre ++ pat ++ sfx /\ q = pre ++ repl ++ sfx` by
    (qpat_assum `p = _` SUBST1_TAC >> qpat_assum `q = _` SUBST1_TAC >>
     simp[Abbr `pat`, Abbr `repl`, Abbr `sfx`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH pat = 4 /\ LENGTH repl = 3 /\
   (!l. ~MEM (AsmLabel l) pat /\ ~MEM (AsmLabel l) repl)` by
    simp[Abbr `pat`, Abbr `repl`] >>
  `asm_splice_ok pat repl` by
    (simp[Abbr `pat`, Abbr `repl`, asm_splice_ok_def, is_data_inst_def,
          asm_label_refs_def, asm_inst_size_def] >>
     rw[] >> EVAL_TAC) >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p` by
    (qpat_assum `p = pre ++ pat ++ sfx` (fn th => fs[th]) >>
     irule asm_splice_static_wf >> simp[]) >>
  `!i. i < LENGTH p /\ (i < b \/ b+4 <= i) ==>
       splice_pc b 4 3 i < LENGTH q /\ EL (splice_pc b 4 3 i) q = EL i p` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `sfx`]
                    (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
     qpat_assum `p = pre ++ pat ++ sfx` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `q = pre ++ repl ++ sfx` (fn th => rewrite_tac[GSYM th]) >>
     simp[Abbr `b`, Abbr `pat`]) >>
  `b+3 < LENGTH q /\ EL b q = AsmOp "ISZERO" /\
   EL (b+1) q = AsmPushLabel x /\ EL (b+2) q = AsmOp "JUMPI" /\
   EL (b+3) q = AsmLabel c` by
    simp[Abbr `b`, Abbr `repl`, Abbr `sfx`, EL_APPEND_EQN] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "canonical"
  >- suspend "forward"
  >> suspend "producers"
QED

Resume conditional_jump_one_layout[canonical]:
  rpt gen_tac >> strip_tac >>
  drule_all lookup_pair_code_label_index >> strip_tac >>
  `INDEX_OF (AsmLabel l) q = SOME (splice_pc b 4 3 d) /\
   (d < b \/ b+4 <= d)` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `sfx`, `l` |-> `l`]
                    splice_index_of_label) >>
     qpat_assum `p = pre ++ pat ++ sfx` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `q = pre ++ repl ++ sfx` (fn th => rewrite_tac[GSYM th]) >>
     simp[Abbr `b`, Abbr `pat`]) >>
  drule_all (Q.INST [`p` |-> `q`] asm_static_wf_code_label) >>
  disch_then (qx_choose_then `new_off` strip_assume_tac) >>
  gvs[dimword_def] >> decide_tac
QED

Resume conditional_jump_one_layout[forward]:
  `!s l. IS_SOME (FLOOKUP (SND (compute_label_offsets s)) l) <=>
          MEM (AsmLabel l) s \/ MEM (AsmDataHeader l) s` by
    (ho_match_mp_tac SNOC_INDUCT >>
     conj_tac >- simp[compute_label_offsets_def] >>
     rpt gen_tac >> strip_tac >> gen_tac >>
     rename1 `SNOC a s` >> Cases_on `a` >>
     simp[compute_label_offsets_snoc, FLOOKUP_UPDATE, MEM_SNOC, AllCaseEqs()] >>
     rw[] >> gvs[]) >>
  simp[Abbr `pat`, Abbr `repl`]
QED

Resume conditional_jump_one_layout[producers]:
  rpt gen_tac >> disch_tac >>
  Cases_on `i < b \/ b+4 <= i`
  >- (disj1_tac >> metis_tac[]) >>
  `EL b p = AsmPushLabel c /\ EL (b+1) p = AsmOp "JUMPI" /\
   EL (b+2) p = AsmPushLabel x /\ EL (b+3) p = AsmOp "JUMP"` by
    simp[Abbr `b`, Abbr `pat`, Abbr `sfx`, EL_APPEND_EQN] >>
  `i = b \/ i = b+1 \/ i = b+2 \/ i = b+3` by decide_tac >>
  metis_tac[asm_inst_distinct, asm_inst_11]
QED

Finalise conditional_jump_one_layout
