Theory staticAbortOptStackLayout
Ancestors
  staticAbortOptPruneUnreachableLayout asmSplice asmSymBridge asmOptPeephole
  asmOptimizer asmSymSem codegenEncodingWf symbolResolve asmIR asmWf
  finite_map list pred_set words arithmetic

(* The binding domain records declarations, not their current byte offsets. *)
Theorem stack_layout_binding_domain[local]:
  !p. FDOM (SND (compute_label_offsets p)) =
      {l | MEM (AsmLabel l) p \/ MEM (AsmDataHeader l) p}
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[compute_label_offsets_def, EXTENSION] >>
  gen_tac >> disch_tac >> qx_gen_tac `a` >> Cases_on `a` >>
  simp[compute_label_offsets_snoc, MEM_SNOC, EXTENSION] >> metis_tac[]
QED

Theorem stack_peephole_one_layout:
  !pre pat repl tail.
    !p. p = pre ++ pat ++ tail ==>
    !q. q = pre ++ repl ++ tail ==>
    !b. b = LENGTH pre ==>
    !m. m = LENGTH pat ==>
    !n. n = LENGTH repl ==>
    !f. f = splice_pc b m n ==>
    !Retained. Retained = (\i. i < b \/ b+m <= i) ==>
    ((pat = [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"] /\
        repl = [AsmOp "SWAP1"; AsmOp "DUP2"]) \/
     (pat = [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] /\ repl = []) \/
     (pat = [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"] /\
        repl = [AsmOp "POP"; AsmOp "POP"]) \/
     (?a. asm_swap_op a /\ pat = [a;a] /\ repl = []) \/
     (?a. asm_commutative_op a /\ pat = [AsmOp "SWAP1";a] /\ repl = [a]) \/
     (pat = [AsmOp "DUP1"; AsmOp "SWAP1"] /\ repl = [AsmOp "DUP1"])) /\
    asm_static_wf p ==>
    asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
    (!i. i < LENGTH p /\ Retained i ==>
         f i < LENGTH q /\ EL (f i) q = EL i p) /\
    (!i l. i < LENGTH p /\
       (EL i p = AsmPushLabel l \/ (?d. EL i p = AsmPushOfst l d) \/
        EL i p = AsmDataLabel l) ==>
         Retained i /\ f i < LENGTH q /\ EL (f i) q = EL i p) /\
    (!l. IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) ==>
         IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)) /\
    (!l off j. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
               FLOOKUP (build_offset_to_pc p) off = SOME j ==>
         Retained j /\ j < LENGTH p /\ EL j p = AsmLabel l /\
         f j < LENGTH q /\ EL (f j) q = AsmLabel l /\
         ?off'. FLOOKUP (SND (compute_label_offsets q)) l = SOME off' /\
                off' < dimword(:256) /\
                FLOOKUP (build_offset_to_pc q) off' = SOME (f j)) /\
    f b = b /\ f (b+m) = b+n /\
    (!i. i < LENGTH p /\ Retained i ==> f (i+1) = f i + 1)
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  rpt gen_tac >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "rule") assume_tac) >>
  `asm_splice_ok pat repl /\ 0 < LENGTH pat /\
   (!a. MEM a (pat ++ repl) ==> ?name. a = AsmOp name)` by suspend "window" >>
  `!l. ~MEM (AsmLabel l) pat /\ ~MEM (AsmLabel l) repl /\
       ~MEM (AsmDataHeader l) pat /\ ~MEM (AsmDataHeader l) repl` by
    (rpt strip_tac >> qpat_assum `!a. MEM a _ ==> _` mp_tac >>
     simp[MEM_APPEND] >> metis_tac[asm_inst_distinct]) >>
  `asm_static_wf (pre ++ repl ++ tail) /\
   FILTER is_data_inst (pre ++ repl ++ tail) = FILTER is_data_inst (pre ++ pat ++ tail)`
    by (irule asm_splice_static_wf >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_asm1_tac
  >- (gen_tac >> disch_tac >> irule splice_fetch >> Cases_on `pat` >> gvs[]) >>
  rpt conj_tac
  >- suspend "producer"
  >- simp[optionTheory.IS_SOME_EQ_NOT_NONE, flookup_thm,
          stack_layout_binding_domain, MEM_APPEND]
  >- suspend "canonical"
  >- simp[splice_pc_def]
  >- (rewrite_tac[splice_pc_def] >> IF_CASES_TAC >> decide_tac) >>
  gen_tac >> BETA_TAC >> disch_tac >> irule (cj 1 splice_pc_next) >> decide_tac
QED

Resume stack_peephole_one_layout[window]:
  `!a. asm_swap_op a \/ asm_commutative_op a ==> ?name. a = AsmOp name` by
    (Cases >> simp[asm_swap_op_def, asm_commutative_op_def]) >>
  asm_x "rule" strip_assume_tac >>
  TRY (rename1 `asm_swap_op a` >> `?name. a = AsmOp name` by metis_tac[]) >>
  TRY (rename1 `asm_commutative_op a` >> `?name. a = AsmOp name` by metis_tac[]) >>
  gvs[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
      symbolResolveTheory.asm_inst_size_def, dup2_opcode, DISJ_IMP_THM, FORALL_AND_THM]
QED

Resume stack_peephole_one_layout[producer]:
  rpt gen_tac >> disch_tac >>
  `i < LENGTH pre \/ LENGTH pre + LENGTH pat <= i` by
    (CCONTR_TAC >>
     `MEM (EL i (pre ++ pat ++ tail)) pat` by
       (simp[EL_APPEND_EQN] >> irule EL_MEM >> decide_tac) >>
     metis_tac[MEM_APPEND, asm_inst_distinct]) >>
  metis_tac[]
QED

Resume stack_peephole_one_layout[canonical]:
  rpt gen_tac >> strip_tac >>
  drule_all lookup_pair_code_label_index >> strip_tac >>
  `INDEX_OF (AsmLabel l) (pre ++ repl ++ tail) =
     SOME (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) j) /\
   (j < LENGTH pre \/ LENGTH pre + LENGTH pat <= j)` by
    (`pat <> []` by (Cases_on `pat` >> gvs[]) >>
     mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`, `repl` |-> `repl`,
                     `pat` |-> `pat`, `l` |-> `l`] splice_index_of_label) >>
     simp[]) >>
  qpat_assum `INDEX_OF (AsmLabel l) (pre ++ repl ++ tail) = SOME _`
    (mp_then (Pos last) mp_tac asm_static_wf_code_label) >>
  simp[] >> strip_tac >>
  fs[INDEX_OF_eq_SOME, dimword_def] >> decide_tac
QED

Finalise stack_peephole_one_layout
