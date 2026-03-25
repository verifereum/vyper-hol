(*
 * Assembly → Bytecode Correctness — Proofs
 *
 * Helper lemmas for asm→bytecode correctness. Proved structural
 * properties of offset maps, encoding, and label resolution.
 *
 * These are used by asmToBytecodeProps (via ACCEPT_TAC) once complete.
 *
 * TOP-LEVEL:
 *   offset_to_pc_inverse_proof    — byte offset → asm index round-trips
 *   label_offset_consistent_proof — labels resolve correctly
 *   encode_inst_length_proof      — encode_inst produces asm_inst_size bytes
 *   encode_at_proof               — bytes at offset match encode_inst
 *
 * HELPER:
 *   botp_*  — build_offset_to_pc FOLDL helpers
 *   clo_*   — compute_label_offsets FOLDL helpers
 *)

Theory asmToBytecodeProofs
Ancestors
  codegenRel symbolResolve asmSem
  list rich_list finite_map indexedLists pair option

(* ===== FOLDL Helper Lemmas ===== *)

(* build_offset_to_pc FOLDL is equivalent to a triple-accumulator FOLDL
   without MAPi (easier for induction). *)
Theorem botp_equiv:
  ∀prog (k:num) (m0:num|->num) (off0:num).
    FOLDL (λ(m,off) (i,inst:asm_inst).
             (m |+ (off,i), off + asm_inst_size inst))
      (m0,off0) (MAPi (λi inst. (k + i, inst)) prog) =
    (λ(m,off,pc:num). (m,off))
      (FOLDL (λ(m,off,pc) inst.
               (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
        (m0,off0,k) prog)
Proof
  Induct >> simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF] >>
  rpt gen_tac >>
  `(λi inst. (k + SUC i, inst:asm_inst)) =
   (λi inst. (SUC k + i, inst))` by simp[FUN_EQ_THM] >>
  pop_assum SUBST_ALL_TAC >>
  first_x_assum
    (qspecl_then [`SUC k`,
                  `m0 |+ (off0, k)`,
                  `off0 + asm_inst_size h`] mp_tac) >>
  simp[arithmeticTheory.ADD1]
QED

(* build_offset_to_pc equals FST of the triple FOLDL *)
Theorem botp_as_triple:
  ∀prog.
    build_offset_to_pc prog =
    FST (FOLDL (λ(m:num|->num,off:num,pc:num) inst.
                  (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
           (FEMPTY,0n,0n) prog)
Proof
  gen_tac >>
  simp[build_offset_to_pc_def] >>
  qspecl_then [`prog`, `0`, `FEMPTY`, `0`] mp_tac botp_equiv >>
  simp[] >> strip_tac >> pairarg_tac >> simp[]
QED

(* Triple FOLDL: offset and pc track correctly *)
Theorem botp_triple_acc:
  ∀prog (m0:num|->num) (off0:num) (pc0:num).
    let (m, off, pc) =
      FOLDL (λ(m,off,pc) inst.
               (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
        (m0,off0,pc0) prog
    in
      off = off0 + SUM (MAP asm_inst_size prog) ∧
      pc = pc0 + LENGTH prog
Proof
  Induct >> simp[] >> rpt gen_tac >> pairarg_tac >> gvs[] >>
  first_x_assum
    (qspecl_then [`m0 |+ (off0, pc0)`,
                  `off0 + asm_inst_size h`, `pc0 + 1`] mp_tac) >>
  pairarg_tac >> gvs[]
QED

(* Triple FOLDL: entries below running offset are preserved *)
Theorem botp_preserves_below:
  ∀prog (m0:num|->num) (off0:num) (pc0:num) k.
    k < off0 ⇒
    FLOOKUP
      (FST (FOLDL (λ(m,off,pc) inst.
                     (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
              (m0,off0,pc0) prog)) k =
    FLOOKUP m0 k
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once listTheory.FOLDL] >>
  first_x_assum
    (qspecl_then [`m0 |+ (off0, pc0)`,
                  `off0 + asm_inst_size h`, `pc0 + 1`, `k`] mp_tac) >>
  simp[FLOOKUP_UPDATE]
QED

(* Triple FOLDL: entry at position j is correctly recorded *)
Theorem botp_main_lemma:
  ∀prog m0 off0 pc0 j.
    j < LENGTH prog ∧ 0 < asm_inst_size (EL j prog) ⇒
    FLOOKUP
      (FST (FOLDL (λ(m:num|->num,off:num,pc:num) inst.
                     (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
              (m0,off0,pc0) prog))
      (off0 + SUM (MAP asm_inst_size (TAKE j prog))) =
    SOME (pc0 + j)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once listTheory.FOLDL] >>
  Cases_on `j` >> gvs[] >| [
    (* j = 0: entry just written, preserved by rest *)
    qspecl_then [`prog`, `m0 |+ (off0, pc0)`,
                 `off0 + asm_inst_size h`, `pc0 + 1`, `off0`]
      mp_tac botp_preserves_below >>
    impl_tac >- simp[] >>
    simp[FLOOKUP_UPDATE],
    (* j = SUC n: IH on tail *)
    first_x_assum
      (qspecl_then [`m0 |+ (off0, pc0)`,
                    `off0 + asm_inst_size h`, `pc0 + 1`, `n`] mp_tac) >>
    simp[]
  ]
QED

(* compute_label_offsets step function: let-elimination *)
Theorem clo_step_eq:
  (λ(pc:num,labels:string|->num) inst.
     (let labels' =
        case inst of
          AsmLabel lbl => labels |+ (lbl, pc)
        | AsmDataHeader lbl' => labels |+ (lbl', pc)
        | _ => labels
      in (pc + asm_inst_size inst, labels'))) =
  (λ(pc,labels) inst.
     (pc + asm_inst_size inst,
      case inst of
        AsmLabel lbl => labels |+ (lbl, pc)
      | AsmDataHeader lbl' => labels |+ (lbl', pc)
      | _ => labels))
Proof
  simp[FUN_EQ_THM, FORALL_PROD]
QED

(* compute_label_offsets: labels not written by later instructions
   are preserved *)
Theorem clo_preserves_label:
  ∀prog off0 (labels0:string|->num) lbl.
    (∀j. j < LENGTH prog ⇒
       EL j prog ≠ AsmLabel lbl ∧
       (∀l. EL j prog = AsmDataHeader l ⇒ l ≠ lbl)) ⇒
    FLOOKUP
      (SND (FOLDL (λ(pc:num,labels:string|->num) inst.
                     (pc + asm_inst_size inst,
                      case inst of
                        AsmLabel lbl => labels |+ (lbl, pc)
                      | AsmDataHeader lbl' => labels |+ (lbl', pc)
                      | _ => labels))
              (off0, labels0) prog)) lbl =
    FLOOKUP labels0 lbl
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once listTheory.FOLDL] >>
  first_x_assum
    (qspecl_then [`off0 + asm_inst_size h`,
                  `case h of AsmLabel l => labels0 |+ (l, off0)
                   | AsmDataHeader l' => labels0 |+ (l', off0)
                   | _ => labels0`, `lbl`] mp_tac) >>
  impl_tac >- (rpt strip_tac >>
               first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]) >>
  strip_tac >> pop_assum SUBST_ALL_TAC >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `h` >> gvs[FLOOKUP_UPDATE]
QED

(* compute_label_offsets: entry at position i is correctly recorded *)
Theorem clo_main_lemma:
  ∀prog off0 (labels0:string|->num) i lbl.
    i < LENGTH prog ∧ EL i prog = AsmLabel lbl ∧
    (∀j. i < j ∧ j < LENGTH prog ⇒
       EL j prog ≠ AsmLabel lbl ∧
       (∀l. EL j prog = AsmDataHeader l ⇒ l ≠ lbl)) ⇒
    FLOOKUP
      (SND (FOLDL (λ(pc:num,labels:string|->num) inst.
                     (pc + asm_inst_size inst,
                      case inst of
                        AsmLabel lbl => labels |+ (lbl, pc)
                      | AsmDataHeader lbl' => labels |+ (lbl', pc)
                      | _ => labels))
              (off0, labels0) prog)) lbl =
    SOME (off0 + SUM (MAP asm_inst_size (TAKE i prog)))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once listTheory.FOLDL] >>
  Cases_on `i` >| [
    (* i = 0: this element is AsmLabel lbl *)
    gvs[asm_inst_size_def] >>
    qspecl_then [`prog`, `off0 + 1`, `labels0 |+ (lbl, off0)`, `lbl`]
      mp_tac clo_preserves_label >>
    impl_tac >- (rpt strip_tac >>
                 first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]) >>
    simp[FLOOKUP_UPDATE],
    (* i = SUC n: recurse into tail *)
    gvs[] >>
    first_x_assum
      (qspecl_then [`off0 + asm_inst_size h`,
                    `case h of AsmLabel l => labels0 |+ (l, off0)
                     | AsmDataHeader l' => labels0 |+ (l', off0)
                     | _ => labels0`, `n`, `lbl`] mp_tac) >>
    impl_tac >- (simp[] >> rpt strip_tac >>
                 first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]) >>
    simp[]
  ]
QED

(* ===== Proved Top-Level Structural Lemmas ===== *)

Theorem offset_to_pc_inverse_proof:
  ∀prog pc.
    pc < LENGTH prog ∧
    0 < asm_inst_size (EL pc prog) ⇒
    FLOOKUP (build_offset_to_pc prog) (asm_pc_to_offset prog pc) =
      SOME pc
Proof
  rpt strip_tac >>
  simp[botp_as_triple, asm_pc_to_offset_def] >>
  qspecl_then [`prog`, `FEMPTY`, `0`, `0`, `pc`] mp_tac botp_main_lemma >>
  simp[]
QED

Theorem label_offset_consistent_proof:
  ∀prog i lbl.
    i < LENGTH prog ∧ EL i prog = AsmLabel lbl ∧
    (∀j. i < j ∧ j < LENGTH prog ⇒
       EL j prog ≠ AsmLabel lbl ∧
       (∀l. EL j prog = AsmDataHeader l ⇒ l ≠ lbl)) ⇒
    FLOOKUP (SND (compute_label_offsets prog)) lbl =
      SOME (asm_pc_to_offset prog i)
Proof
  rpt strip_tac >>
  simp[compute_label_offsets_def, clo_step_eq, asm_pc_to_offset_def] >>
  qspecl_then [`prog`, `0`, `FEMPTY`, `i`, `lbl`] mp_tac clo_main_lemma >>
  impl_tac >- (simp[] >> rpt strip_tac >> res_tac >> gvs[]) >>
  simp[]
QED

Theorem encode_inst_length_proof:
  ∀offsets inst.
    (∀name. inst = AsmOp name ⇒ IS_SOME (evm_opcode_byte name)) ∧
    (∀lbl off. FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes off) ≤ symbol_size) ∧
    (∀lbl d off. inst = AsmPushOfst lbl d ∧
       FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes (off + d)) ≤ symbol_size) ⇒
    LENGTH (encode_inst offsets inst) = asm_inst_size inst
Proof
  Cases_on `inst` >>
  simp[encode_inst_def, asm_inst_size_def] >>
  rpt strip_tac >>
  TRY (Cases_on `evm_opcode_byte s` >> gvs[IS_SOME_DEF]) >>
  TRY (rename1 `AsmPush bytes` >>
       Cases_on `bytes` >> simp[encode_inst_def]) >>
  TRY (Cases_on `FLOOKUP offsets s` >>
       simp[pad_bytes_def] >> rw[] >> res_tac >> simp[]) >>
  TRY (Cases_on `FLOOKUP offsets s0` >>
       simp[pad_bytes_def] >> rw[] >> res_tac >> simp[])
QED

Theorem flat_map_at_proof:
  ∀(f:'a -> 'b list) (ls:'a list) i (g:'a -> num).
    i < LENGTH ls ∧
    (∀j. j < LENGTH ls ⇒ LENGTH (f (EL j ls)) = g (EL j ls)) ⇒
    TAKE (g (EL i ls))
      (DROP (SUM (MAP g (TAKE i ls))) (FLAT (MAP f ls))) =
    f (EL i ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `pre = TAKE i ls` >>
  qabbrev_tac `mid = EL i ls` >>
  qabbrev_tac `post = DROP (SUC i) ls` >>
  `SUM (MAP g pre) = LENGTH (FLAT (MAP f pre))` by (
    simp[LENGTH_FLAT, MAP_MAP_o] >> AP_TERM_TAC >>
    simp[MAP_EQ_f, combinTheory.o_DEF, Abbr`pre`] >>
    rpt strip_tac >>
    `∃k. k < MIN i (LENGTH ls) ∧ e = EL k ls` by (
      imp_res_tac MEM_EL >>
      qexists_tac `n` >> gvs[EL_TAKE]) >>
    gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  `FLAT (MAP f ls) = FLAT (MAP f pre) ++ f mid ++ FLAT (MAP f post)` by (
    `ls = pre ++ [mid] ++ post` by
      simp[Abbr`pre`, Abbr`mid`, Abbr`post`, TAKE_DROP_SUC] >>
    pop_assum SUBST1_TAC >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `DROP (LENGTH (FLAT (MAP f pre)))
     ((FLAT (MAP f pre) ++ f mid) ++ FLAT (MAP f post)) =
   DROP (LENGTH (FLAT (MAP f pre)))
     (FLAT (MAP f pre) ++ f mid) ++ FLAT (MAP f post)` by
    simp[DROP_APPEND1] >>
  pop_assum SUBST_ALL_TAC >>
  simp[DROP_LENGTH_APPEND] >>
  `LENGTH (f mid) = g mid` by simp[Abbr`mid`] >>
  pop_assum (SUBST1_TAC o SYM) >>
  simp[TAKE_LENGTH_APPEND]
QED

Theorem encode_at_proof:
  ∀prog offsets i.
    i < LENGTH prog ∧
    (_, offsets) = compute_label_offsets prog ∧
    (∀j. j < LENGTH prog ⇒
       (∀name. EL j prog = AsmOp name ⇒
          IS_SOME (evm_opcode_byte name)) ∧
       (∀lbl off. FLOOKUP offsets lbl = SOME off ⇒
          LENGTH (encode_num_bytes off) ≤ symbol_size) ∧
       (∀lbl d off. EL j prog = AsmPushOfst lbl d ∧
          FLOOKUP offsets lbl = SOME off ⇒
          LENGTH (encode_num_bytes (off + d)) ≤ symbol_size)) ⇒
    TAKE (asm_inst_size (EL i prog))
      (DROP (asm_pc_to_offset prog i) (assemble prog)) =
    encode_inst offsets (EL i prog)
Proof
  rpt strip_tac >>
  `assemble prog = FLAT (MAP (encode_inst offsets) prog)` by (
    simp[assemble_def] >> pairarg_tac >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[asm_pc_to_offset_def] >>
  irule flat_map_at_proof >> simp[] >>
  rpt strip_tac >>
  qspecl_then [`offsets`, `EL j prog`] mp_tac encode_inst_length_proof >>
  impl_tac >- (
    rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
    metis_tac[]) >>
  simp[]
QED
