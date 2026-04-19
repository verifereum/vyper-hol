(*
 * Assembly → Bytecode Correctness — Proofs
 *
 * Helper lemmas for asm→bytecode correctness. Structural
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
  codegenRel symbolResolve asmSem asmWf
  vfmContext vfmOperation vfmTypes words
  list rich_list finite_map indexedLists pair option alist

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

(* ===== Top-Level Structural Lemmas ===== *)

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


(* encoding_wf condition for a single instruction *)
Definition encoding_wf_inst_def:
  encoding_wf_inst inst offsets ⇔
    (∀name. inst = AsmOp name ⇒ IS_SOME (evm_opcode_byte name)) ∧
    (∀bytes. inst = AsmPush bytes ⇒ LENGTH bytes ≤ 32) ∧
    (∀lbl off. FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes off) ≤ symbol_size) ∧
    (∀lbl d off. inst = AsmPushOfst lbl d ∧
       FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes (off + d)) ≤ symbol_size)
End

(* Extract per-instruction encoding_wf from whole-program asm_encoding_wf *)
Theorem asm_encoding_wf_el:
  ∀prog i.
    asm_encoding_wf prog ∧ i < LENGTH prog ⇒
    encoding_wf_inst (EL i prog) (SND (compute_label_offsets prog))
Proof
  rw[asm_encoding_wf_def, encoding_wf_inst_def, LET_THM] >>
  Cases_on `compute_label_offsets prog` >> gvs[] >>
  metis_tac[]
QED

(* ===== encoding_wf_inst wrappers ===== *)
(* These take encoding_wf_inst directly, eliminating boilerplate at call sites *)

Theorem ewi_encode_at:
  ∀prog i.
    i < LENGTH prog ∧ asm_encoding_wf prog ⇒
    TAKE (asm_inst_size (EL i prog))
      (DROP (asm_pc_to_offset prog i) (assemble prog)) =
    encode_inst (SND (compute_label_offsets prog)) (EL i prog)
Proof
  rpt strip_tac >>
  Cases_on `compute_label_offsets prog` >> gvs[] >>
  irule (GEN_ALL encode_at_proof) >>
  rpt conj_tac >> gvs[] >>
  rpt strip_tac >>
  gvs[asm_encoding_wf_def, LET_THM] >> metis_tac[]
QED

Theorem ewi_length:
  ∀inst offsets.
    encoding_wf_inst inst offsets ⇒
    LENGTH (encode_inst offsets inst) = asm_inst_size inst
Proof
  rpt strip_tac >> gvs[encoding_wf_inst_def] >>
  irule encode_inst_length_proof >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> simp[]
QED

(* ===== encode_num_bytes / word_of_bytes roundtrip ===== *)

(* Helper: encode_num_bytes unfold for nonzero n *)
Theorem encode_num_bytes_nonzero[local]:
  n <> 0 ==>
  (encode_num_bytes n = SNOC ((n2w n):word8) (encode_num_bytes (n DIV 256)))
Proof
  strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV[asmIRTheory.encode_num_bytes_def])) >>
  ASM_REWRITE_TAC[]
QED

(* Core roundtrip: num_of_bytes (REVERSE (encode_num_bytes n)) = n.
   encode_num_bytes produces big-endian minimal bytes.
   REVERSE gives little-endian. num_of_bytes is little-endian decode.
   The roundtrip holds because n MOD 256 + 256 * (n DIV 256) = n.
   IMPORTANT: uses PURE_REWRITE_TAC/SUBST1_TAC throughout to avoid
   rewriting loops with the IH (which contains encode_num_bytes). *)
Theorem num_of_bytes_encode_roundtrip:
  !n. num_of_bytes (REVERSE (encode_num_bytes n)) = n
Proof
  completeInduct_on `n` >>
  Cases_on `n`
  >- EVAL_TAC
  >>
  rename1 `SUC m` >>
  SUBST1_TAC (AP_TERM ``\x. num_of_bytes (REVERSE x)``
    (MP (INST [``n:num`` |-> ``SUC m``] encode_num_bytes_nonzero)
        (DECIDE ``SUC m <> 0``))
    |> BETA_RULE) >>
  PURE_REWRITE_TAC[REVERSE_SNOC] >>
  PURE_ONCE_REWRITE_TAC[byteTheory.num_of_bytes_def] >>
  `SUC m DIV 256 < SUC m` by
    simp[arithmeticTheory.DIV_LESS] >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_8] >>
  `(SUC m = (SUC m DIV 256) * 256 + SUC m MOD 256) /\
   SUC m MOD 256 < 256` by
    (irule_at Any arithmeticTheory.DIVISION >> simp[]) >>
  decide_tac
QED

(* ===== build_offset_to_pc reverse direction ===== *)

(* Helper: entries in the FOLDL with values below pc0 come from m0 *)
Theorem botp_small_values_from_init:
  ∀prog (m0:num|->num) off0 pc0 off v.
    FLOOKUP
      (FST (FOLDL (λ(m,off,pc) inst.
                     (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
              (m0,off0,pc0) prog)) off = SOME v ∧
    v < pc0 ⇒
    FLOOKUP m0 off = SOME v
Proof
  Induct
  >- (rpt strip_tac >> gvs[])
  >> rpt gen_tac >> strip_tac >>
  gvs[Once listTheory.FOLDL] >>
  first_x_assum
    (qspecl_then [`m0 |+ (off0, pc0)`,
                  `off0 + asm_inst_size h`, `pc0 + 1`,
                  `off`, `v`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  Cases_on `off = off0` >> gvs[FLOOKUP_UPDATE]
QED

(* Helper: positive sizes on a tail from positive sizes on the whole list *)
Theorem asm_inst_size_pos_tail:
  ∀h prog.
    (∀i. i < LENGTH (h::prog) ⇒ 0 < asm_inst_size (EL i (h::prog))) ⇒
    (∀i. i < LENGTH prog ⇒ 0 < asm_inst_size (EL i prog))
Proof
  rpt strip_tac >>
  `SUC i < LENGTH (h::prog)` by simp[] >>
  res_tac >> fs[]
QED

(* The main range lemma: FOLDL entries with values >= pc0 have canonical offsets *)
Theorem botp_range_lemma:
  ∀prog (m0:num|->num) off0 pc0 off pc.
    (∀i. i < LENGTH prog ⇒ 0 < asm_inst_size (EL i prog)) ∧
    (∀off' pc'. FLOOKUP m0 off' = SOME pc' ⇒ pc' < pc0) ∧
    FLOOKUP
      (FST (FOLDL (λ(m,off,pc) inst.
                     (m |+ (off,pc), off + asm_inst_size inst, pc + 1))
              (m0,off0,pc0) prog)) off = SOME pc ∧
    pc ≥ pc0 ⇒
    pc < pc0 + LENGTH prog ∧
    off = off0 + SUM (MAP asm_inst_size (TAKE (pc - pc0) prog))
Proof
  Induct >- (rpt strip_tac >> gvs[] >> res_tac >> gvs[])
  \\ rpt gen_tac \\ strip_tac
  \\ rename1 `h :: prog`
  (* Unfold FOLDL for h::prog in the FLOOKUP assumption *)
  \\ qpat_x_assum `FLOOKUP (FST (FOLDL _ _ (_::_))) _ = _`
       (mp_tac o ONCE_REWRITE_RULE [listTheory.FOLDL])
  \\ simp[] \\ strip_tac
  (* Derive tail size fact *)
  \\ sg `∀i. i < LENGTH prog ⇒ 0 < asm_inst_size (EL i prog)`
  >- (
    MATCH_MP_TAC asm_inst_size_pos_tail >>
    qexists_tac `h` >> first_assum ACCEPT_TAC
  )
  (* Case split: pc = pc0 or pc > pc0 *)
  \\ Cases_on `pc = pc0`
  >- (
    gvs[] >>
    qspecl_then [`prog`, `m0 |+ (off0, pc)`, `off0 + asm_inst_size h`,
                 `pc + 1`, `off`, `pc`]
      mp_tac botp_small_values_from_init >>
    impl_tac >- simp[] >>
    strip_tac >>
    Cases_on `off = off0` >- simp[] >>
    gvs[FLOOKUP_UPDATE] >> res_tac >> gvs[]
  )
  (* pc ≠ pc0, so pc ≥ pc0 + 1 *)
  \\ `pc ≥ pc0 + 1` by simp[]
  \\ first_x_assum
       (qspecl_then [`m0 |+ (off0, pc0)`,
                     `off0 + asm_inst_size h`, `pc0 + 1`,
                     `off`, `pc`] mp_tac)
  \\ impl_tac
  >- (
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- (rpt strip_tac >> Cases_on `off' = off0` >> gvs[FLOOKUP_UPDATE] >>
        res_tac >> gvs[])
    >- (first_assum ACCEPT_TAC)
    >- simp[]
  )
  \\ strip_tac
  \\ conj_tac >- simp[]
  \\ `pc - pc0 = SUC (pc - (pc0 + 1))` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ simp[]
QED

(* Reverse direction of offset_to_pc_inverse:
   FLOOKUP (build_offset_to_pc prog) off = SOME pc implies
   pc < LENGTH prog and asm_pc_to_offset prog pc = off.
   Requires all instruction sizes are positive up to pc. *)
Theorem offset_to_pc_reverse:
  ∀prog off pc.
    (∀i. i < LENGTH prog ⇒ 0 < asm_inst_size (EL i prog)) ∧
    FLOOKUP (build_offset_to_pc prog) off = SOME pc ⇒
    pc < LENGTH prog ∧ asm_pc_to_offset prog pc = off
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`prog`, `FEMPTY`, `0`, `0`, `off`, `pc`]
    mp_tac botp_range_lemma >>
  impl_tac >- fs[botp_as_triple, FLOOKUP_EMPTY] >>
  simp[asm_pc_to_offset_def]
QED

(* Word-level roundtrip: word_of_bytes F 0w decodes REVERSE encode_num_bytes.
   Requires dimindex >= 8 and divides 8 (standard for word8, word32, word256).
   Key bridge for AsmPush simulation. *)
Theorem word_of_bytes_encode_roundtrip:
  !v. 8 <= dimindex (:'a) /\ divides 8 (dimindex (:'a)) ==>
      word_of_bytes F (0w:'a word)
        (REVERSE (encode_num_bytes (w2n v))) = (v:'a word)
Proof
  rpt strip_tac >>
  fs[GSYM byteTheory.word_of_bytes_le_def,
     cv_stdTheory.word_of_bytes_le_eq_num_of_bytes,
     num_of_bytes_encode_roundtrip]
QED

(* Roundtrip for padded encoding: pad_bytes doesn't affect the decoded value.
   Key bridge for AsmPushLabel/AsmPushOfst simulation. *)
Theorem word_of_bytes_pad_encode_roundtrip:
  ∀off n.
    8 ≤ dimindex (:'a) ∧ divides 8 (dimindex (:'a)) ⇒
    word_of_bytes F (0w:'a word)
      (REVERSE (pad_bytes n (encode_num_bytes off))) = n2w off
Proof
  rpt strip_tac >>
  Cases_on `LENGTH (encode_num_bytes off) ≥ n`
  >- simp[pad_bytes_def, GSYM byteTheory.word_of_bytes_le_def,
          cv_stdTheory.word_of_bytes_le_eq_num_of_bytes,
          num_of_bytes_encode_roundtrip]
  >> `pad_bytes n (encode_num_bytes off) =
      REPLICATE (n − LENGTH (encode_num_bytes off)) 0w ++
      encode_num_bytes off`
       by simp[pad_bytes_def]
  >> pop_assum SUBST1_TAC
  >> simp[REVERSE_APPEND,
          GSYM byteTheory.word_of_bytes_le_def,
          cv_stdTheory.word_of_bytes_le_eq_num_of_bytes,
          byteTheory.num_of_bytes_APPEND,
          byteTheory.num_of_bytes_REPLICATE_0w,
          num_of_bytes_encode_roundtrip]
QED
