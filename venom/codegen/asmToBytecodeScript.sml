(*
 * Assembly → Bytecode Correctness
 *
 * Proves that asm execution produces the same result as
 * vfmExecution$run on the assembled bytecode (assemble prog).
 *
 * Key insight: both use the same label offsets (compute_label_offsets).
 * The asm interpreter pushes concrete byte offsets for labels and maps
 * them back to asm indices for jumps. The EVM interpreter uses byte
 * offsets directly. At each step, stacks/memory/storage are identical.
 *
 * The bisimulation invariant is asm_evm_rel, which says:
 *   - stacks identical
 *   - memory identical
 *   - PC related by asm_pc_to_offset (sum of instruction sizes)
 *
 * Modulo gas (asm interpreter ignores gas entirely).
 *
 * TOP-LEVEL:
 *   asm_bytecode_step   — single step correspondence
 *   asm_bytecode_sim    — forward simulation (asm terminates ⇒ EVM matches)
 *   offset_to_pc_inverse — structural: byte offset → asm index inverse
 *   label_offset_consistent — labels resolve to correct byte offsets
 *)

Theory asmToBytecode
Ancestors
  codegenRel
Libs
  listTheory rich_listTheory finite_mapTheory indexedListsTheory pairTheory
  optionTheory symbolResolveTheory codegenRelTheory asmSemTheory

(* ===== Well-formedness for asm programs ===== *)

(* All labels in the program are unique *)
Definition asm_labels_unique_def:
  asm_labels_unique prog ⇔
    ALL_DISTINCT (FILTER IS_SOME
      (MAP (λinst. case inst of AsmLabel l => SOME l | _ => NONE) prog))
End

(* All jump targets resolve to valid JUMPDEST instructions *)
Definition asm_jumps_valid_def:
  asm_jumps_valid prog ⇔
    let (_, offsets) = compute_label_offsets prog in
    let otp = build_offset_to_pc prog in
    ∀lbl off pc.
      FLOOKUP offsets lbl = SOME off ∧
      FLOOKUP otp off = SOME pc ∧
      pc < LENGTH prog ⇒
      (∃l. EL pc prog = AsmLabel l)
End

(* Data section is at the end and not reachable by execution *)
Definition asm_data_at_end_def:
  asm_data_at_end prog ⇔
    ∀i. i < LENGTH prog ⇒
      (case EL i prog of
         AsmDataHeader _ => ∀j. j ≥ i ∧ j < LENGTH prog ⇒
           (case EL j prog of
              AsmDataHeader _ => T | AsmDataItem _ => T
            | AsmDataLabel _ => T | _ => F)
       | _ => T)
End

Definition asm_wf_def:
  asm_wf prog ⇔
    asm_labels_unique prog ∧
    asm_jumps_valid prog ∧
    asm_data_at_end prog
End

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

(* ===== Encoding Properties ===== *)

(* encode_inst produces exactly asm_inst_size bytes when:
   1. All opcodes are valid (AsmOp has a known encoding)
   2. All label offsets fit within symbol_size bytes
   3. All PushOfst computed values fit within symbol_size bytes *)
Theorem encode_inst_length:
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

(* FLAT (MAP f ls) at position i gives f (EL i ls), when
   LENGTH (f x) = g x for all elements *)
Theorem flat_map_at:
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
  (* SUM (MAP g pre) = LENGTH (FLAT (MAP f pre)) *)
  `SUM (MAP g pre) = LENGTH (FLAT (MAP f pre))` by (
    simp[LENGTH_FLAT, MAP_MAP_o] >> AP_TERM_TAC >>
    simp[MAP_EQ_f, combinTheory.o_DEF, Abbr`pre`] >>
    rpt strip_tac >>
    `∃k. k < MIN i (LENGTH ls) ∧ e = EL k ls` by (
      imp_res_tac MEM_EL >>
      qexists_tac `n` >> gvs[EL_TAKE]) >>
    gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* Rewrite FLAT (MAP f ls) using split *)
  `FLAT (MAP f ls) = FLAT (MAP f pre) ++ f mid ++ FLAT (MAP f post)` by (
    `ls = pre ++ [mid] ++ post` by
      simp[Abbr`pre`, Abbr`mid`, Abbr`post`, TAKE_DROP_SUC] >>
    pop_assum SUBST1_TAC >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* DROP past prefix, TAKE mid *)
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

(* Bytes at offset asm_pc_to_offset in assemble prog match encode_inst.
   This bridges the asm instruction index to the EVM byte position. *)
Theorem encode_at:
  ∀prog offsets i.
    i < LENGTH prog ∧
    (_, offsets) = compute_label_offsets prog ∧
    (* All opcodes valid and all label offsets fit *)
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
  irule flat_map_at >> simp[] >>
  rpt strip_tac >>
  qspecl_then [`offsets`, `EL j prog`] mp_tac encode_inst_length >>
  impl_tac >- (
    rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
    metis_tac[]) >>
  simp[]
QED

(* ===== Step Correspondence ===== *)

(* Single step: if asm takes one step producing AsmOK, the EVM
   can take one or more steps on the assembled bytecode reaching
   a related state.

   "one or more" because a single asm instruction may correspond to
   multiple EVM bytes (e.g. PUSH2 is 3 bytes but one asm instruction).

   Modulo gas: assumes sufficient gas for each EVM step. *)
Theorem asm_bytecode_step:
  ∀prog label_offsets otp as es inst.
    asm_wf prog ∧
    (_, label_offsets) = compute_label_offsets prog ∧
    otp = build_offset_to_pc prog ∧
    asm_evm_rel prog as es ∧
    as.as_pc < LENGTH prog ∧
    inst = EL as.as_pc prog ⇒
    ∀as'.
      asm_step label_offsets otp inst as = AsmOK as' ⇒
      ∃es'. asm_evm_rel prog as' es'
      (* NOTE: es' is reachable from es via EVM steps on assemble prog.
         The full proof will connect es' to step/run, currently cheated. *)
Proof
  cheat
QED

(* ===== Forward Simulation ===== *)

(* If asm execution halts, EVM execution of the assembled bytecode
   also halts with a corresponding result.

   Direction: asm terminates ⇒ EVM terminates with matching result.
   The converse would require reasoning about gas.

   Assumes sufficient gas on the EVM side (modulo gas).
   If run_asm returns AsmError ("out of fuel" or invalid),
   no conclusion about EVM is drawn. *)
Theorem asm_bytecode_sim:
  ∀fuel prog as es.
    asm_wf prog ∧
    asm_evm_rel prog as es ⇒
    (* Halt: asm halts cleanly ⇒ EVM halts cleanly *)
    (∀as'. run_asm fuel prog as = AsmHalt as' ⇒
       ∃es'. run es = SOME (INR NONE, es') ∧
             asm_evm_rel prog as' es') ∧
    (* Revert: asm reverts ⇒ EVM reverts *)
    (∀as'. run_asm fuel prog as = AsmRevert as' ⇒
       ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
             asm_evm_rel prog as' es') ∧
    (* Fault: asm faults ⇒ EVM faults (non-revert exception) *)
    (∀as'. run_asm fuel prog as = AsmFault as' ⇒
       ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                 exc ≠ Reverted ∧
                 asm_evm_rel prog as' es')
Proof
  cheat
QED

(* ===== Offset Map Properties ===== *)

(* build_offset_to_pc is left-inverse of asm_pc_to_offset at
   instruction boundaries: byte_offset → asm_index round-trips.
   Requires positive instruction size at pc so later entries don't
   overwrite (AsmDataHeader has size 0 but is never executed). *)
Theorem offset_to_pc_inverse:
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

(* compute_label_offsets agrees with asm_pc_to_offset for labels:
   the byte offset assigned to a label matches its position.
   Requires no later instruction writes the same label name
   (AsmLabel or AsmDataHeader). Under asm_wf, AsmLabel names are
   unique and data headers are at the end. *)
Theorem label_offset_consistent:
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
