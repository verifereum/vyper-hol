(*
 * Assembly Encode/Parse Bridge — Proofs
 *
 * Proves parse_opcode recognizes encoded instructions.
 * Depends on asmParseProofs (ML precomputation helpers).
 *
 * EXPORTS:
 *   encode_inst_nonempty     — encode_inst non-empty for non-data
 *   parse_opcode_encode_inst — parse_opcode recognizes encoded instructions
 *)

Theory asmEncodeParse

Ancestors
  asmParseProofs asmToBytecodeProofs
  codegenRel symbolResolve asmWf vfmContext vfmOperation
  list rich_list finite_map words combin option

Theorem encode_inst_nonempty:
  ∀offsets inst.
    ¬is_data_inst inst ∧
    (∀name. inst = AsmOp name ⇒ IS_SOME (evm_opcode_byte name)) ⇒
    encode_inst offsets inst ≠ []
Proof
  ho_match_mp_tac encode_inst_ind >>
  simp[is_data_inst_def, encode_inst_def, LET_THM] >>
  rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> CASE_TAC >> gvs[])
  >- (CASE_TAC >> simp[])
  >- (CASE_TAC >> simp[])
QED

Theorem parse_opcode_encode_inst:
  ∀offsets inst rest.
    ¬is_data_inst inst ∧
    (∀name. inst = AsmOp name ⇒ IS_SOME (evm_opcode_byte name)) ∧
    (∀bytes. inst = AsmPush bytes ⇒ LENGTH bytes ≤ 32) ∧
    (∀lbl off. FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes off) ≤ symbol_size) ∧
    (∀lbl d off. inst = AsmPushOfst lbl d ∧
       FLOOKUP offsets lbl = SOME off ⇒
       LENGTH (encode_num_bytes (off + d)) ≤ symbol_size) ⇒
    ∃op. parse_opcode (encode_inst offsets inst ++ rest) = SOME op ∧
         opcode op = encode_inst offsets inst
Proof
  ho_match_mp_tac encode_inst_ind >>
  simp[is_data_inst_def, encode_inst_def] >> rpt conj_tac
  (* AsmOp *)
  >- (rpt gen_tac >> strip_tac >> CASE_TAC >> gvs[] >>
      drule evm_byte_bridge >>
      disch_then (qspec_then `rest` strip_assume_tac) >>
      qexists_tac `op` >> simp[])
  (* AsmPush [] *)
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`0`, `[]`, `rest`] mp_tac parse_opcode_push >> simp[])
  (* AsmPush (v12::v13) *)
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`LENGTH (v12::v13)`, `v12::v13`, `rest`]
        mp_tac parse_opcode_push >> simp[])
  (* AsmPushLabel *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[symbol_size_def] >>
      CASE_TAC >> gvs[]
      >- (qspecl_then [`2`, `REPLICATE 2 (0w:byte)`, `rest`]
            mp_tac parse_opcode_push >> simp[])
      >- (res_tac >>
          qspecl_then [`2`, `pad_bytes 2 (encode_num_bytes x)`, `rest`]
            mp_tac parse_opcode_push >>
          (impl_tac >- simp[pad_bytes_length]) >>
          simp[]))
  (* AsmPushOfst *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[symbol_size_def] >>
      CASE_TAC >> gvs[]
      >- (qspecl_then [`2`, `REPLICATE 2 (0w:byte)`, `rest`]
            mp_tac parse_opcode_push >> simp[])
      >- (res_tac >>
          qspecl_then [`2`, `pad_bytes 2 (encode_num_bytes (delta + x))`, `rest`]
            mp_tac parse_opcode_push >>
          (impl_tac >- simp[pad_bytes_length]) >>
          simp[]))
  (* AsmLabel *)
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`"JUMPDEST"`, `91w`]
        mp_tac evm_byte_bridge >>
      (impl_tac >- EVAL_TAC) >>
      simp[])
QED

(* === encoding_wf_inst wrappers === *)

Theorem ewi_nonempty:
  ∀inst offsets.
    encoding_wf_inst inst offsets ∧ ¬is_data_inst inst ⇒
    encode_inst offsets inst ≠ []
Proof
  rpt strip_tac >> fs[encoding_wf_inst_def] >>
  imp_res_tac encode_inst_nonempty
QED

Theorem ewi_parse_opcode:
  ∀inst offsets rest.
    encoding_wf_inst inst offsets ∧ ¬is_data_inst inst ⇒
    ∃op. parse_opcode (encode_inst offsets inst ++ rest) = SOME op ∧
         opcode op = encode_inst offsets inst
Proof
  rpt gen_tac >> strip_tac >>
  irule parse_opcode_encode_inst >>
  fs[encoding_wf_inst_def] >>
  rpt strip_tac >> res_tac >> simp[]
QED

(* ===== PC offset helpers ===== *)

Theorem asm_pc_to_offset_suc:
  ∀prog j. j < LENGTH prog ⇒
    asm_pc_to_offset prog (SUC j) =
    asm_pc_to_offset prog j + asm_inst_size (EL j prog)
Proof
  Induct_on `prog` >> rw[asm_pc_to_offset_def] >>
  Cases_on `j` >> gvs[asm_pc_to_offset_def]
QED

Theorem asm_pc_to_offset_mono:
  ∀prog j i.
    j < i ∧ i ≤ LENGTH prog ∧
    (∀k. j ≤ k ∧ k < i ⇒ ¬is_data_inst (EL k prog)) ⇒
    asm_pc_to_offset prog j < asm_pc_to_offset prog i
Proof
  Induct_on `i` >> rw[] >>
  Cases_on `j < i`
  >- (`asm_pc_to_offset prog j < asm_pc_to_offset prog i` by
        (first_x_assum irule >> rw[]) >>
      `asm_pc_to_offset prog i ≤ asm_pc_to_offset prog (SUC i)` by
        (simp[asm_pc_to_offset_suc]) >>
      decide_tac)
  >> `j = i` by decide_tac >> gvs[] >>
     simp[asm_pc_to_offset_suc] >>
     `0 < asm_inst_size (EL i prog)` by
       (irule non_data_inst_size_pos >> gvs[])
QED

(* ===== Assemble/Parse Exact Correspondence ===== *)

(* Helper: TAKE n l = x implies l = x ++ DROP n l *)
Theorem take_eq_append_drop[local]:
  ∀n (l:'a list) x. TAKE n l = x ⇒ l = x ++ DROP n l
Proof
  metis_tac[TAKE_DROP]
QED

(* One step of parse_code: recognized opcode advances *)
Theorem parse_code_one_step:
  ∀pc m enc rest op.
    enc ≠ [] ∧
    parse_opcode (enc ++ rest) = SOME op ∧
    opcode op = enc ⇒
    parse_code pc m (enc ++ rest) =
    parse_code (pc + LENGTH enc) (m |+ (pc, op)) rest
Proof
  rw[] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_code_def])) >>
  `¬NULL (opcode op ++ rest)` by (Cases_on `opcode op` >> gvs[]) >>
  simp[] >> gvs[DROP_LENGTH_APPEND]
QED

(* parse_opcode only produces well-formed opnames *)
Theorem parse_opcode_wf_opname:
  ∀opc op. parse_opcode opc = SOME op ⇒ wf_opname op
Proof
  rw[parse_opcode_def, some_def] >>
  gvs[] >>
  SELECT_ELIM_TAC >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* parse_code at each instruction boundary stores opname with
   opcode = encode_inst *)
Theorem parse_code_prefix:
  ∀i prog.
    i ≤ LENGTH prog ∧
    asm_encoding_wf prog ∧
    (∀j. j < i ⇒ ¬is_data_inst (EL j prog)) ⇒
    ∃m. parse_code 0 FEMPTY (assemble prog) =
        parse_code (asm_pc_to_offset prog i) m
                   (DROP (asm_pc_to_offset prog i) (assemble prog)) ∧
        ∀j. j < i ⇒
          ∃op. FLOOKUP m (asm_pc_to_offset prog j) = SOME op ∧
               opcode op = encode_inst (SND (compute_label_offsets prog))
                                       (EL j prog) ∧
               wf_opname op
Proof
  Induct >> rw[]
  >- (qexists_tac `FEMPTY` >> simp[asm_pc_to_offset_def])
  >> rpt strip_tac >>
  `i ≤ LENGTH prog` by decide_tac >>
  `∀j. j < i ⇒ ¬is_data_inst (EL j prog)` by (rpt strip_tac >> gvs[]) >>
  first_x_assum drule_all >> strip_tac >>
  `i < LENGTH prog` by decide_tac >>
  `¬is_data_inst (EL i prog)` by gvs[] >>
  drule_all asm_encoding_wf_el >> strip_tac >>
  drule_all ewi_encode_at >> strip_tac >>
  `encode_inst (SND (compute_label_offsets prog)) (EL i prog) ≠ ([]:(byte list))` by
    (imp_res_tac ewi_nonempty) >>
  `LENGTH (encode_inst (SND (compute_label_offsets prog)) (EL i prog)) =
   asm_inst_size (EL i prog)` by
    (irule ewi_length >> simp[]) >>
  `asm_pc_to_offset prog (SUC i) =
   asm_pc_to_offset prog i + asm_inst_size (EL i prog)` by
    (match_mp_tac asm_pc_to_offset_suc >> simp[]) >>
  `DROP (asm_pc_to_offset prog i) (assemble prog) =
   encode_inst (SND (compute_label_offsets prog)) (EL i prog) ++
   DROP (asm_pc_to_offset prog (SUC i)) (assemble prog)` by
    (imp_res_tac take_eq_append_drop >> gvs[DROP_DROP_T]) >>
  drule_all ewi_parse_opcode >>
  disch_then (qspec_then
    `DROP (asm_pc_to_offset prog (SUC i)) (assemble prog)` strip_assume_tac) >>
  `parse_code (asm_pc_to_offset prog i) m
              (encode_inst (SND (compute_label_offsets prog)) (EL i prog) ++
               DROP (asm_pc_to_offset prog (SUC i)) (assemble prog)) =
   parse_code (asm_pc_to_offset prog i +
               LENGTH (encode_inst (SND (compute_label_offsets prog)) (EL i prog)))
              (m |+ (asm_pc_to_offset prog i, op))
              (DROP (asm_pc_to_offset prog (SUC i)) (assemble prog))` by
    (imp_res_tac parse_code_one_step >> gvs[]) >>
  qexists_tac `m |+ (asm_pc_to_offset prog i, op)` >>
  conj_tac >- gvs[] >>
  rpt strip_tac >>
  Cases_on `j < i`
  >- (first_x_assum drule >> strip_tac >>
      simp[FLOOKUP_UPDATE] >>
      `asm_pc_to_offset prog j ≠ asm_pc_to_offset prog i` by
        (CCONTR_TAC >> gvs[] >>
         `asm_pc_to_offset prog j < asm_pc_to_offset prog i` by
           (irule asm_pc_to_offset_mono >> rw[]) >>
         decide_tac) >>
      simp[])
  >> `j = i` by decide_tac >> gvs[] >>
     simp[FLOOKUP_UPDATE] >>
     imp_res_tac parse_opcode_wf_opname
QED

(* Main result: at instruction i, parse_code has the exact opname *)
Theorem assemble_parse_exact:
  ∀prog i.
    asm_wf prog ∧
    i < LENGTH prog ∧
    (∀j. j ≤ i ⇒ ¬is_data_inst (EL j prog)) ⇒
    ∃op. FLOOKUP (parse_code 0 FEMPTY (assemble prog))
                 (asm_pc_to_offset prog i) = SOME op ∧
         opcode op = encode_inst (SND (compute_label_offsets prog))
                                 (EL i prog) ∧
         wf_opname op
Proof
  rpt strip_tac >>
  `asm_encoding_wf prog` by fs[asm_wf_def] >>
  `SUC i ≤ LENGTH prog` by decide_tac >>
  `∀j. j < SUC i ⇒ ¬is_data_inst (EL j prog)` by
    (rpt strip_tac >> `j ≤ i` by decide_tac >> gvs[]) >>
  drule_all parse_code_prefix >> strip_tac >>
  `i < SUC i` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `op` >> rpt conj_tac
  >- (`asm_pc_to_offset prog i < asm_pc_to_offset prog (SUC i)` by
        (irule asm_pc_to_offset_mono >> rw[]) >>
      gvs[] >> irule parse_code_preserves_below >> gvs[])
  >> gvs[]
QED

(* ===== Offset total and bounds ===== *)

(* asm_pc_to_offset at LENGTH prog = LENGTH (assemble prog) *)
Theorem asm_encoding_wf_mem:
  ∀prog inst.
    asm_encoding_wf prog ∧ MEM inst prog ⇒
    encoding_wf_inst inst (SND (compute_label_offsets prog))
Proof
  rpt strip_tac >>
  fs[MEM_EL] >>
  metis_tac[asm_encoding_wf_el]
QED

Theorem asm_pc_to_offset_total:
  ∀prog.
    asm_encoding_wf prog ⇒
    asm_pc_to_offset prog (LENGTH prog) = LENGTH (assemble prog)
Proof
  rw[asm_pc_to_offset_def, TAKE_LENGTH_ID, assemble_def, LET_THM] >>
  Cases_on `compute_label_offsets prog` >> simp[] >>
  simp[LENGTH_FLAT, MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >>
  rpt strip_tac >>
  irule (GSYM ewi_length) >>
  `SND (q,r) = r` by simp[] >>
  metis_tac[asm_encoding_wf_mem]
QED

(* pc in bounds => byte offset in bounds *)
(* Weak monotonicity: i ≤ j ⇒ offset i ≤ offset j *)
Theorem asm_pc_to_offset_weak_mono:
  ∀prog i j.
    i ≤ j ∧ j ≤ LENGTH prog ⇒
    asm_pc_to_offset prog i ≤ asm_pc_to_offset prog j
Proof
  rw[asm_pc_to_offset_def] >>
  `TAKE j prog = TAKE i prog ++ DROP i (TAKE j prog)` by
    (`TAKE i (TAKE j prog) = TAKE i prog` by
       simp[TAKE_TAKE] >>
     metis_tac[TAKE_DROP]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[MAP_APPEND, SUM_APPEND]
QED

Theorem offset_in_bounds:
  ∀prog pc.
    asm_wf prog ∧
    pc < LENGTH prog ∧
    (∀j. j ≤ pc ⇒ ¬is_data_inst (EL j prog)) ⇒
    asm_pc_to_offset prog pc < LENGTH (assemble prog)
Proof
  rpt strip_tac >>
  `asm_encoding_wf prog` by fs[asm_wf_def] >>
  (* offset pc < offset (SUC pc) via strict mono (non-data at pc) *)
  `asm_pc_to_offset prog pc < asm_pc_to_offset prog (SUC pc)` by
    (irule asm_pc_to_offset_mono >>
     rw[] >> `k = pc` by decide_tac >> gvs[]) >>
  (* offset (SUC pc) <= offset (LENGTH prog) via weak mono *)
  `asm_pc_to_offset prog (SUC pc) ≤ asm_pc_to_offset prog (LENGTH prog)` by
    (irule asm_pc_to_offset_weak_mono >> simp[]) >>
  `asm_pc_to_offset prog (LENGTH prog) = LENGTH (assemble prog)` by
    (irule asm_pc_to_offset_total >> simp[]) >>
  decide_tac
QED

(* ===== Opcode identification from byte value ===== *)

(* Helper: if opcode op = [b] and wf_opname op, then op is determined by b.
   This is the core dispatch lemma for asm_evm_step. *)
Theorem opcode_byte_91_is_jumpdest:
  ∀op. wf_opname op ∧ opcode op = [91w:word8] ⇒ op = JumpDest
Proof
  Cases >> simp[opcode_def, wf_opname_def] >>
  rpt strip_tac >>
  gvs[n2w_11, word_add_n2w, dimword_8]
QED

(* General opcode injectivity: well-formed opnames with equal opcodes are equal.
   Proof: first byte of opcode determines the constructor family, then
   parameters are determined by remaining bytes + wf_opname constraints. *)
Theorem opcode_wf_inj:
  ∀op1 op2. wf_opname op1 ∧ wf_opname op2 ∧ opcode op1 = opcode op2 ⇒
            op1 = op2
Proof
  Cases >> simp[opcode_def, wf_opname_def] >> rpt strip_tac >>
  Cases_on `op2` >>
  gvs[opcode_def, wf_opname_def, word_add_n2w, n2w_11, dimword_8]
QED
