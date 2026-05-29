(*
 * Literals Codesize — Proofs
 *
 * Key property: lit_codesize_inst is a semantic identity on well-formed
 * instructions. The two mathematical facts are:
 *   NOT case: word_1comp (word_1comp w) = w
 *   SHL case: word_lsl (w >>> tz) tz = w  when tz = trailing_zeros w /\ w <> 0w
 *
 * The SHL identity needs:
 *   - tz < 256 (guaranteed: w <> 0w in SHL guard => trailing_zeros < 256)
 *   - w2n (n2w tz : 256 word) = tz (since tz < 256 < 2^256)
 *   - bottom tz bits of w are all zero (definition of trailing_zeros)
 *
 * Code paths through step_inst:
 *   ASSIGN [Lit w] uses the direct ASSIGN case in step_inst_base
 *   NOT [Lit (~w)] uses exec_pure1 word_1comp
 *   SHL [Lit (n2w tz); Lit (w>>>tz)] uses exec_pure2 (\n w. word_lsl w (w2n n))
 *   All non-INVOKE, so step_inst = step_inst_base (via step_inst_non_invoke).
 *
 * inst_wf is needed for equality: without it, ASSIGN and exec_pure1/exec_pure2
 *   produce different error strings when inst_outputs is malformed.
 * At the function level, lift_result absorbs error differences so no
 * precondition is needed.
 *
 * No analysis framework used — this is a pure peephole rewrite.
 *)

Theory literalsCodesizeProofs
Ancestors
  literalsCodesizeDefs passSimulationDefs passSimulationProps venomWf
  venomExecSemantics venomExecProofs stateEquiv stateEquivProps crossBlockSimProps
  option list
Libs
  fcpLib

(* ===== Word-level helpers ===== *)

(* Bit SUC n of w equals bit n of w shifted right by 1 *)
Theorem word_bit_suc_lsr[local]:
  !(w : 256 word) n. n < 255 ==>
    (word_bit (SUC n) w <=> word_bit n (w >>> 1))
Proof
  rw[wordsTheory.word_bit_def, wordsTheory.word_lsr_def] >>
  `dimindex (:256) = 256` by (CONV_TAC fcpLib.INDEX_CONV) >>
  simp[fcpTheory.FCP_BETA, arithmeticTheory.ADD1]
QED

(* A nonzero word with bit 0 clear stays nonzero after right shift by 1 *)
Theorem lsr1_nonzero[local]:
  !(w : 256 word). w <> 0w /\ ~word_bit 0 w ==> w >>> 1 <> 0w
Proof
  rw[wordsTheory.word_eq_0, wordsTheory.word_bit_def] >>
  `dimindex (:256) = 256` by (CONV_TAC fcpLib.INDEX_CONV) >>
  fs[] >>
  `?j. j < 256 /\ w ' j` by metis_tac[] >>
  Cases_on `j` >- fs[] >>
  rename1 `SUC k < 256` >>
  qexists_tac `k` >>
  fs[wordsTheory.word_lsr_def, fcpTheory.FCP_BETA, arithmeticTheory.ADD1]
QED

(* trailing_zeros produces bits that are all zero below tz *)
Theorem trailing_zeros_bits[local]:
  !(w : 256 word).
    w <> 0w ==>
    !i. i < trailing_zeros w ==> ~word_bit i w
Proof
  ho_match_mp_tac (fetch "literalsCodesizeDefs" "trailing_zeros_ind") >>
  rpt gen_tac >> strip_tac >>
  strip_tac >> rpt strip_tac >>
  Cases_on `word_bit 0 w` >- gvs[Once trailing_zeros_def] >>
  Cases_on `i` >- fs[] >>
  rename1 `SUC n < _` >>
  (* If SUC n >= 256, word_bit is trivially F *)
  Cases_on `255 <= n` >-
    (fs[wordsTheory.word_bit_def] >>
     `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >> fs[]) >>
  (* n < 255: unfold trailing_zeros, use IH *)
  `trailing_zeros w = SUC (trailing_zeros (w >>> 1))` by
    (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [trailing_zeros_def])) >> simp[]) >>
  `n < trailing_zeros (w >>> 1)` by fs[] >>
  fs[word_bit_suc_lsr] >>
  `w >>> 1 <> 0w` by (irule lsr1_nonzero >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

(* trailing_zeros w < 256 when w <> 0w — derived from trailing_zeros_bits *)
Theorem trailing_zeros_bound[local]:
  !(w : 256 word). w <> 0w ==> trailing_zeros w < 256
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  drule trailing_zeros_bits >> strip_tac >>
  `256 <= trailing_zeros w` by fs[] >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  `w = 0w` suffices_by fs[] >>
  PURE_REWRITE_TAC [wordsTheory.word_eq_0] >>
  rpt strip_tac >>
  `i < trailing_zeros w` by fs[] >>
  res_tac >> gvs[wordsTheory.word_bit_def]
QED

(* Right-shift then left-shift is identity when low bits are zero *)
Theorem lsr_lsl_trailing_zeros[local]:
  !(w : 256 word).
    w <> 0w ==>
    word_lsl (w >>> trailing_zeros w) (trailing_zeros w) = w
Proof
  rpt strip_tac >>
  `trailing_zeros w < 256` by (irule trailing_zeros_bound >> simp[]) >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[fcpTheory.CART_EQ] >> rpt strip_tac >>
  simp[wordsTheory.word_lsl_def, wordsTheory.word_lsr_def,
       fcpTheory.FCP_BETA] >>
  Cases_on `trailing_zeros w <= i` >- simp[] >>
  `i < trailing_zeros w` by fs[] >>
  `~word_bit i w` by (irule trailing_zeros_bits >> simp[]) >>
  fs[wordsTheory.word_bit_def]
QED

(* ===== Core step_inst equality ===== *)

Theorem lit_codesize_assign_not_step[local]:
  !fuel ctx inst s c out.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Lit c] /\
    inst.inst_outputs = [out] ==>
    step_inst fuel ctx
      (inst with <|inst_opcode := NOT; inst_operands := [Lit (~c)]|>) s =
    step_inst fuel ctx inst s
Proof
  rw[venomExecSemanticsTheory.step_inst_def,
     venomExecSemanticsTheory.step_inst_base_def,
     venomExecSemanticsTheory.exec_pure1_def,
     venomStateTheory.eval_operand_def]
QED

Theorem lit_codesize_assign_shl_step[local]:
  !fuel ctx inst s c out.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Lit c] /\
    inst.inst_outputs = [out] /\
    c <> 0w ==>
    step_inst fuel ctx
      (inst with
       <|inst_opcode := SHL;
         inst_operands := [Lit (n2w (trailing_zeros c));
                           Lit (c >>> trailing_zeros c)]|>) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `trailing_zeros c < 256` by (irule trailing_zeros_bound >> simp[]) >>
  `trailing_zeros c < dimword(:256)` by
    (fs[wordsTheory.dimword_def] >> CONV_TAC fcpLib.INDEX_CONV >> fs[]) >>
  rw[venomExecSemanticsTheory.step_inst_def,
     venomExecSemanticsTheory.step_inst_base_def,
     venomExecSemanticsTheory.exec_pure2_def,
     venomStateTheory.eval_operand_def,
     arithmeticTheory.LESS_MOD,
     lsr_lsl_trailing_zeros]
QED

(* Core lemma: each well-formed rewritten instruction produces the
   identical step_inst result.
   inst_wf ensures correct operand/output counts, making error paths
   unreachable and allowing exact equality. *)
Theorem lit_codesize_inst_step_eq:
  !fuel ctx inst s.
    inst_wf inst ==>
    step_inst fuel ctx (lit_codesize_inst inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  simp[lit_codesize_inst_def] >>
  Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  gvs[inst_wf_def] >>
  (* Resolve inst_outputs = [out] from LENGTH = 1 *)
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> gvs[]) >>
  rpt (IF_CASES_TAC >> simp[]) >> gvs[] >>
  FIRST [
    irule lit_codesize_assign_not_step >> simp[],
    irule lit_codesize_assign_shl_step >> simp[]]
QED

(* ===== Lifting to block and function level ===== *)

(* Helper: block_map_transform preserves bb_instructions via MAP *)
Triviality block_map_transform_bb_instructions[local]:
  !f bb. (block_map_transform f bb).bb_instructions = MAP f bb.bb_instructions
Proof
  Cases_on `bb` >>
  simp[passSimulationDefsTheory.block_map_transform_def] >>
  EVAL_TAC >> simp[]
QED

(* Helper: block_map_transform preserves bb_label *)
Theorem block_map_transform_label:
  !f bb. (block_map_transform f bb).bb_label = bb.bb_label
Proof
  Cases_on `bb` >>
  simp[passSimulationDefsTheory.block_map_transform_def] >>
  EVAL_TAC >> simp[]
QED

(* Unconditional: lookup on MAP gives OPTION_MAP of original lookup *)
Theorem lookup_block_lit_codesize_eq:
  !lbl fns.
    lookup_block lbl (MAP (block_map_transform lit_codesize_inst) fns) =
    OPTION_MAP (block_map_transform lit_codesize_inst) (lookup_block lbl fns)
Proof
  rpt strip_tac >>
  irule passSimulationPropsTheory.lookup_block_map >>
  rpt strip_tac >> Cases_on `bb` >>
  simp[passSimulationDefsTheory.block_map_transform_def] >>
  EVAL_TAC >> simp[]
QED

(* Conditional: if original lookup is NONE, so is transformed lookup *)
Theorem lookup_block_lit_codesize_NONE[local]:
  !lbl fns.
    lookup_block lbl fns = NONE ==>
    lookup_block lbl (MAP (block_map_transform lit_codesize_inst) fns) = NONE
Proof
  simp[lookup_block_lit_codesize_eq]
QED

(* Conditional: if original lookup is SOME bb, transformed lookup is SOME (f bb) *)
Theorem lookup_block_lit_codesize_SOME[local]:
  !lbl fns bb.
    lookup_block lbl fns = SOME bb ==>
    lookup_block lbl (MAP (block_map_transform lit_codesize_inst) fns) =
    SOME (block_map_transform lit_codesize_inst bb)
Proof
  simp[lookup_block_lit_codesize_eq]
QED

(* Helper: function_map_transform preserves fn_blocks via MAP *)
(* Critical: simp cannot reduce (fn with fn_blocks := MAP bt fn.fn_blocks).fn_blocks *)
Triviality function_map_transform_fn_blocks[local]:
  !bt fn. (function_map_transform bt fn).fn_blocks = MAP bt fn.fn_blocks
Proof
  Cases_on `fn` >>
  simp[passSimulationDefsTheory.function_map_transform_def] >>
  EVAL_TAC >> simp[]
QED

(* Helper: get_instruction on block_map_transform *)
Theorem get_instruction_block_map_transform[local]:
  !f bb idx.
    get_instruction (block_map_transform f bb) idx =
    OPTION_MAP f (get_instruction bb idx)
Proof
  rw[venomInstTheory.get_instruction_def,
     block_map_transform_bb_instructions,
     listTheory.EL_MAP, listTheory.LENGTH_MAP]
QED

(* Helper: lit_codesize_inst preserves is_terminator *)
Theorem lit_codesize_inst_is_terminator[local]:
  !inst. is_terminator (lit_codesize_inst inst).inst_opcode =
         is_terminator inst.inst_opcode
Proof
  rw[lit_codesize_inst_def] >>
  Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[venomInstTheory.is_terminator_def])
QED

(* Lit_codesize_inst preserves PHI instructions and never creates PHIs *)
Theorem lit_codesize_inst_phi_preserving[local]:
  !inst.
    inst.inst_opcode = PHI ==>
    lit_codesize_inst inst = inst
Proof
  rw[lit_codesize_inst_def]
QED

Theorem lit_codesize_inst_phi_opcode_preserving[local]:
  !inst.
    inst.inst_opcode = PHI ==>
    (lit_codesize_inst inst).inst_opcode = PHI
Proof
  rw[lit_codesize_inst_def]
QED

Theorem lit_codesize_inst_non_phi_opcode_preserving[local]:
  !inst.
    inst.inst_opcode <> PHI ==>
    (lit_codesize_inst inst).inst_opcode <> PHI
Proof
  rw[lit_codesize_inst_def] >>
  Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[venomInstTheory.is_terminator_def])
QED

(* Block-level equality: transformed block produces identical result *)
Theorem lit_codesize_block_eq:
  !fuel ctx bb s.
    EVERY inst_wf bb.bb_instructions ==>
    exec_block fuel ctx (block_map_transform lit_codesize_inst bb) s =
    exec_block fuel ctx bb s
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
  simp[get_instruction_block_map_transform] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  (* inst_wf from EVERY *)
  `inst_wf inst` by (
    fs[venomInstTheory.get_instruction_def] >>
    metis_tac[listTheory.EVERY_EL]) >>
  (* step_inst equality *)
  `step_inst fuel ctx (lit_codesize_inst inst) s =
   step_inst fuel ctx inst s` by
    metis_tac[lit_codesize_inst_step_eq] >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  simp[lit_codesize_inst_is_terminator] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  (* Recursive case: measure decreases *)
  first_x_assum irule >> simp[] >>
  fs[venomInstTheory.get_instruction_def]
QED

Theorem phi_prefix_length_lit_codesize_inst[local]:
  !insts. phi_prefix_length (MAP lit_codesize_inst insts) = phi_prefix_length insts
Proof
  Induct >- simp[phi_prefix_length_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def] >- (
    metis_tac[lit_codesize_inst_phi_opcode_preserving,
              lit_codesize_inst_phi_preserving]) >>
  metis_tac[lit_codesize_inst_non_phi_opcode_preserving]
QED

Theorem eval_phis_lit_codesize_inst2[local]:
  !s insts.
    eval_phis s (MAP lit_codesize_inst insts) = eval_phis s insts
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  rpt gen_tac >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >- (
    `lit_codesize_inst h = h` by metis_tac[lit_codesize_inst_phi_preserving] >>
    `(lit_codesize_inst h).inst_opcode = PHI` by simp[] >>
    simp[eval_phis_def]) >>
  `(lit_codesize_inst h).inst_opcode <> PHI` by
    metis_tac[lit_codesize_inst_non_phi_opcode_preserving] >>
  simp[eval_phis_def]
QED

Theorem lit_codesize_run_block_eq6:
  !fuel ctx bb s.
    EVERY inst_wf bb.bb_instructions ==>
    run_block fuel ctx (block_map_transform lit_codesize_inst bb) s =
    run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  `!s. exec_block fuel ctx (block_map_transform lit_codesize_inst bb) s =
       exec_block fuel ctx bb s`
    by metis_tac[lit_codesize_block_eq] >>
  irule run_block_eq_from_exec_block_eq >>
  simp[block_map_transform_def,
       phi_prefix_length_lit_codesize_inst,
       eval_phis_lit_codesize_inst2]
QED

(* Bridge: run_block equality implies run_block_entry equality (overloads) *)
Theorem lit_codesize_run_block_entry_eq:
  !fuel ctx bb s.
    EVERY inst_wf bb.bb_instructions ==>
    run_block_entry fuel ctx (block_map_transform lit_codesize_inst bb) s =
    run_block_entry fuel ctx bb s
Proof
  metis_tac[lit_codesize_run_block_eq6]
QED


(* Per-block run_block_entry equality for lit_codesize_inst,
   instantiated from fn_inst_wf. *)
Theorem lit_codesize_rbe_from_fnwf:
  !fuel' ctx fn bb s'.
    fn_inst_wf fn /\ MEM bb fn.fn_blocks ==>
    run_block_entry fuel' ctx (block_map_transform lit_codesize_inst bb) s' =
    run_block_entry fuel' ctx bb s'
Proof
  rpt strip_tac >>
  irule lit_codesize_run_block_entry_eq >>
  qpat_x_assum `fn_inst_wf fn` mp_tac >>
  simp[fn_inst_wf_def, EVERY_MEM] >>
  strip_tac >> first_x_assum drule >> simp[EVERY_MEM]
QED

(* Per-block label preservation for lit_codesize_inst *)
Theorem lit_codesize_lbl_from_mem:
  !fn bb.
    MEM bb fn.fn_blocks ==>
    (block_map_transform lit_codesize_inst bb).bb_label = bb.bb_label
Proof
  rpt strip_tac >>
  simp[block_map_transform_label]
QED



Theorem lit_codesize_fmap_xform_ante:
  !fn ctx.
    fn_inst_wf fn ==>
    (!bb. MEM bb fn.fn_blocks ==>
       (block_map_transform lit_codesize_inst bb).bb_label = bb.bb_label) /\
    (!fuel' bb s'. MEM bb fn.fn_blocks ==>
       run_block_entry fuel' ctx (block_map_transform lit_codesize_inst bb) s' =
       run_block_entry fuel' ctx bb s')
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[block_map_transform_label]) >>
  rpt gen_tac >> strip_tac >>
  irule lit_codesize_run_block_entry_eq >>
  qpat_x_assum `fn_inst_wf fn` mp_tac >>
  simp[fn_inst_wf_def, EVERY_MEM] >>
  strip_tac >> first_x_assum drule >> simp[EVERY_MEM]
QED

Theorem lit_codesize_fn_eq:
  !fuel ctx fn s.
    fn_inst_wf fn ==>
    run_blocks fuel ctx (lit_codesize_function fn) s =
    run_blocks fuel ctx fn s
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[lit_codesize_function_def] >>
  irule passSimulationPropsTheory.run_blocks_fmap_xform_eq >>
  qspecl_then [`fn`,`ctx`] drule lit_codesize_fmap_xform_ante >>
  strip_tac >>
  metis_tac[]
QED

Theorem lit_codesize_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (lit_codesize_function fn) s)
Proof
  rpt strip_tac >>
  simp[lit_codesize_fn_eq, lift_result_refl,
       state_equiv_refl, execution_equiv_refl]
QED
