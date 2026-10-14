(*
 * Assembly encoding interface regressions (TASK045).
 * TOP-LEVEL: encoding_wf_with_zero_size_data, duplicate_offset_last_write,
 *   zero_size_reverse_lookup, encoding_only_parse.
 * These are concrete kernel checks, not a claim about all codegen output.
 *)
Theory asmEncodingRegression
Ancestors
  asmToBytecodeProps asmToBytecodeProofs asmEncodeParse asmWf
  symbolResolve asmIR codegenRel finite_map list indexedLists words
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset

(* Includes repeated labels, a terminal zero-size header, empty data, and
   a data-label reference. Encoding wf deliberately permits these. *)
Definition encoding_regression_prog_def:
  encoding_regression_prog =
    [AsmLabel "entry"; AsmLabel "entry"; AsmOp "STOP";
     AsmDataHeader "data"; AsmDataHeader "data"; AsmDataItem [];
     AsmDataItem [42w]; AsmDataLabel "data"; AsmDataHeader "code_end"]
End

Theorem encoding_wf_with_zero_size_data:
  asm_encoding_wf encoding_regression_prog /\
  ~asm_wf encoding_regression_prog /\
  asm_inst_size (EL 3 encoding_regression_prog) = 0 /\
  asm_inst_size (EL 5 encoding_regression_prog) = 0 /\
  asm_inst_size (EL 8 encoding_regression_prog) = 0
Proof
  `~asm_labels_unique encoding_regression_prog` by EVAL_TAC >>
  simp[asm_wf_def, encoding_regression_prog_def, asm_inst_size_def] >>
  rw[asm_encoding_wf_def, compute_label_offsets_def, asm_inst_size_def,
     symbol_size_def, FLOOKUP_UPDATE] >>
  TRY (rename1 `i < 9` >>
       `MEM (EL i encoding_regression_prog) encoding_regression_prog` by
         (irule EL_MEM >> simp[encoding_regression_prog_def]) >>
       fs[encoding_regression_prog_def]) >>
  gvs[] >> simp[asm_inst_size_def, evm_opcode_byte_def, evm_opcode_table_def] >>
  gvs[AllCaseEqs()] >> EVAL_TAC
QED

(* At offset 3, two headers and empty data are overwritten by the data byte;
   the terminal header is still a valid entry at offset LENGTH (assemble ...). *)
Theorem duplicate_offset_last_write:
  FLOOKUP (build_offset_to_pc encoding_regression_prog) 3 = SOME 6 /\
  FLOOKUP (build_offset_to_pc encoding_regression_prog) 6 = SOME 8 /\
  FLOOKUP (SND (compute_label_offsets encoding_regression_prog)) "entry" = SOME 1 /\
  FLOOKUP (SND (compute_label_offsets encoding_regression_prog)) "data" = SOME 3 /\
  FLOOKUP (SND (compute_label_offsets encoding_regression_prog)) "code_end" = SOME 6 /\
  assemble encoding_regression_prog = [91w; 91w; 0w; 42w; 0w; 3w]
Proof
  EVAL_TAC
QED

(* Exercise the generalized reverse interface at every surviving entry,
   including the zero-size final header. No positive-size premise is supplied. *)
Theorem zero_size_reverse_lookup:
  !off pc.
    FLOOKUP (build_offset_to_pc encoding_regression_prog) off = SOME pc ==>
    pc < LENGTH encoding_regression_prog /\
    asm_pc_to_offset encoding_regression_prog pc = off
Proof
  rpt strip_tac >> drule offset_to_pc_reverse >> simp[]
QED

(* Parsing at the STOP prefix needs only encoding wf, even though repeated
   labels and the data header make asm_wf false. *)
Theorem encoding_only_parse:
  ?op. FLOOKUP (parse_code 0 FEMPTY (assemble encoding_regression_prog))
               (asm_pc_to_offset encoding_regression_prog 2) = SOME op /\
       opcode op = encode_inst (SND (compute_label_offsets encoding_regression_prog))
                               (EL 2 encoding_regression_prog) /\
       wf_opname op
Proof
  irule assemble_parse_exact >>
  simp[encoding_wf_with_zero_size_data, encoding_regression_prog_def] >>
  rpt strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2` by decide_tac >>
  gvs[is_data_inst_def]
QED
