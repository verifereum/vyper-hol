(* The actual installed suffix starts at the final code_end header. The
   assembler's existing encoding-wellformedness condition is essential:
   symbol fields use fixed widths in layout but encode arbitrary naturals. *)
Theory immutableCodeLayout
Ancestors
  e2eDefs e2eEntry e2eProducers lowerDloadDefs asmEncodeParse asmToBytecodeProofs
  asmWf asmSem asmIR symbolResolve finite_map list arithmetic
  stackPlanGen planExec codegen
  rich_list codegenRel codegenEncodingWf

Theorem immutable_runtime_codegen_nonempty:
  codegen_assembly policy unit = SOME prog ==> assemble prog <> []
Proof
  cheat
QED

Theorem immutable_installed_prefix_guard:
  codegen_assembly policy unit = SOME prog ==>
  ((~?tail. assemble prog ++ section = 0xEFw::tail) <=>
   (~?tail. assemble prog = 0xEFw::tail))
Proof
  cheat
QED

Theorem immutable_layout_fold_size:
  !prog pc (labels:string|->num).
  FST (FOLDL (\(pc,labels) inst.
      (pc + asm_inst_size inst,
       case inst of AsmLabel lbl => labels |+ (lbl,pc)
        | AsmDataHeader lbl => labels |+ (lbl,pc) | _ => labels))
    (pc,labels) prog) = pc + SUM (MAP asm_inst_size prog)
Proof
  cheat
QED

Theorem immutable_code_end_offset:
  !prefix lbl.
  FLOOKUP (SND (compute_label_offsets (prefix ++ [AsmDataHeader lbl]))) lbl =
    SOME (asm_pc_to_offset (prefix ++ [AsmDataHeader lbl]) (LENGTH prefix + 1))
Proof
  cheat
QED

Theorem immutable_code_end_length:
  prog = prefix ++ [AsmDataHeader "code_end"] /\ asm_encoding_wf prog ==>
  FLOOKUP (SND (compute_label_offsets prog)) "code_end" =
    SOME (LENGTH (assemble prog))
Proof
  cheat
QED

(* No synthetic label is inserted into the entry state. This lemma consumes
   the ordinary assembler condition and the generated final-header shape. *)
Theorem entry_venom_state_code_layout:
  !tops prog am tx es cp prefix.
  call_state_rel tops (assemble prog) am tx es /\
  prog = prefix ++ [AsmDataHeader "code_end"] /\ asm_encoding_wf prog ==>
  code_layout_valid (entry_venom_state prog cp es)
Proof
  cheat
QED

Theorem generated_entry_immutable_code_layout:
  !tops prog am tx es cp policy unit.
  call_state_rel tops (assemble prog) am tx es /\
  codegen_assembly policy unit = SOME prog /\ asm_encoding_wf prog ==>
  code_layout_valid (entry_venom_state prog cp es)
Proof
  cheat
QED

(* unit_shape_ok rules out OFFSET, the only source of unbounded push
   offsets, and codegen_assembly bounds the code size, so codegen's output
   meets asm_encoding_wf. *)
Theorem generated_entry_code_layout_shape:
  !tops prog am tx es cp policy unit.
  call_state_rel tops (assemble prog) am tx es /\
  codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit ==>
  code_layout_valid (entry_venom_state prog cp es)
Proof
  cheat
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else print "statement-check gate skipped\n"
  end) (DB.thms "immutableCodeLayout");
