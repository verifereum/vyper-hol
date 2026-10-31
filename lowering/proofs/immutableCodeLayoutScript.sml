(* The actual installed suffix starts at the final code_end header. The
   assembler's existing encoding-wellformedness condition is essential:
   symbol fields use fixed widths in layout but encode arbitrary naturals. *)
Theory immutableCodeLayout
Ancestors
  e2eDefs e2eEntry e2eProducers lowerDloadDefs asmEncodeParse asmToBytecodeProofs
  asmWf asmSem asmIR symbolResolve finite_map list arithmetic
  stackPlanGen planExec codegen
  rich_list codegenRel

Theorem immutable_runtime_codegen_nonempty:
  codegen_assembly policy unit = SOME prog ==> assemble prog <> []
Proof
  strip_tac >> drule codegen_assembly_success_shape >> strip_tac >>
  gvs[assemble_def, context_plan_ops_def, execute_plan_def, MAP_APPEND,
      FLAT_APPEND, revert_postamble_def, exec_stack_op_def, encode_inst_def] >>
  pairarg_tac >> simp[]
QED

Theorem immutable_compiled_runtime_nonempty:
  compile_vyper (K SOME) policy tops = SOME (deploy_bc,runtime_bc) ==>
  runtime_bc <> []
Proof
  strip_tac >> drule compile_vyper_runtime_phases >> strip_tac >>
  gvs[] >> drule immutable_runtime_codegen_nonempty >> simp[]
QED

Theorem immutable_installed_prefix_guard:
  codegen_assembly policy unit = SOME prog ==>
  ((~?tail. assemble prog ++ section = 0xEFw::tail) <=>
   (~?tail. assemble prog = 0xEFw::tail))
Proof
  strip_tac >> drule immutable_runtime_codegen_nonempty >>
  Cases_on `assemble prog` >> simp[]
QED

Theorem immutable_layout_fold_size:
  !prog pc (labels:string|->num).
  FST (FOLDL (\(pc,labels) inst.
      (pc + asm_inst_size inst,
       case inst of AsmLabel lbl => labels |+ (lbl,pc)
        | AsmDataHeader lbl => labels |+ (lbl,pc) | _ => labels))
    (pc,labels) prog) = pc + SUM (MAP asm_inst_size prog)
Proof
  Induct >> simp[] >> rpt gen_tac >> simp[ADD_ASSOC]
QED

Theorem immutable_code_end_offset:
  !prefix lbl.
  FLOOKUP (SND (compute_label_offsets (prefix ++ [AsmDataHeader lbl]))) lbl =
    SOME (asm_pc_to_offset (prefix ++ [AsmDataHeader lbl]) (LENGTH prefix + 1))
Proof
  rpt gen_tac >>
  simp[compute_label_offsets_def, FOLDL_APPEND, clo_step_eq,
       asm_pc_to_offset_def, asm_inst_size_def, SUM_APPEND] >>
  pairarg_tac >> simp[FLOOKUP_UPDATE] >>
  qspecl_then [`prefix`,`0`,`FEMPTY`] mp_tac immutable_layout_fold_size >>
  asm_rewrite_tac[] >>
  simp[TAKE_LENGTH_TOO_LONG, SUM_APPEND, asm_inst_size_def]
QED

Theorem immutable_code_end_length:
  prog = prefix ++ [AsmDataHeader "code_end"] /\ asm_encoding_wf prog ==>
  FLOOKUP (SND (compute_label_offsets prog)) "code_end" =
    SOME (LENGTH (assemble prog))
Proof
  strip_tac >> drule asm_pc_to_offset_total >> strip_tac >>
  gvs[immutable_code_end_offset]
QED

(* No synthetic label is inserted into the entry state. This lemma consumes
   the ordinary assembler condition and the generated final-header shape. *)
Theorem entry_venom_state_code_layout:
  !tops prog am tx es cp prefix.
  call_state_rel tops (assemble prog) am tx es /\
  prog = prefix ++ [AsmDataHeader "code_end"] /\ asm_encoding_wf prog ==>
  code_layout_valid (entry_venom_state prog cp es)
Proof
  rpt strip_tac >> rename1 `entry_venom_state prog cplan es` >>
  drule_then (qspec_then `cplan` strip_assume_tac)
    entry_venom_state_installed_section >>
  drule_all immutable_code_end_length >> strip_tac >>
  qpat_x_assum `prog = _` kall_tac >>
  rewrite_tac[code_layout_valid_def] >> conj_tac
  >- (qexists_tac `assemble prog` >> asm_rewrite_tac[]) >> conj_tac
  >- (qpat_assum `(entry_venom_state _ _ _).vs_code = _`
        (fn th => rewrite_tac[th]) >>
      simp[entry_venom_state_frame_fields]) >>
  qpat_x_assum `(entry_venom_state _ _ _).vs_code = _` kall_tac >>
  `LENGTH (entry_venom_state prog cplan es).vs_code <= 24576` by
    gvs[call_state_rel_def, entry_venom_state_frame_fields] >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac
QED

Theorem generated_entry_immutable_code_layout:
  !tops prog am tx es cp policy unit.
  call_state_rel tops (assemble prog) am tx es /\
  codegen_assembly policy unit = SOME prog /\ asm_encoding_wf prog ==>
  code_layout_valid (entry_venom_state prog cp es)
Proof
  rpt strip_tac >> drule codegen_assembly_success_shape >> strip_tac >>
  irule entry_venom_state_code_layout >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[APPEND_ASSOC]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable code layout: " ^ name)
  end) (DB.thms "immutableCodeLayout");
