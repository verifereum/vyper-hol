(* The actual installed suffix starts at the final code_end header. The
   assembler's existing encoding-wellformedness condition is essential:
   symbol fields use fixed widths in layout but encode arbitrary naturals. *)
Theory immutableCodeLayout
Ancestors
  e2eDefs e2eEntry e2eProducers lowerDloadDefs asmEncodeParse asmToBytecodeProofs
  asmWf asmSem asmIR symbolResolve finite_map list arithmetic
  stackPlanGen planExec codegen
  rich_list codegenRel codegenEncodingWf codegenAsmStaticWf
  asmOptEncodingLayout asmOptimizer fnPlanPlaceRevertPostamble

Theorem immutable_runtime_codegen_nonempty:
  codegen_assembly policy unit = SOME prog ==> assemble prog <> []
Proof
  strip_tac >> drule codegen_assembly_success_shape >> strip_tac >>
  gvs[assemble_def, context_plan_ops_def, execute_plan_def, MAP_APPEND,
      FLAT_APPEND, revert_postamble_def, exec_stack_op_def, encode_inst_def] >>
  pairarg_tac >> simp[]
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
    (drule call_state_rel_code_length >>
     simp[entry_venom_state_frame_fields]) >>
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

(* unit_shape_ok rules out OFFSET, the only source of unbounded push
   offsets, and codegen_assembly bounds the code size, so codegen's output
   meets asm_encoding_wf. *)
Theorem generated_entry_code_layout_shape:
  !tops prog am tx es cp policy unit.
  call_state_rel tops (assemble prog) am tx es /\
  codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit ==>
  code_layout_valid (entry_venom_state prog cp es)
Proof
  rpt strip_tac >>
  drule_all codegen_assembly_asm_encoding_wf >> strip_tac >>
  metis_tac[generated_entry_immutable_code_layout]
QED

Theorem opt_entry_code_layout_valid_own:
  !fin tops rpolicy prog prog' am tx es cplan unit.
  fin IN accepted_finalizers /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  fin rpolicy prog = SOME prog' /\
  call_state_rel tops (assemble prog') am tx es ==>
  code_layout_valid (opt_entry_state_own prog prog' cplan es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `fin = K SOME`
  >- (gvs[combinTheory.K_THM, opt_entry_state_own_identity] >>
      metis_tac[generated_entry_code_layout_shape]) >>
  `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum SUBST_ALL_TAC >>
  drule codegen_assembly_success_shape >> strip_tac >>
  `?prefix. prog = prefix ++ [AsmDataHeader "code_end"]` by metis_tac[APPEND_ASSOC] >>
  `~MEM (AsmLabel "code_end") prog` by
    (drule codegen_assembly_symbols >> simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  `asm_encoding_wf prog /\ !lbl d. ~MEM (AsmPushOfst lbl d) prog` by
    metis_tac[codegen_assembly_asm_encoding_wf, codegen_assembly_no_push_ofst] >>
  drule_then (qspec_then `cplan` strip_assume_tac)
    entry_venom_state_installed_section >>
  `LENGTH (entry_venom_state prog' cplan es).vs_code <= 24576` by
    (drule call_state_rel_code_length >> simp_tac bool_ss [entry_venom_state_frame_fields]) >>
  `LENGTH (assemble prog') < 65536` by
    (qpat_assum `(entry_venom_state _ _ _).vs_code = _` (fn eq =>
       qpat_assum `LENGTH (entry_venom_state _ _ _).vs_code <= _`
         (mp_tac o REWRITE_RULE [eq, LENGTH_APPEND])) >> decide_tac) >>
  drule_all asm_opt_finalizer_end_offset >> strip_tac >>
  `FLOOKUP (lo_reloc prog prog') "code_end" =
    FLOOKUP (SND (compute_label_offsets prog')) "code_end"` by
    (qpat_assum `~MEM (AsmLabel "code_end") prog` (fn absent =>
       simp_tac (srw_ss()) [lo_reloc_def, FLOOKUP_FUNION, FLOOKUP_DRESTRICT, absent])) >>
  mp_tac (Q.SPECL [`tops`, `prog'`, `am`, `tx`, `es`, `cplan`, `head`]
    entry_venom_state_code_layout) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  Cases_on `FLOOKUP (SND (compute_label_offsets prog')) "code_end"` >>
  qpat_assum `FLOOKUP (SND (compute_label_offsets prog')) "code_end" = _`
    (fn lookup => qpat_assum `FLOOKUP (lo_reloc _ _) _ = _` (fn labels =>
      simp_tac (srw_ss()) [code_layout_valid_def, opt_entry_state_own_def,
        entry_venom_state_frame_fields, FLOOKUP_o_f, labels, lookup]))
QED
