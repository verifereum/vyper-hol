(* Producers for the asm_opt_finalizer case of the top theorems.
 *
 * The Venom run and the stages S1-S6 are taken on opt_entry_state: the
 * EVM frame es's entry state (its accounts, call trace and GAS readings)
 * with the unoptimized layout, prog's code and labels followed by es's
 * immutables section. codegen_correct_asm_opt then relates that Venom run
 * to the frame es, which runs the optimized code.
 *
 * TOP-LEVEL: compile_vyper_runtime_phases_asm_opt,
 * compile_vyper_runtime_nonempty_asm_opt, opt_entry_state,
 * opt_entry_initial_venom_state_rel, opt_entry_code_layout_valid,
 * opt_entry_fields, opt_entry_codegen_asm_entry_rel,
 * opt_entry_asm_frame_rel, gas_variant_code_layout_valid,
 * o1_pipeline_memory_obligations_raw, o1_pipeline_label_flow_ok,
 * o1_pipeline_sym_unit_static_ok, o1_pipeline_code_end_offset_ok,
 * lower_vyper_runtime_unit_sym_src_ok.
 *)
Theory e2eAsmOpt
Ancestors
  e2eProducers e2eDefs e2eEntry immutableCodeLayout codegenAsmOpt
  codegenLabelDisciplined codegenEntryRel asmFrameRel
  codegenSymRel o1PipelineCorrect compilePhasesProps compileVyper codegen
  asmOptimizer contextCodegenRel unitShapeDefs vyperLoweringCorrect
  contextPlanLayoutProps unitMemInv stepWriteFootprint o1PassContract
  contextRawReachable codegenEncodingWf spillWordBounds symbolResolve asmWf
  memSafeRun lowerDloadDefs
  frameRel codegenRel o1LabelFlowCompose

(* L1 for the optimizer: the runtime is the optimized assembly of the O1
   output's generated assembly. *)
Theorem compile_vyper_runtime_phases_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy unit out prog prog' cplan.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cplan /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cplan.cp_initial_fmp (context_plan_ops cplan) ++
           data_segment_asm out.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    assembly_target_safe rpolicy.rpol_target prog' /\
    runtime_bc = assemble prog'
Proof
  simp[compile_vyper_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_def, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  rename1 `lower_vyper_runtime_unit tops rpolicy = SOME unit` >>
  rename1 `run_venom_pipeline (K T) (K T) (K T)
             rpolicy o1_pipeline_spec unit = SOME out` >>
  qpat_x_assum `codegen_assembly rpolicy out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* compile_vyper_runtime_nonempty for the optimizer. *)
Theorem compile_vyper_runtime_nonempty_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  runtime_bc <> []
Proof
  cheat
QED

(* es's entry state with prog's code and labels: prog's code followed by
   the section es's code has after prog'. *)
Definition opt_entry_state_def:
  opt_entry_state prog prog' cplan es =
    entry_venom_state prog cplan es with
      <| vs_code := assemble prog ++
           DROP (LENGTH (assemble prog')) (FST (HD es.contexts)).msgParams.code;
         vs_data_section :=
           DROP (LENGTH (assemble prog')) (FST (HD es.contexts)).msgParams.code |>
End

(* entry_venom_state_initial_venom_state_rel for opt_entry_state. *)
Theorem opt_entry_initial_venom_state_rel:
  !tops prog prog' am tx es cplan.
  call_state_rel tops (assemble prog') am tx es ==>
  initial_venom_state_rel tops am tx (opt_entry_state prog prog' cplan es)
Proof
  rpt strip_tac >>
  drule_then (qspec_then `cplan` mp_tac) entry_venom_state_initial_venom_state_rel >>
  simp[initial_venom_state_rel_def, venom_env_rel_def, opt_entry_state_def,
       entry_venom_state_frame_fields] >>
  simp[entry_venom_state_def] >> strip_tac >> fs[]
QED

(* code_layout_valid reads no GAS readings. *)
Theorem gas_variant_code_layout_valid:
  gas_variant si so /\ code_layout_valid so ==> code_layout_valid si
Proof
  rw[gas_variant_def] >> qpat_x_assum `so = _` SUBST_ALL_TAC >>
  fs[code_layout_valid_def]
QED

(* generated_entry_code_layout_shape for opt_entry_state. *)
Theorem opt_entry_code_layout_valid:
  !tops prog prog' am tx es cplan policy unit.
  call_state_rel tops (assemble prog') am tx es /\
  codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit ==>
  code_layout_valid (opt_entry_state prog prog' cplan es)
Proof
  rpt strip_tac >>
  drule_all codegen_assembly_asm_encoding_wf >> strip_tac >>
  drule codegen_assembly_success_shape >> strip_tac >>
  `FLOOKUP (SND (compute_label_offsets prog)) "code_end" =
     SOME (LENGTH (assemble prog))` by
    (irule immutable_code_end_length >> fs[] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  `LENGTH (assemble prog) < 65536` by
    (qpat_x_assum `asm_encoding_wf prog` mp_tac >>
     qpat_x_assum `FLOOKUP _ "code_end" = _` mp_tac >>
     Cases_on `compute_label_offsets prog` >>
     simp[asmWfTheory.asm_encoding_wf_def] >> rpt strip_tac >>
     qpat_x_assum `!lbl off. _` drule >> strip_tac >>
     drule spillWordBoundsTheory.encode_num_bytes_length_bound >>
     simp[symbolResolveTheory.symbol_size_def]) >>
  `LENGTH (FST (HD es.contexts)).msgParams.code <= 24576` by
    gvs[call_state_rel_def] >>
  simp[code_layout_valid_def, opt_entry_state_def,
       entry_venom_state_frame_fields] >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  qpat_x_assum `prog = _` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- (qexists_tac `LENGTH (assemble prog)` >> asm_rewrite_tac[]) >>
  decide_tac
QED

(* opt_entry_state reads everything but the code and the layout from es. *)
Theorem opt_entry_fields:
  !tops prog prog' am tx es cplan vs.
  call_state_rel tops (assemble prog') am tx es /\
  vs = opt_entry_state prog prog' cplan es ==>
    vs.vs_outcomes = MAP SND (call_trace es) /\
    vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
    vs.vs_call_ctx.cc_calldata =
      buffer_to_list (FST (HD es.contexts)).msgParams.data /\
    vs.vs_fmp = vs.vs_initial_fmp /\ ~vs.vs_call_ctx.cc_static /\
    o1_initial_state_ok vs /\
    vs.vs_code = assemble prog ++ vs.vs_data_section
Proof
  rpt strip_tac >> gvs[] >>
  simp[opt_entry_state_def, entry_venom_state_frame_fields,
       entry_venom_state_fresh, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  gvs[call_state_rel_def, entry_venom_state_def, opt_entry_state_def]
QED

(* initial_ctx_codegen_asm_entry_rel for opt_entry_state: the entry
   assembly state relates to it for prog's layout. *)
Theorem opt_entry_codegen_asm_entry_rel:
  !tops prog prog' am tx es cplan u.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u ==>
  codegen_asm_entry_rel cplan prog (opt_entry_state prog prog' cplan es)
    (entry_asm_state (opt_entry_state prog prog' cplan es) es)
Proof
  rpt strip_tac >>
  simp[codegen_asm_entry_rel_def, entry_asm_state_def, shared_state_rel_def,
       venom_asm_terminal_rel_def, opt_entry_state_def,
       entry_venom_state_frame_fields, entry_venom_state_fresh] >>
  gvs[call_state_rel_def, entry_venom_state_def, venomStateTheory.init_venom_state_def,
      context_memory_rel_def]
QED

(* asm_frame_rel_entry for opt_entry_state: the frame es runs prog''s
   code from the entry assembly state with that code. *)
Theorem opt_entry_asm_frame_rel:
  !tops prog prog' am tx es cplan u.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u /\
  assemble prog' <> [] ==>
  asm_frame_rel prog' (opt_entry_state prog prog' cplan es).vs_data_section es
    (entry_asm_state (opt_entry_state prog prog' cplan es) es with
       as_code := assemble prog' ++
         (opt_entry_state prog prog' cplan es).vs_data_section) es
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`u`, `cplan`] assume_tac)
    entry_venom_state_initial_ctx_rel >>
  drule_then (qspec_then `cplan` strip_assume_tac)
    entry_venom_state_installed_section >>
  fs[entry_venom_state_frame_fields] >>
  `account_already_created
     (lookup_account (FST (HD es.contexts)).msgParams.callee
        es.rollback.accounts)` by
    (`(FST (HD es.contexts)).msgParams.code <> []` by
       (strip_tac >> fs[]) >>
     gvs[call_state_rel_def, vfmExecutionTheory.account_already_created_def,
         listTheory.NULL_EQ]) >>
  `asm_frame_rel prog' (entry_venom_state prog' cplan es).vs_data_section es
     (entry_asm_state (entry_venom_state prog' cplan es) es) es` by
    metis_tac[asm_frame_rel_entry] >>
  `entry_asm_state (opt_entry_state prog prog' cplan es) es with
     as_code := assemble prog' ++
       (opt_entry_state prog prog' cplan es).vs_data_section =
   entry_asm_state (entry_venom_state prog' cplan es) es` by
    (qpat_assum `_ = assemble prog' ++ _` (fn th => REWRITE_TAC [GSYM th]) >>
     simp[opt_entry_state_def, entry_asm_state_def] >>
     simp[entry_venom_state_def] >>
     qpat_x_assum `_ = assemble prog' ++ _` (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `entry_asm_state _ _ with as_code := _ = _` SUBST1_TAC >>
  fs[opt_entry_state_def, entry_venom_state_frame_fields]
QED

(* ===== Static facts of the O1 output the label discipline needs ===== *)

(* o1_pipeline_memory_obligations with its invariant named: the states
   reachable from vs. *)
Theorem o1_pipeline_memory_obligations_raw:
  !out cplan vs.
    generate_context_plan out.po_unit.cu_context = SOME cplan /\
    o1_lowered_inv out.po_unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cplan.cp_initial_fmp
    ==>
    codegen_memory_obligations (raw_reachable vs) out.po_unit.cu_context cplan /\
    codegen_reachability_package (raw_reachable vs) out.po_unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  `?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
         mem_inv (lowered_mem_ok eom (w2n vs.vs_initial_fmp))
           out.po_unit.cu_context vs` by
    (fs[o1_lowered_inv_def, mem_inv_raw_reachable] >>
     rpt strip_tac >> first_x_assum drule >>
     drule ctxLookupAgreeTheory.raw_reachable_initial_fmp >>
     simp[lowered_mem_fact_def]) >>
  gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  metis_tac[mem_inv_codegen_obligations, step_write_footprint_holds]
QED

(* ===== The O1 pipeline's static and offset facts for the optimizer case ===== *)

(* label_flow_ok survives O1: LowerDload's code_end ADD feeds only its own
   CODECOPY, and the later passes copy such a pointer only by ASSIGN. *)
Theorem o1_pipeline_label_flow_ok:
  !rpolicy unit out.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  label_flow_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) ==>
  label_flow_ok out.po_unit.cu_context
Proof
  ACCEPT_TAC o1_pipeline_label_flow_preserved
QED

(* O1 keeps the data segment and makes INVOKE targets well formed. *)
Theorem o1_pipeline_sym_unit_static_ok:
  !rpolicy unit out.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) ==>
  sym_unit_static_ok out.po_unit
Proof
  cheat
QED

(* run_venom_pipeline_correct, also carrying the source's DLOAD offset
   bound (every offset within the data section, shorter than 2^255) to the
   O1 output's code_end ADDs. *)
Theorem o1_pipeline_code_end_offset_ok:
  !D lo rpolicy unit out vs_out.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\ o1_run_state_ok vs_out /\
    reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    fixed_region_reserved lo unit.cu_context /\ dead_wf D /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "code_end") inst.inst_operands) /\
    LENGTH vs_out.vs_data_section < dimword (:256) DIV 2
    ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (raw_unit_memory_ok unit.cu_context vs_in /\
       ptr_discipline lo unit.cu_context vs_in /\
       taint_within D unit.cu_context vs_in /\
       mem_inv dload_offset_ok unit.cu_context vs_in /\
       mem_inv dload_headroom_ok unit.cu_context vs_in /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vs_in.vs_code /\
                               s.vs_data_section = vs_in.vs_data_section)
         unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out /\
       code_end_offset_ok (raw_reachable vs_out) out.po_unit.cu_context)
Proof
  cheat
QED

(* The runtime unit's source-side static facts: no CODESIZE, CODECOPY only
   from runtime_begin, no code_end label yet, and a byte-only data segment
   (empty under Linear dispatch). *)
Theorem lower_vyper_runtime_unit_sym_src_ok:
  !tops rpolicy unit.
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  label_flow_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)
Proof
  cheat
QED
