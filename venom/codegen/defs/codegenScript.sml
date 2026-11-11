(*
 * Unit-based, target-aware Venom -> EVM code generation.
 *
 * Planning and plan execution produce checked assembly.  Byte assembly occurs
 * only after an explicit finalizer callback has returned another checked
 * assembly program.
 *)

Theory codegen
Ancestors
  asmTargetSafety
  assemblyFinalizer
  mergesort

(* The assembler's symbol checks.  Every AsmLabel and AsmDataHeader defines
   a symbol, and a name defined twice is an error, as in Python's
   _add_to_symbol_map (vyper/evm/assembler/symbols.py), which rejects a
   duplicate among labels, data headers and code_end; compute_label_offsets
   would otherwise let the later definition overwrite the earlier.  The
   names are distinct iff sorting them leaves them strictly increasing;
   that form is checked because ALL_DISTINCT over strings is quadratic
   under EVAL, too slow for the bytecode fixtures (asm_symbols_ok_distinct
   gives ALL_DISTINCT back).  The program must also fit the 2-byte label
   pushes (SYMBOL_SIZE = 2), so every offset compute_label_offsets assigns
   is below 65536. *)
Definition asm_defined_symbols_def:
  asm_defined_symbols (AsmLabel l) = [l] /\
  asm_defined_symbols (AsmDataHeader l) = [l] /\
  asm_defined_symbols _ = []
End

Definition asm_symbols_ok_def:
  asm_symbols_ok asm <=>
    SORTED string_lt
      (mergesort string_lt (FLAT (MAP asm_defined_symbols asm))) /\
    SUM (MAP asm_inst_size asm) < 65536
End

Theorem asm_symbols_ok_distinct:
  asm_symbols_ok asm ==> ALL_DISTINCT (FLAT (MAP asm_defined_symbols asm))
Proof
  rw[asm_symbols_ok_def] >>
  `ALL_DISTINCT (mergesort string_lt (FLAT (MAP asm_defined_symbols asm)))`
    by (irule sortingTheory.SORTED_ALL_DISTINCT >>
        qexists_tac `string_lt` >>
        simp[relationTheory.irreflexive_def, relationTheory.transitive_def,
             stringTheory.string_lt_nonrefl] >>
        metis_tac[stringTheory.string_lt_trans]) >>
  metis_tac[sortingTheory.ALL_DISTINCT_PERM, mergesortTheory.mergesort_perm]
QED

Definition codegen_assembly_def:
  codegen_assembly (rpolicy : resolved_compiler_policy)
                   (unit : compilation_unit) : asm_inst list option =
    if ~target_capabilities_wf rpolicy.rpol_target then NONE
    else if ~context_target_safe rpolicy.rpol_target unit.cu_context then NONE
    else
      case generate_context_plan unit.cu_context of
        NONE => NONE
      | SOME plan =>
          let asm =
            execute_plan plan.cp_initial_fmp (context_plan_ops plan) ++
            data_segment_asm unit.cu_data_segment ++
            [AsmDataHeader "code_end"]
          in
            if assembly_target_safe rpolicy.rpol_target asm /\
               asm_symbols_ok asm
            then SOME asm
            else NONE
End

Definition codegen_assembly_fuel_def:
  codegen_assembly_fuel fuel (rpolicy : resolved_compiler_policy)
                           (unit : compilation_unit) : asm_inst list option =
    if ~target_capabilities_wf rpolicy.rpol_target then NONE
    else if ~context_target_safe rpolicy.rpol_target unit.cu_context then NONE
    else
      case generate_context_plan_fuel fuel unit.cu_context of
        NONE => NONE
      | SOME plan =>
          let asm =
            execute_plan plan.cp_initial_fmp (context_plan_ops plan) ++
            data_segment_asm unit.cu_data_segment ++
            [AsmDataHeader "code_end"]
          in
            if assembly_target_safe rpolicy.rpol_target asm /\
               asm_symbols_ok asm
            then SOME asm
            else NONE
End

Definition finalize_codegen_def:
  finalize_codegen (finalizer : assembly_finalizer)
                   (rpolicy : resolved_compiler_policy)
                   (unit : compilation_unit) : byte list option =
    case codegen_assembly rpolicy unit of
      NONE => NONE
    | SOME asm =>
        case finalizer rpolicy asm of
          NONE => NONE
        | SOME finalized_asm =>
            if assembly_target_safe rpolicy.rpol_target finalized_asm
            then SOME (assemble finalized_asm)
            else NONE
End

(* The fixture profile uses the identity finalizer.  codegen_assembly has
   already checked target safety, so do not traverse the complete assembly a
   second time merely to rediscover the same fact during CBV evaluation. *)
Theorem finalize_codegen_identity[compute]:
  finalize_codegen (K SOME) rpolicy unit =
    OPTION_MAP assemble (codegen_assembly rpolicy unit)
Proof
  Cases_on `codegen_assembly rpolicy unit` >> simp[finalize_codegen_def] >>
  `assembly_target_safe rpolicy.rpol_target x` by
    (qpat_x_assum `codegen_assembly rpolicy unit = SOME x` mp_tac >>
     simp[codegen_assembly_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  simp[]
QED
