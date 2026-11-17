(*
 * Symbolic assembly with fixed own-code bytes supplied to each step.
 * The source and finalized programs share these bytes, independently of
 * their instruction lists and of the data-label environment. Keeping them
 * outside sym_state leaves sym_init and the existing contract unchanged.
 *
 * TOP-LEVEL:
 *   sym_codecopy_own, sym_step_op_own, sym_step_own, sym_run_own
 *   label_disciplined_own, asm_refines_own, finalizer_correct_own
 *)

Theory asmSymOwnCode
Ancestors
  asmSymSem asmSem

(* Label sources retain the existing data-read discipline; concrete
   sources read the supplied own-code bytes with asmSem's zero padding. *)
Definition sym_codecopy_own_def:
  sym_codecopy_own p env own ss =
    case ss.sym_stack of
      Val dst :: Lab l d :: Val sz :: stk =>
        if sym_data_label p env l ∧ sym_delta_ok d then
          sym_lift 3
            (mem_labels_clear ss.sym_mem_labels
               (in_mem_range (w2n dst) (w2n sz))) ss
            (asm_copy_to_mem (DROP d (env ' l))
               (ss.sym_base with as_stack := [dst; 0w; sz]))
        else SymBad "CODECOPY from a code label"
    | Val dst :: Val src :: Val sz :: stk =>
        sym_lift 3
          (mem_labels_clear ss.sym_mem_labels
             (in_mem_range (w2n dst) (w2n sz))) ss
          (asm_copy_to_mem own
             (ss.sym_base with as_stack := [dst; src; sz]))
    | _ =>
        if LENGTH ss.sym_stack < 3 then SymError "codecopy: stack underflow"
        else SymBad "CODECOPY of the code bytes"
End

(* Only own-code reads differ from sym_step_op. *)
Definition sym_step_op_own_def:
  sym_step_op_own p env own name ss =
    if name = "CODESIZE" then
      sym_set_stack (Val (n2w (LENGTH own)) :: ss.sym_stack) ss
    else if name = "CODECOPY" then sym_codecopy_own p env own ss
    else sym_step_op p env name ss
End

(* Non-opcode instructions use the existing symbolic step. *)
Definition sym_step_own_def:
  sym_step_own p env own inst ss =
    case inst of
      AsmOp name => sym_step_op_own p env own name ss
    | _ => sym_step p env inst ss
End

(* Own-code bytes stay fixed throughout the fuel-based run. *)
Definition sym_run_own_def:
  sym_run_own p env own (fuel:num) ss =
    if fuel = 0 then SymError "out of fuel"
    else if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
    else
      case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_run_own p env own (fuel - 1) ss'
      | r => r
Termination
  WF_REL_TAC `measure (λ(_, _, _, fuel, _). fuel)`
End

(* Label misuse is excluded for every fuel at the fixed own-code bytes. *)
Definition label_disciplined_own_def:
  label_disciplined_own env own p s ⇔
    asm_static_wf p ∧
    ∀fuel msg. sym_run_own p env own fuel (sym_init s) ≠ SymBad msg
End

(* Both programs read the same own-code bytes and data environment. *)
Definition asm_refines_own_def:
  asm_refines_own p p' ⇔
    asm_static_wf p ⇒
    asm_static_wf p' ∧
    FILTER is_data_inst p' = FILTER is_data_inst p ∧
    ∀env own s fuel.
      sym_terminal (sym_run_own p env own fuel (sym_init s)) ⇒
      ∃fuel'. sym_result_rel (sym_run_own p env own fuel (sym_init s))
                             (sym_run_own p' env own fuel' (sym_init s))
End

(* Successful finalization preserves the own-code symbolic observations. *)
Definition finalizer_correct_own_def:
  finalizer_correct_own (f : assembly_finalizer) ⇔
    ∀rp p p'. f rp p = SOME p' ⇒ asm_refines_own p p'
End

(* Target statements for the next proof layers; these are not theorems
   exported by this definitions theory.

   prune_unreachable_code_refines_own:
     ∀p. asm_refines_own p (FST (prune_unreachable_code p))

   merge_iszero_refines_own:
     ∀p. asm_refines_own p (FST (merge_iszero p))

   merge_jumpdests_refines_own:
     ∀p. asm_refines_own p (FST (merge_jumpdests p))

   prune_inefficient_jumps_refines_own:
     ∀p. asm_refines_own p (FST (prune_inefficient_jumps p))

   optimize_inefficient_jumps_refines_own:
     ∀p. asm_refines_own p (FST (optimize_inefficient_jumps p))

   prune_unused_jumpdests_refines_own:
     ∀p. asm_refines_own p (FST (prune_unused_jumpdests p))

   stack_peephole_opts_refines_own:
     ∀p p' c. stack_peephole_opts p = SOME (p', c) ⇒ asm_refines_own p p'

   asm_opt_finalizer_refines_own:
     asm_opt_finalizer rp p = SOME p' ⇒ asm_refines_own p p'

   asm_sym_backward_own:
     asm_static_wf p ∧
     s.as_pc = 0 ∧
     asm_data_env_ok p env s.as_code ∧
     sym_terminal (sym_run_own p env s.as_code fuel (sym_init s))
     ⇒
     ∃n.
       sym_result_rel
         (sym_run_own p env s.as_code fuel (sym_init s))
         (asm_result_sym
           (asm_steps (SND (compute_label_offsets p))
                      (build_offset_to_pc p) p n s))
 *)
