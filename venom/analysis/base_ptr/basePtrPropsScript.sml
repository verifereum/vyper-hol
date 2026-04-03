(*
 * Base Pointer Analysis — Properties
 *
 * Public API for base pointer analysis consumers.
 *
 * Frame/lookup:
 *   bp_get_ptrs_update_same, bp_get_ptrs_update_diff, bp_get_ptrs_fempty,
 *   bp_handle_inst_other_var, bp_handle_inst_no_output_unchanged
 *
 * Soundness:
 *   ptr_matches_var       — a pointer correctly describes a variable's runtime value
 *   bp_ptr_sound          — all tracked variables match some pointer in their set
 *   bp_handle_inst_sound  — transfer function preserves bp_ptr_sound
 *   bp_process_block_sound — block-level soundness preservation
 *   bp_ptr_from_op_sound  — singleton pointer ⇒ exact runtime address
 *   bp_segment_from_ops_sound — alloca-backed mem_loc ⇒ runtime address
 *   bp_segment_from_ops_lit   — literal offset mem_loc (trivial)
 *)

Theory basePtrProps
Ancestors
  basePtrDefs basePtrProofs venomExecSemantics venomWf passSharedDefs
  memLocDefs finite_map
Libs
  pred_setLib

(* ===== bp_get_ptrs lookup lemmas ===== *)

Theorem bp_get_ptrs_update_same:
  ∀result k v. bp_get_ptrs (result |+ (k, v)) k = v
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_update_diff:
  ∀result k1 k2 v. k1 ≠ k2 ⇒
    bp_get_ptrs (result |+ (k1, v)) k2 = bp_get_ptrs result k2
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_fempty:
  ∀v. bp_get_ptrs FEMPTY v = []
Proof
  rw[bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* ===== bp_handle_inst frame ===== *)

(* Transfer function only modifies the output variable's pointer set.
 * Needed for any analysis that reasons about variables not defined by inst. *)
Theorem bp_handle_inst_other_var:
  ∀result inst c r v.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_other_var_proof
QED

(* No-output instructions don't modify the pointer map at all. *)
Theorem bp_handle_inst_no_output_unchanged:
  ∀result inst c r.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_no_output_unchanged_proof
QED

(* ===== Soundness Definitions ===== *)

(* A pointer correctly describes a variable's runtime value.
   Known offset: v holds n2w(alloca_base + off).
   Unknown offset: v holds n2w(alloca_base + delta) for some delta. *)
Definition ptr_matches_var_def:
  ptr_matches_var (Ptr (Allocation aid) (SOME off)) v s =
    (∃base sz.
       FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
       lookup_var v s = SOME (n2w (base + off))) ∧
  ptr_matches_var (Ptr (Allocation aid) NONE) v s =
    (∃base sz delta.
       FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
       lookup_var v s = SOME (n2w (base + delta)))
End

(* Every tracked variable with a defined runtime value matches some
   pointer in its tracked set (over-approximation soundness).
   Variables that are undefined (not yet assigned) are unconstrained
   since the analysis runs over all blocks including unexecuted ones. *)
Definition bp_ptr_sound_def:
  bp_ptr_sound (bp : bp_result) (s : venom_state) ⇔
    ∀v. bp_get_ptrs bp v ≠ [] ∧ IS_SOME (lookup_var v s) ⇒
      ∃p. MEM p (bp_get_ptrs bp v) ∧ ptr_matches_var p v s
End

(* Initialization: analysis starts from FEMPTY, which is trivially sound. *)
Theorem bp_ptr_sound_init:
  ∀s. bp_ptr_sound FEMPTY s
Proof
  rw[bp_ptr_sound_def, bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* ===== Buffer Safety: Pointer Offsets Within Alloca Bounds ===== *)

(* Every tracked pointer with a known offset has that offset within
 * the alloca's allocated size. Needed for byte-for-byte precision
 * of aliasing analysis (sub_offset_by stays non-negative).
 *
 * Without this: analysis is sound but conservative (NONE for OOB).
 * With this: analysis matches Python precision for valid programs.
 *
 * Discharged by construction from Vyper→Venom lowering:
 * all pointer arithmetic uses compile-time-known offsets within
 * the alloca's declared size.
 *
 *)
Definition bp_ptrs_bounded_def:
  bp_ptrs_bounded (bp : bp_result) (s : venom_state) ⇔
    ∀v aid off.
      MEM (Ptr (Allocation aid) (SOME off)) (bp_get_ptrs bp v) ⇒
      ∀base sz.
        FLOOKUP s.vs_allocas aid = SOME (base, sz) ⇒ off ≤ sz
End

(* ===== Soundness Theorems ===== *)

(* Transfer function preserves bp_ptr_sound through a successful step.
   Fresh-output precondition: the output variable must not already
   have pointer info. Under SSA (each variable defined once) this
   is automatic. Without SSA, stale pointers for re-defined variables
   would be unsound. *)
Theorem bp_handle_inst_sound:
  ∀bp inst c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_handle_inst bp inst = (c, bp') ∧
    step_inst fuel ctx inst s = OK s' ∧
    inst_wf inst ∧
    (∀out. inst_output inst = SOME out ⇒ bp_get_ptrs bp out = []) ⇒
    bp_ptr_sound bp' s'
Proof
  cheat
QED

(* Block-level: processing a block preserves soundness through run_block.
   Fresh-output: no instruction's output variable has prior pointer info
   at the time that instruction is processed. Under SSA this is automatic. *)
Theorem bp_process_block_sound:
  ∀bp bb c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_process_block bp bb.bb_instructions = (c, bp') ∧
    run_block fuel ctx bb s = OK s' ∧
    s.vs_inst_idx = 0 ∧
    (∀inst. MEM inst bb.bb_instructions ⇒ inst_wf inst) ∧
    (* SSA-like: each output variable is fresh (not already tracked) *)
    ALL_DISTINCT (FLAT (MAP (λi. i.inst_outputs) bb.bb_instructions)) ∧
    (∀inst out. MEM inst bb.bb_instructions ∧
               inst_output inst = SOME out ⇒
               bp_get_ptrs bp out = []) ⇒
    bp_ptr_sound bp' s'
Proof
  cheat
QED

(* Singleton pointer ⇒ exact runtime address.
   When bp_ptr_from_op returns a unique pointer with known offset,
   the variable holds exactly n2w(alloca_base + off). *)
Theorem bp_ptr_from_op_sound:
  ∀bp v aid off s.
    bp_ptr_sound bp s ∧
    bp_ptr_from_op bp (Var v) = SOME (Ptr (Allocation aid) (SOME off)) ∧
    IS_SOME (eval_operand (Var v) s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand (Var v) s = SOME (n2w (base + off))
Proof
  cheat
QED

(* Alloca-backed mem_loc correctly describes runtime address.
   When bp_segment_from_ops returns a fixed location with known alloca,
   the offset operand evaluates to n2w(alloca_base + ml_offset). *)
Theorem bp_segment_from_ops_sound:
  ∀bp ops ml aid off s.
    bp_ptr_sound bp s ∧
    bp_segment_from_ops bp ops = ml ∧
    ml_is_fixed ml ∧
    ml.ml_alloca = SOME (Allocation aid) ∧
    ml.ml_offset = SOME off ∧
    IS_SOME (eval_operand ops.iao_ofst s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand ops.iao_ofst s = SOME (n2w (base + off))
Proof
  cheat
QED

(* Literal offset: bp_segment_from_ops with Lit operand returns
   ml_alloca = NONE with ml_offset = w2n of the literal. *)
Theorem bp_segment_from_ops_lit_offset:
  ∀bp (n : bytes32) sz_op.
    (bp_segment_from_ops bp
      <| iao_ofst := Lit n; iao_size := sz_op;
         iao_max_size := sz_op |>).ml_offset = SOME (w2n n) ∧
    (bp_segment_from_ops bp
      <| iao_ofst := Lit n; iao_size := sz_op;
         iao_max_size := sz_op |>).ml_alloca = NONE
Proof
  simp[bp_segment_from_ops_def, LET_THM]
QED

