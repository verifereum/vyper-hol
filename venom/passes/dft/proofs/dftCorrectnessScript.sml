(*
 * DFT Pass — Correctness
 *
 * Instruction reordering preserves semantics when the reordered
 * sequence respects all data and effect dependencies.
 *
 * Key properties:
 *   1. Data deps preserved: operand producers appear earlier
 *   2. Effect deps preserved: RAW/WAR/WAW ordering maintained
 *   3. Independent instructions commute
 *
 * TOP-LEVEL:
 *   independent_commute          — independent instructions commute
 *   dft_block_simulates          — block-level simulation
 *   dft_pass_correct             — pass correctness
 *)

Theory dftCorrectness
Ancestors
  dftDefs passSimulationDefs passSimulationProofs
  stateEquiv stateEquivProofs venomExecSemantics venomExecProps venomEffects
  execEquivParamProofs
Libs
  venomExecSemanticsTheory

(* ===== Valid topological ordering ===== *)

Definition valid_topo_order_def:
  valid_topo_order block_insts order eda reordered <=>
    PERM reordered (FILTER (\i. ~is_pseudo i.inst_opcode) block_insts) /\
    !i j.
      i < j /\ j < LENGTH reordered ==>
      ~MEM (EL j reordered)
           (inst_all_deps block_insts order eda (EL i reordered))
End

(* ===== Independent instructions commute ===== *)

Definition independent_insts_def:
  independent_insts block_insts order eda inst1 inst2 <=>
    ~MEM inst1 (inst_all_deps block_insts order eda inst2) /\
    ~MEM inst2 (inst_all_deps block_insts order eda inst1)
End

Theorem independent_commute:
  !fuel ctx inst1 inst2 s.
    (* No data dependency: operands don't use each other's outputs *)
    DISJOINT (set inst1.inst_outputs)
             (set (MAP (\op. case op of Var v => v | _ => "")
                       inst2.inst_operands)) /\
    DISJOINT (set inst2.inst_outputs)
             (set (MAP (\op. case op of Var v => v | _ => "")
                       inst1.inst_operands)) /\
    (* No output aliasing *)
    DISJOINT (set inst1.inst_outputs) (set inst2.inst_outputs) /\
    (* No effect conflict: read/write effects don't interfere *)
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    (* ALLOCA modifies vs_allocas (untracked by effects system) which
       INVOKE reads via setup_callee — exclude from commutativity *)
    ~is_alloca_op inst1.inst_opcode /\
    ~is_alloca_op inst2.inst_opcode ==>
    (case step_inst fuel ctx inst1 s of
       OK s1 => step_inst fuel ctx inst2 s1
     | other => other)
    =
    (case step_inst fuel ctx inst2 s of
       OK s2 => step_inst fuel ctx inst1 s2
     | other => other)
Proof
  cheat
QED

(* ===== Block simulation ===== *)

(* CHEATED: Block simulation for DFT reordering.
   Requires the reordered instructions to respect all dependencies.
   The DFT algorithm produces a valid topological order by construction. *)
Theorem dft_block_simulates:
  !order eda fuel ctx bb s.
    s.vs_inst_idx = 0 /\
    valid_topo_order bb.bb_instructions order eda
                     (dft_block order bb).bb_instructions ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (run_block fuel ctx bb s)
      (run_block fuel ctx (dft_block order bb) s)
Proof
  cheat
QED

(* ===== Helper lemmas ===== *)

Theorem dft_block_label[simp]:
  !order bb. (dft_block order bb).bb_label = bb.bb_label
Proof
  rw[dft_block_def]
QED

(* ===== Function-level correctness ===== *)

(* CHEATED: dft_fn now includes StackOrderAnalysis convergence loop.
   Correctness proof must account for the iterative scheduling. *)
Theorem dft_function_correct:
  !fn fuel ctx s.
    (!bb order. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result (state_equiv {}) (execution_equiv {})
          (run_block fuel ctx bb s)
          (run_block fuel ctx (dft_block order bb) s)) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dft_fn fn) s)
Proof
  cheat
QED

(* ===== Pass correctness ===== *)

(* TODO: needs fuel determinism proof.
   For now, cheated pending fuel determinism infrastructure. *)
Theorem dft_pass_correct:
  !fn ctx s.
    (!bb order. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result (state_equiv {}) (execution_equiv {})
          (run_block fuel ctx bb s)
          (run_block fuel ctx (dft_block order bb) s)) ==>
    pass_correct {}
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (dft_fn fn) s)
Proof
  cheat
QED

(* ===== Obligations ===== *)

(* DFT only reorders instructions within blocks — no new outputs. *)
Theorem dft_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (dft_fn fn)
Proof
  cheat
QED

Theorem dft_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (dft_fn fn)
Proof
  cheat
QED

(* DFT is the only pass that runs after SUE — must preserve sue form. *)
Theorem dft_preserves_single_use_form:
  ∀fn. single_use_form fn ⇒ single_use_form (dft_fn fn)
Proof
  cheat
QED
