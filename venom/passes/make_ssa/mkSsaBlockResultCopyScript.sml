(*
 * SSA Construction Block-Level: Result Equivalence for Copy and Control Ops
 *
 * TOP-LEVEL:
 *   - calldatacopy_result_ssa_equiv
 *   - returndatacopy_result_ssa_equiv
 *   - assign_result_ssa_equiv
 *   - jmp_result_ssa_equiv
 *   - jnz_result_ssa_equiv
 *)

Theory mkSsaBlockResultCopy
Ancestors
  mkSsaBlockResultContext mkSsaBlockResultCore mkSsaBlockCompat
  mkSsaStateEquiv venomSem

(* Helper: CALLDATACOPY gives ssa_result_equiv with SAME vm. *)
Theorem calldatacopy_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "calldatacopy requires 3 operands"
       | [op_size] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_orig of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_orig of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_orig of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      OK
                        (write_memory_with_expansion (w2n destOffset)
                           (TAKE (w2n size_val)
                              (DROP (w2n offset) s_orig.vs_call_ctx.cc_calldata ++
                               REPLICATE (w2n size_val) 0w)) s_orig))
       | op_size::op_offset::op_destOffset::v10 => Error "calldatacopy requires 3 operands")
      (case inst_ssa.inst_operands of
         [] => Error "calldatacopy requires 3 operands"
       | [op_size] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset] => Error "calldatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_ssa of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_ssa of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_ssa of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      OK
                        (write_memory_with_expansion (w2n destOffset)
                           (TAKE (w2n size_val)
                              (DROP (w2n offset) s_ssa.vs_call_ctx.cc_calldata ++
                               REPLICATE (w2n size_val) 0w)) s_ssa))
       | op_size::op_offset::op_destOffset::v10 => Error "calldatacopy requires 3 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  simp[option_triple_case] >>
  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[ssa_result_equiv_def],
       (Cases_on `t'` >| [
          gvs[ssa_result_equiv_def],
          (rename1 `h''::t_tail` >>
           Cases_on `t_tail` >| [
             (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              gvs[] >>
              Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h'') s_ssa` >>
              gvs[ssa_result_equiv_def, AllCaseEqs()] >>
              `s_orig.vs_call_ctx = s_ssa.vs_call_ctx` by fs[ssa_state_equiv_def] >>
              pop_assum (fn eq => simp_tac std_ss [eq]) >>
              irule write_memory_with_expansion_ssa_equiv >>
              simp[]),
             gvs[ssa_result_equiv_def]
           ])
        ])
     ])
  ]
QED

(* Helper: RETURNDATACOPY gives ssa_result_equiv with SAME vm. *)
Theorem returndatacopy_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "returndatacopy requires 3 operands"
       | [op_size] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_orig of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_orig of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_orig of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      if w2n offset + w2n size_val > LENGTH s_orig.vs_returndata then
                        Revert (revert_state s_orig)
                      else
                        OK
                          (write_memory_with_expansion (w2n destOffset)
                             (TAKE (w2n size_val)
                                (DROP (w2n offset) s_orig.vs_returndata)) s_orig))
       | op_size::op_offset::op_destOffset::v10 => Error "returndatacopy requires 3 operands")
      (case inst_ssa.inst_operands of
         [] => Error "returndatacopy requires 3 operands"
       | [op_size] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset] => Error "returndatacopy requires 3 operands"
       | [op_size; op_offset; op_destOffset] =>
         (case eval_operand op_size s_ssa of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_ssa of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case eval_operand op_destOffset s_ssa of
                    NONE => Error "undefined operand"
                  | SOME destOffset =>
                      if w2n offset + w2n size_val > LENGTH s_ssa.vs_returndata then
                        Revert (revert_state s_ssa)
                      else
                        OK
                          (write_memory_with_expansion (w2n destOffset)
                             (TAKE (w2n size_val)
                                (DROP (w2n offset) s_ssa.vs_returndata)) s_ssa))
       | op_size::op_offset::op_destOffset::v10 => Error "returndatacopy requires 3 operands")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  simp[option_triple_case] >>
  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[ssa_result_equiv_def],
       (Cases_on `t'` >| [
          gvs[ssa_result_equiv_def],
          (rename1 `h''::t_tail` >>
           Cases_on `t_tail` >| [
             (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
                (irule eval_operand_ssa_equiv >> simp[]) >>
              gvs[] >>
              Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
              gvs[ssa_result_equiv_def] >>
              Cases_on `eval_operand (ssa_operand vm h'') s_ssa` >>
              gvs[ssa_result_equiv_def, AllCaseEqs()] >>
              `s_orig.vs_returndata = s_ssa.vs_returndata` by fs[ssa_state_equiv_def] >>
              pop_assum (fn eq => simp_tac std_ss [eq]) >>
              simp[LET_DEF] >>
              CASE_TAC >| [
                (gvs[ssa_result_equiv_def] >>
                 irule revert_state_ssa_equiv >> simp[]),
                (gvs[ssa_result_equiv_def] >>
                 irule write_memory_with_expansion_ssa_equiv >> simp[])
              ]),
             gvs[ssa_result_equiv_def]
           ])
        ])
     ])
  ]
QED

(* Helper: ASSIGN gives ssa_result_equiv with SAME vm.
 * ASSIGN has one operand and one output variable. *)
Theorem assign_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "assign requires 1 operand and single output"
       | op1::ops =>
           case inst.inst_outputs of
             [] => Error "assign requires 1 operand and single output"
           | [out] =>
               (case ops of
                  [] =>
                    (case eval_operand op1 s_orig of
                       SOME v => OK (update_var out v s_orig)
                     | NONE => Error "undefined operand")
                | _ => Error "assign requires 1 operand and single output")
           | _ => Error "assign requires 1 operand and single output")
      (case inst_ssa.inst_operands of
         [] => Error "assign requires 1 operand and single output"
       | op1::ops =>
           case inst_ssa.inst_outputs of
             [] => Error "assign requires 1 operand and single output"
           | [out] =>
               (case ops of
                  [] =>
                    (case eval_operand op1 s_ssa of
                       SOME v => OK (update_var out v s_ssa)
                     | NONE => Error "undefined operand")
                | _ => Error "assign requires 1 operand and single output")
           | _ => Error "assign requires 1 operand and single output")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  (* Now have [h] operand and [h'] output *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> gvs[ssa_result_equiv_def] >>
  irule ssa_state_equiv_update_same_vm >>
  Cases_on `FLOOKUP vm h'` >> gvs[]
QED

(* Helper: JMP gives ssa_result_equiv with SAME vm.
 * Labels are not renamed in SSA, so jump targets match. *)
Theorem jmp_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [Label target] => OK (jump_to target s_orig)
       | _ => Error "jmp requires label operand")
      (case inst_ssa.inst_operands of
         [Label target] => OK (jump_to target s_ssa)
       | _ => Error "jmp requires label operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  (* Case split on operand count: [] vs [h] vs h::h'::t' *)
  Cases_on `inst.inst_operands` >> simp[ssa_result_equiv_def] >>
  Cases_on `t` >> simp[ssa_result_equiv_def] >>
  (* Case split on operand type: Lit, Var, Label *)
  Cases_on `h` >> simp[ssa_operand_def, ssa_result_equiv_def] >>
  (* Lit cases solved. Var cases need CASE_TAC for FLOOKUP expansion *)
  rpt (CASE_TAC >> simp[ssa_result_equiv_def]) >>
  (* Label singleton case needs jump_to_ssa_equiv *)
  irule jump_to_ssa_equiv >> simp[]
QED

(* Helper: JNZ gives ssa_result_equiv with SAME vm.
 * The condition operand is transformed, but labels are unchanged. *)
Theorem jnz_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [cond_op; Label if_nonzero; Label if_zero] =>
           (case eval_operand cond_op s_orig of
              SOME cond =>
                if cond <> 0w then OK (jump_to if_nonzero s_orig)
                else OK (jump_to if_zero s_orig)
            | NONE => Error "undefined condition")
       | _ => Error "jnz requires cond and 2 labels")
      (case inst_ssa.inst_operands of
         [cond_op; Label if_nonzero; Label if_zero] =>
           (case eval_operand cond_op s_ssa of
              SOME cond =>
                if cond <> 0w then OK (jump_to if_nonzero s_ssa)
                else OK (jump_to if_zero s_ssa)
            | NONE => Error "undefined condition")
       | _ => Error "jnz requires cond and 2 labels")
Proof
  rpt strip_tac >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  (* Initial setup *)
  simp[ssa_operand_def, ssa_result_equiv_def] >>
  (* Split on inst.inst_operands: [] case closes, h::t case simplifies *)
  CASE_TAC >> simp[ssa_result_equiv_def] >> simp[] >>
  (* CASE_TAC picks eval_operand h s_orig and splits NONE/SOME *)
  CASE_TAC >> simp[ssa_operand_def, ssa_result_equiv_def] >>
  (* For both NONE and SOME cases, use eval_operand_ssa_equiv *)
  drule_all eval_operand_ssa_equiv >> strip_tac >> gvs[] >>
  (* Continue case splitting on t, then use jump_to_ssa_equiv for OK cases *)
  rpt (CASE_TAC >> simp[ssa_operand_def, ssa_result_equiv_def]) >>
  irule jump_to_ssa_equiv >> simp[]
QED
