(*
 * SSA Construction Block-Level: Result Equivalence for Context and Hash Ops
 *
 * TOP-LEVEL:
 *   - assert_result_ssa_equiv
 *   - assert_unreachable_result_ssa_equiv
 *   - blockhash_result_ssa_equiv
 *   - balance_result_ssa_equiv
 *   - calldataload_result_ssa_equiv
 *   - sha3_result_ssa_equiv
 *   - sha3_64_result_ssa_equiv
 *)

Theory mkSsaBlockResultContext
Ancestors
  mkSsaBlockResultMem mkSsaBlockResultCore mkSsaBlockCompat
  mkSsaStateEquiv venomSem

(* Helper: ASSERT gives ssa_result_equiv with SAME vm. *)
Theorem assert_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_orig of
              SOME cond =>
                if cond = 0w then Revert (revert_state s_orig)
                else OK s_orig
            | NONE => Error "undefined operand")
       | _ => Error "assert requires 1 operand")
      (case inst_ssa.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_ssa of
              SOME cond =>
                if cond = 0w then Revert (revert_state s_ssa)
                else OK s_ssa
            | NONE => Error "undefined operand")
       | _ => Error "assert requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `x = 0w` >> gvs[ssa_result_equiv_def] >>
  irule revert_state_ssa_equiv >> simp[]
QED

(* Helper: ASSERT_UNREACHABLE gives ssa_result_equiv with SAME vm. *)
Theorem assert_unreachable_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_orig of
              SOME cond =>
                if cond <> 0w then Halt (halt_state s_orig)
                else OK s_orig
            | NONE => Error "undefined operand")
       | _ => Error "assert_unreachable requires 1 operand")
      (case inst_ssa.inst_operands of
         [cond_op] =>
           (case eval_operand cond_op s_ssa of
              SOME cond =>
                if cond <> 0w then Halt (halt_state s_ssa)
                else OK s_ssa
            | NONE => Error "undefined operand")
       | _ => Error "assert_unreachable requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `inst.inst_operands` >> fs[ssa_result_equiv_def] >>
  Cases_on `t` >> fs[ssa_result_equiv_def] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  Cases_on `eval_operand (ssa_operand vm h) s_ssa` >> fs[ssa_result_equiv_def] >> gvs[] >>
  Cases_on `x <> 0w` >> gvs[ssa_result_equiv_def] >>
  irule halt_state_ssa_equiv >> simp[]
QED

(* Helper: BLOCKHASH gives ssa_result_equiv with SAME vm. *)
Theorem blockhash_result_ssa_equiv:
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
         [] => Error "blockhash requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME blocknum =>
              case inst.inst_outputs of
                [] => Error "blockhash requires single output"
              | [out] => OK (update_var out (s_orig.vs_block_ctx.bc_blockhash (w2n blocknum)) s_orig)
              | out::v6::v7 => Error "blockhash requires single output")
       | op1::v9::v10 => Error "blockhash requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "blockhash requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME blocknum =>
              case inst_ssa.inst_outputs of
                [] => Error "blockhash requires single output"
              | [out] => OK (update_var out (s_ssa.vs_block_ctx.bc_blockhash (w2n blocknum)) s_ssa)
              | out::v6::v7 => Error "blockhash requires single output")
       | op1::v9::v10 => Error "blockhash requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
        (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
           (irule eval_operand_ssa_equiv >> simp[]) >>
        Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
        fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
        `s_orig.vs_block_ctx = s_ssa.vs_block_ctx` by fs[ssa_state_equiv_def] >>
        pop_assum (fn eq => simp_tac std_ss [eq]) >>
        irule ssa_state_equiv_update_same_vm >>
        Cases_on `FLOOKUP vm h'` >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: BALANCE gives ssa_result_equiv with SAME vm. *)
Theorem balance_result_ssa_equiv:
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
         [] => Error "balance requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME addr =>
              case inst.inst_outputs of
                [] => Error "balance requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (n2w (lookup_account (w2w addr) s_orig.vs_accounts).balance)
                       s_orig)
              | out::v6::v7 => Error "balance requires single output")
       | op1::v9::v10 => Error "balance requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "balance requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME addr =>
              case inst_ssa.inst_outputs of
                [] => Error "balance requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (n2w (lookup_account (w2w addr) s_ssa.vs_accounts).balance)
                       s_ssa)
              | out::v6::v7 => Error "balance requires single output")
       | op1::v9::v10 => Error "balance requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
        (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
           (irule eval_operand_ssa_equiv >> simp[]) >>
        Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
        fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
        `s_orig.vs_accounts = s_ssa.vs_accounts` by fs[ssa_state_equiv_def] >>
        pop_assum (fn eq => simp_tac std_ss [eq]) >>
        irule ssa_state_equiv_update_same_vm >>
        Cases_on `FLOOKUP vm h'` >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: CALLDATALOAD gives ssa_result_equiv with SAME vm. *)
Theorem calldataload_result_ssa_equiv:
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
         [] => Error "calldataload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME offset =>
              case inst.inst_outputs of
                [] => Error "calldataload requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (word_of_bytes T (0w:bytes32)
                          (TAKE 32
                             (DROP (w2n offset) s_orig.vs_call_ctx.cc_calldata ++
                              REPLICATE 32 0w))) s_orig)
              | out::v6::v7 => Error "calldataload requires single output")
       | op1::v9::v10 => Error "calldataload requires 1 operand")
      (case inst_ssa.inst_operands of
         [] => Error "calldataload requires 1 operand"
       | [op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME offset =>
              case inst_ssa.inst_outputs of
                [] => Error "calldataload requires single output"
              | [out] =>
                  OK
                    (update_var out
                       (word_of_bytes T (0w:bytes32)
                          (TAKE 32
                             (DROP (w2n offset) s_ssa.vs_call_ctx.cc_calldata ++
                              REPLICATE 32 0w))) s_ssa)
              | out::v6::v7 => Error "calldataload requires single output")
       | op1::v9::v10 => Error "calldataload requires 1 operand")
Proof
  rw[] >>
  qpat_x_assum `inst_ssa.inst_operands = _` (fn th => ONCE_REWRITE_TAC [th]) >>

  Cases_on `inst.inst_operands` >| [
    gvs[ssa_result_equiv_def],
    (Cases_on `t` >| [
        (`eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
           (irule eval_operand_ssa_equiv >> simp[]) >>
        Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
        fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `inst.inst_outputs` >> fs[ssa_result_equiv_def] >> gvs[] >>
        Cases_on `t` >> fs[ssa_result_equiv_def] >> gvs[] >>
        `s_orig.vs_call_ctx = s_ssa.vs_call_ctx` by fs[ssa_state_equiv_def] >>
        pop_assum (fn eq => simp_tac std_ss [eq]) >>
        irule ssa_state_equiv_update_same_vm >>
        Cases_on `FLOOKUP vm h'` >> gvs[]),
       gvs[ssa_result_equiv_def]
     ])
  ]
QED

(* Helper: SHA3 gives ssa_result_equiv with SAME vm. *)
Theorem sha3_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sha3 requires 2 operands"
       | [op_size] => Error "sha3 requires 2 operands"
       | [op_size; op_offset] =>
         (case eval_operand op_size s_orig of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_orig of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case inst.inst_outputs of
                    [] => Error "sha3 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (TAKE (w2n size_val)
                                    (DROP (w2n offset) s_orig.vs_memory ++
                                     REPLICATE (w2n size_val) 0w)))) s_orig)
                  | out::v6::v7 => Error "sha3 requires single output")
       | op_size::op_offset::v10::v11 => Error "sha3 requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "sha3 requires 2 operands"
       | [op_size] => Error "sha3 requires 2 operands"
       | [op_size; op_offset] =>
         (case eval_operand op_size s_ssa of
            NONE => Error "undefined operand"
          | SOME size_val =>
              case eval_operand op_offset s_ssa of
                NONE => Error "undefined operand"
              | SOME offset =>
                  case inst_ssa.inst_outputs of
                    [] => Error "sha3 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (TAKE (w2n size_val)
                                    (DROP (w2n offset) s_ssa.vs_memory ++
                                     REPLICATE (w2n size_val) 0w)))) s_ssa)
                  | out::v6::v7 => Error "sha3 requires single output")
       | op_size::op_offset::v10::v11 => Error "sha3 requires 2 operands")
Proof
  rpt strip_tac >>
  `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
    fs[inst_ssa_compatible_def] >>
  Cases_on `inst.inst_operands` >| [
    gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
       (Cases_on `t'` >| [
          (simp[] >>
           `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `inst.inst_outputs` >| [
             gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
             (Cases_on `t` >| [
                (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >>
                 gvs[ssa_result_equiv_def] >>
                 `s_orig.vs_memory = s_ssa.vs_memory` by fs[ssa_state_equiv_def] >>
                 pop_assum (fn eq => simp_tac std_ss [eq]) >>
                 irule ssa_state_equiv_update_same_vm >>
                 gvs[]),
                gvs[ssa_result_equiv_def]
              ])
           ]),
          gvs[inst_ssa_compatible_def, ssa_result_equiv_def]
        ])
     ])
  ]
QED

(* Helper: SHA3_64 gives ssa_result_equiv with SAME vm. *)
Theorem sha3_64_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 ==>
    ssa_result_equiv vm
      (case inst.inst_operands of
         [] => Error "sha3_64 requires 2 operands"
       | [op2] => Error "sha3_64 requires 2 operands"
       | [op2; op1] =>
         (case eval_operand op1 s_orig of
            NONE => Error "undefined operand"
          | SOME v1 =>
              case eval_operand op2 s_orig of
                NONE => Error "undefined operand"
              | SOME v2 =>
                  case inst.inst_outputs of
                    [] => Error "sha3_64 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (word_to_bytes v1 T ++ word_to_bytes v2 T)))
                           s_orig)
                  | out::v6::v7 => Error "sha3_64 requires single output")
       | op2::op1::v10::v11 => Error "sha3_64 requires 2 operands")
      (case inst_ssa.inst_operands of
         [] => Error "sha3_64 requires 2 operands"
       | [op2] => Error "sha3_64 requires 2 operands"
       | [op2; op1] =>
         (case eval_operand op1 s_ssa of
            NONE => Error "undefined operand"
          | SOME v1 =>
              case eval_operand op2 s_ssa of
                NONE => Error "undefined operand"
              | SOME v2 =>
                  case inst_ssa.inst_outputs of
                    [] => Error "sha3_64 requires single output"
                  | [out] =>
                      OK
                        (update_var out
                           (word_of_bytes T 0w
                              (Keccak_256_w64
                                 (word_to_bytes v1 T ++ word_to_bytes v2 T)))
                           s_ssa)
                  | out::v6::v7 => Error "sha3_64 requires single output")
       | op2::op1::v10::v11 => Error "sha3_64 requires 2 operands")
Proof
  rpt strip_tac >>
  `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
    fs[inst_ssa_compatible_def] >>
  Cases_on `inst.inst_operands` >| [
    gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
    (Cases_on `t` >| [
       gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
       (Cases_on `t'` >| [
          (simp[] >>
           `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
             (irule eval_operand_ssa_equiv >> simp[]) >>
           Cases_on `eval_operand (ssa_operand vm h') s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `eval_operand (ssa_operand vm h) s_ssa` >>
           gvs[ssa_result_equiv_def] >>
           Cases_on `inst.inst_outputs` >| [
             gvs[inst_ssa_compatible_def, ssa_result_equiv_def],
             (Cases_on `t` >| [
                (drule_all inst_ssa_compatible_outputs_equiv >> strip_tac >>
                 gvs[ssa_result_equiv_def] >>
                 `s_orig.vs_memory = s_ssa.vs_memory` by fs[ssa_state_equiv_def] >>
                 pop_assum (fn eq => simp_tac std_ss [eq]) >>
                 irule ssa_state_equiv_update_same_vm >>
                 gvs[]),
                gvs[ssa_result_equiv_def]
              ])
           ]),
          gvs[inst_ssa_compatible_def, ssa_result_equiv_def]
        ])
     ])
  ]
QED
