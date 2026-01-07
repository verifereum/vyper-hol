(* 
 * Simplify-CFG Equivalence Lemmas
 *
 * Basic equivalence facts and state-operation preservation for CFG transforms.
 *)

Theory scfgEquiv
Ancestors
  scfgDefs scfgStateOps stateEquiv venomSem venomSemProps venomState venomInst
  finite_map pair list rich_list

(* ===== Equivalence Basics ===== *)

Theorem state_equiv_cfg_refl:
  !s. state_equiv_cfg s s
Proof
  rw[state_equiv_cfg_def, var_equiv_def]
QED

Theorem state_equiv_cfg_sym:
  !s1 s2. state_equiv_cfg s1 s2 ==> state_equiv_cfg s2 s1
Proof
  rw[state_equiv_cfg_def, var_equiv_def]
QED

Theorem state_equiv_cfg_trans:
  !s1 s2 s3.
    state_equiv_cfg s1 s2 /\ state_equiv_cfg s2 s3 ==> state_equiv_cfg s1 s3
Proof
  rw[state_equiv_cfg_def, var_equiv_def] >> metis_tac[]
QED

Theorem state_equiv_cfg_ctrl_eq:
  !s1 s2.
    state_equiv_cfg s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    s1 = s2
Proof
  Cases_on `s1` >> Cases_on `s2` >>
  rw[state_equiv_cfg_def, var_equiv_def, lookup_var_def] >>
  simp[finite_mapTheory.fmap_eq_flookup, venomStateTheory.venom_state_11]
QED

Theorem state_equiv_cfg_inst_idx:
  !s1 s2 idx.
    state_equiv_cfg s1 s2 ==> state_equiv_cfg (s1 with vs_inst_idx := idx) s2
Proof
  rw[state_equiv_cfg_def, var_equiv_def, lookup_var_def]
QED

Theorem result_equiv_cfg_refl:
  !r. result_equiv_cfg r r
Proof
  Cases >> rw[result_equiv_cfg_def, state_equiv_cfg_refl]
QED

Theorem result_equiv_cfg_sym:
  !r1 r2. result_equiv_cfg r1 r2 ==> result_equiv_cfg r2 r1
Proof
  Cases >> Cases >> rw[result_equiv_cfg_def, state_equiv_cfg_sym]
QED

Theorem result_equiv_cfg_trans:
  !r1 r2 r3. result_equiv_cfg r1 r2 /\ result_equiv_cfg r2 r3 ==> result_equiv_cfg r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[result_equiv_cfg_def] >> metis_tac[state_equiv_cfg_trans]
QED

Theorem result_equiv_cfg_error:
  !e1 e2. result_equiv_cfg (Error e1) (Error e2)
Proof
  simp[result_equiv_cfg_def]
QED

Theorem run_function_equiv_cfg_refl:
  !fn s. run_function_equiv_cfg fn fn s
Proof
  rw[run_function_equiv_cfg_def]
  >- (qexists_tac `fuel` >> simp[result_equiv_cfg_refl])
  >- (qexists_tac `fuel'` >> simp[result_equiv_cfg_refl])
QED

Theorem run_function_equiv_cfg_trans:
  !fn1 fn2 fn3 s.
    run_function_equiv_cfg fn1 fn2 s /\
    run_function_equiv_cfg fn2 fn3 s ==> run_function_equiv_cfg fn1 fn3 s
Proof
  rw[run_function_equiv_cfg_def] >> metis_tac[result_equiv_cfg_trans]
QED

(* ===== Operand Evaluation under state_equiv_cfg ===== *)

Theorem eval_operand_state_equiv_cfg:
  !op s1 s2.
    state_equiv_cfg s1 s2 ==> eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_cfg_def, var_equiv_def]
QED

(* ===== Result Equivalence for Operand Execution ===== *)

Theorem exec_binop_result_equiv_cfg:
  !f inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_binop f inst s1) (exec_binop f inst s2)
Proof
  rw[exec_binop_def] >>
  drule eval_operand_state_equiv_cfg >> strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem exec_unop_result_equiv_cfg:
  !f inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_unop f inst s1) (exec_unop f inst s2)
Proof
  rw[exec_unop_def] >>
  drule eval_operand_state_equiv_cfg >> strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem exec_modop_result_equiv_cfg:
  !f inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_modop f inst s1) (exec_modop f inst s2)
Proof
  rw[exec_modop_def] >>
  drule eval_operand_state_equiv_cfg >> strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem returndatacopy_eval_state_equiv_cfg:
  !op_size op_offset op_destOffset s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg
      (case eval_operand op_size s1 of
         NONE => Error "undefined operand"
       | SOME size_val =>
         case eval_operand op_offset s1 of
           NONE => Error "undefined operand"
         | SOME offset =>
           case eval_operand op_destOffset s1 of
             NONE => Error "undefined operand"
           | SOME destOffset =>
             if w2n offset + w2n size_val > LENGTH s1.vs_returndata then
               Revert (revert_state s1)
             else
               OK
                 (write_memory_with_expansion (w2n destOffset)
                    (TAKE (w2n size_val)
                       (DROP (w2n offset) s1.vs_returndata)) s1))
      (case eval_operand op_size s2 of
         NONE => Error "undefined operand"
       | SOME size_val =>
         case eval_operand op_offset s2 of
           NONE => Error "undefined operand"
         | SOME offset =>
           case eval_operand op_destOffset s2 of
             NONE => Error "undefined operand"
           | SOME destOffset =>
             if w2n offset + w2n size_val > LENGTH s2.vs_returndata then
               Revert (revert_state s2)
             else
               OK
                 (write_memory_with_expansion (w2n destOffset)
                    (TAKE (w2n size_val)
                       (DROP (w2n offset) s2.vs_returndata)) s2))
Proof
  rpt strip_tac >>
  Cases_on `eval_operand op_size s1`
  >- (
    `eval_operand op_size s2 = NONE` by
      metis_tac[eval_operand_state_equiv_cfg] >>
    simp[result_equiv_cfg_def]
  )
  >- (
    rename1 `eval_operand op_size s1 = SOME size_val` >>
    `eval_operand op_size s2 = SOME size_val` by
      metis_tac[eval_operand_state_equiv_cfg] >>
    simp[] >>
    Cases_on `eval_operand op_offset s1`
    >- (
      `eval_operand op_offset s2 = NONE` by
        metis_tac[eval_operand_state_equiv_cfg] >>
      simp[result_equiv_cfg_def]
    )
    >- (
      rename1 `eval_operand op_offset s1 = SOME offset` >>
      `eval_operand op_offset s2 = SOME offset` by
        metis_tac[eval_operand_state_equiv_cfg] >>
      simp[] >>
      Cases_on `eval_operand op_destOffset s1`
      >- (
        `eval_operand op_destOffset s2 = NONE` by
          metis_tac[eval_operand_state_equiv_cfg] >>
        simp[result_equiv_cfg_def]
      )
      >- (
        rename1 `eval_operand op_destOffset s1 = SOME destOffset` >>
        `eval_operand op_destOffset s2 = SOME destOffset` by
          metis_tac[eval_operand_state_equiv_cfg] >>
        simp[] >>
        irule returndatacopy_state_equiv_cfg >> simp[]
      )
    )
  )
QED

Theorem returndatacopy_state_equiv_cfg_comm:
  !destOffset size_val offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg
      (if w2n size_val + w2n offset > LENGTH s1.vs_returndata then
         Revert (revert_state s1)
       else
         OK
           (write_memory_with_expansion (w2n destOffset)
              (TAKE (w2n size_val) (DROP (w2n offset) s1.vs_returndata)) s1))
      (if w2n size_val + w2n offset > LENGTH s2.vs_returndata then
         Revert (revert_state s2)
       else
         OK
           (write_memory_with_expansion (w2n destOffset)
              (TAKE (w2n size_val) (DROP (w2n offset) s2.vs_returndata)) s2))
Proof
  rpt strip_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV
    [arithmeticTheory.ADD_COMM]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV
    [arithmeticTheory.ADD_COMM])) >>
  irule returndatacopy_state_equiv_cfg >> simp[]
QED

Theorem returndatacopy_inst_operands_state_equiv_cfg:
  !inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg
      (case inst.inst_operands of
         [op_size; op_offset; op_destOffset] =>
           (case eval_operand op_size s1 of
              NONE => Error "undefined operand"
            | SOME size_val =>
              case eval_operand op_offset s1 of
                NONE => Error "undefined operand"
              | SOME offset =>
                case eval_operand op_destOffset s1 of
                  NONE => Error "undefined operand"
                | SOME destOffset =>
                  if w2n offset + w2n size_val > LENGTH s1.vs_returndata then
                    Revert (revert_state s1)
                  else
                    OK
                      (write_memory_with_expansion (w2n destOffset)
                         (TAKE (w2n size_val)
                            (DROP (w2n offset) s1.vs_returndata)) s1))
       | _ => Error "returndatacopy requires 3 operands")
      (case inst.inst_operands of
         [op_size; op_offset; op_destOffset] =>
           (case eval_operand op_size s2 of
              NONE => Error "undefined operand"
            | SOME size_val =>
              case eval_operand op_offset s2 of
                NONE => Error "undefined operand"
              | SOME offset =>
                case eval_operand op_destOffset s2 of
                  NONE => Error "undefined operand"
                | SOME destOffset =>
                  if w2n offset + w2n size_val > LENGTH s2.vs_returndata then
                    Revert (revert_state s2)
                  else
                    OK
                      (write_memory_with_expansion (w2n destOffset)
                         (TAKE (w2n size_val)
                            (DROP (w2n offset) s2.vs_returndata)) s2))
       | _ => Error "returndatacopy requires 3 operands")
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_error] >>
  Cases_on `t` >> gvs[result_equiv_cfg_error] >>
  Cases_on `t'` >> gvs[result_equiv_cfg_error] >>
  Cases_on `t` >>
  gvs[result_equiv_cfg_error, returndatacopy_eval_state_equiv_cfg]
QED

Theorem sha3_val_state_equiv_cfg:
  !size_val offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    word_of_bytes T 0w
      (Keccak_256_w64
         (TAKE (w2n size_val)
            (DROP (w2n offset) s1.vs_memory ⧺ REPLICATE (w2n size_val) 0w))) =
    word_of_bytes T 0w
      (Keccak_256_w64
         (TAKE (w2n size_val)
            (DROP (w2n offset) s2.vs_memory ⧺ REPLICATE (w2n size_val) 0w)))
Proof
  rw[state_equiv_cfg_def]
QED

Theorem sha3_update_var_state_equiv_cfg:
  !out size_val offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out
         (word_of_bytes T 0w
            (Keccak_256_w64
               (TAKE (w2n size_val)
                  (DROP (w2n offset) s1.vs_memory ⧺
                   REPLICATE (w2n size_val) 0w)))) s1)
      (update_var out
         (word_of_bytes T 0w
            (Keccak_256_w64
               (TAKE (w2n size_val)
                  (DROP (w2n offset) s2.vs_memory ⧺
                   REPLICATE (w2n size_val) 0w)))) s2)
Proof
  rpt strip_tac >>
  irule update_var_state_equiv_cfg_eq >>
  simp[sha3_val_state_equiv_cfg]
QED

Theorem sha3_inst_operands_state_equiv_cfg:
  !inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg
      (case inst.inst_operands of
         [op_size; op_offset] =>
           (case eval_operand op_size s1 of
              NONE => Error "undefined operand"
            | SOME size_val =>
              case eval_operand op_offset s1 of
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
                                (DROP (w2n offset) s1.vs_memory ⧺
                                 REPLICATE (w2n size_val) 0w)))) s1)
                | out::v6::v7 => Error "sha3 requires single output")
       | _ => Error "sha3 requires 2 operands")
      (case inst.inst_operands of
         [op_size; op_offset] =>
           (case eval_operand op_size s2 of
              NONE => Error "undefined operand"
            | SOME size_val =>
              case eval_operand op_offset s2 of
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
                                (DROP (w2n offset) s2.vs_memory ⧺
                                 REPLICATE (w2n size_val) 0w)))) s2)
                | out::v6::v7 => Error "sha3 requires single output")
       | _ => Error "sha3 requires 2 operands")
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands`
  >- simp[result_equiv_cfg_error]
  >- (Cases_on `t`
      >- simp[result_equiv_cfg_error]
      >- (Cases_on `t'`
          >- (
            simp[result_equiv_cfg_error] >>
            simp[eval_operand_state_equiv_cfg] >>
            simp[GSYM eval_operand_state_equiv_cfg] >>
            Cases_on `eval_operand h s1`
            >- (
              fs[eval_operand_state_equiv_cfg, result_equiv_cfg_error] >>
              simp[GSYM eval_operand_state_equiv_cfg] >>
              qspec_then `h` mp_tac eval_operand_state_equiv_cfg >>
              simp[] >> strip_tac >>
              first_x_assum (qspecl_then [`s1`,`s2`] mp_tac) >>
              simp[] >> strip_tac >>
              simp[result_equiv_cfg_error])
            >- (
              simp[] >>
              qspec_then `h` mp_tac eval_operand_state_equiv_cfg >>
              simp[] >> strip_tac >>
              first_x_assum (qspecl_then [`s1`,`s2`] mp_tac) >>
              simp[] >> strip_tac >>
              simp[] >>
              qpat_x_assum `SOME x = eval_operand h s2` (assume_tac o SYM) >>
              simp[] >>
              Cases_on `eval_operand h' s1`
              >- (
                qspec_then `h'` mp_tac eval_operand_state_equiv_cfg >>
                simp[] >> strip_tac >>
                first_x_assum (qspecl_then [`s1`,`s2`] mp_tac) >>
                simp[] >> strip_tac >>
                simp[result_equiv_cfg_error])
              >- (
                simp[] >>
                qspec_then `h'` mp_tac eval_operand_state_equiv_cfg >>
                simp[] >> strip_tac >>
                first_x_assum (qspecl_then [`s1`,`s2`] mp_tac) >>
                strip_tac >>
                first_x_assum drule_all >>
                strip_tac >>
                qpat_x_assum `eval_operand h' s1 = eval_operand h' s2`
                  (fn th => simp[SYM th]) >>
                Cases_on `inst.inst_outputs` >>
                simp[result_equiv_cfg_error, sha3_update_var_state_equiv_cfg] >>
                Cases_on `t` >>
                simp[result_equiv_cfg_error, sha3_update_var_state_equiv_cfg] >>
                simp[scfgDefsTheory.result_equiv_cfg_def,
                     sha3_update_var_state_equiv_cfg])))
          >- simp[result_equiv_cfg_error]))
QED

(* ===== Instruction Stepping Preserves state_equiv_cfg ===== *)

Theorem step_inst_state_equiv_cfg:
  !inst s1 s2.
    state_equiv_cfg s1 s2 /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb)
  ==>
    result_equiv_cfg (step_inst inst s1) (step_inst inst s2)
Proof
  rpt strip_tac >>
  simp[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  TRY (irule exec_binop_result_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (irule exec_unop_result_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (irule exec_modop_result_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       irule calldataload_update_var_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       irule calldatacopy_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (irule returndatacopy_inst_operands_state_equiv_cfg >>
       simp[] >> NO_TAC) >>
  TRY (irule sha3_inst_operands_state_equiv_cfg >>
       simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       irule balance_update_var_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       irule blockhash_update_var_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def, calldata_state_equiv_cfg,
                           calldataload_val_state_equiv_cfg,
                           eval_operand_state_equiv_cfg] >>
       TRY (drule_all mload_state_equiv_cfg >> strip_tac >> gvs[]) >>
       TRY (drule_all sload_state_equiv_cfg >> strip_tac >> gvs[]) >>
       TRY (drule_all tload_state_equiv_cfg >> strip_tac >> gvs[]) >>
       irule update_var_state_equiv_cfg_eq >>
       simp[calldata_state_equiv_cfg] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       TRY (irule mstore_state_equiv_cfg >> simp[]) >>
       TRY (irule sstore_state_equiv_cfg >> simp[]) >>
       TRY (irule tstore_state_equiv_cfg >> simp[]) >> NO_TAC) >>
  TRY (simp[eval_operand_state_equiv_cfg] >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def, calldata_state_equiv_cfg] >>
       irule write_memory_with_expansion_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (rpt CASE_TAC >>
       gvs[result_equiv_cfg_error, state_equiv_cfg_def,
           eval_operand_state_equiv_cfg] >>
       irule update_var_state_equiv_cfg_eq >> simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       irule jump_to_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (simp[result_equiv_cfg_def] >> irule halt_state_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (simp[result_equiv_cfg_def] >> irule revert_state_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
       TRY (irule halt_state_state_equiv_cfg >> simp[]) >>
       TRY (irule revert_state_state_equiv_cfg >> simp[]) >>
       simp[state_equiv_cfg_refl] >> NO_TAC) >>
  TRY (drule eval_operand_state_equiv_cfg >> strip_tac >>
       rpt CASE_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def,
                           eval_operand_state_equiv_cfg] >>
       irule update_var_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (simp[result_equiv_cfg_def, state_equiv_cfg_def] >>
       irule update_var_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (rpt CASE_TAC >> gvs[result_equiv_cfg_def, state_equiv_cfg_def] >>
       irule update_var_state_equiv_cfg >> simp[] >> NO_TAC) >>
  TRY (Cases_on `inst.inst_outputs` >> simp[result_equiv_cfg_def] >>
       Cases_on `t` >> simp[result_equiv_cfg_def, msize_update_var_state_equiv_cfg] >>
       NO_TAC) >>
  TRY (Cases_on `inst.inst_outputs` >> simp[result_equiv_cfg_def] >>
       Cases_on `t` >> simp[result_equiv_cfg_def,
                             update_var_call_ctx_state_equiv_cfg,
                             update_var_tx_ctx_state_equiv_cfg,
                             update_var_block_ctx_state_equiv_cfg,
                             selfbalance_update_var_state_equiv_cfg,
                             returndatasize_update_var_state_equiv_cfg,
                             update_var_state_equiv_cfg] >>
       NO_TAC) >>
  simp[result_equiv_cfg_def]
QED

(* ===== Block-Level Equivalence Helpers ===== *)

Theorem block_has_no_phi_inst:
  !bb inst.
    block_has_no_phi bb /\
    MEM inst bb.bb_instructions ==> inst.inst_opcode <> PHI
Proof
  rw[block_has_no_phi_def, block_has_phi_def] >> metis_tac[]
QED

Theorem step_in_block_inst_idx_succ:
  !bb s v.
    step_in_block bb s = (OK v, F) ==> v.vs_inst_idx = s.vs_inst_idx + 1
Proof
  rpt strip_tac >>
  qpat_x_assum `step_in_block bb s = (OK v, F)` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[] >>
  strip_tac >>
  drule_all step_inst_preserves_inst_idx >>
  gvs[next_inst_def]
QED

Theorem step_in_block_state_equiv_cfg:
  !bb s1 s2 res1 is_term.
    step_in_block bb s1 = (res1, is_term) /\
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx
  ==>
    ?res2. step_in_block bb s2 = (res2, is_term) /\
           result_equiv_cfg res1 res2
Proof
  rpt strip_tac >>
  qpat_x_assum `s1.vs_inst_idx = s2.vs_inst_idx` (assume_tac o SYM) >>
  qpat_x_assum `step_in_block bb s1 = (res1, is_term)` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx`
  >- (
    strip_tac >>
    qexists_tac `Error "block not terminated"` >>
    qpat_x_assum `_ = (res1,is_term)` mp_tac >>
    simp[] >> strip_tac >>
    simp[result_equiv_cfg_def]
  )
  >- (
    rename1 `get_instruction bb _ = SOME inst` >>
    strip_tac >>
    simp[] >>
    sg `result_equiv_cfg (step_inst inst s1) (step_inst inst s2)`
    >- (irule step_inst_state_equiv_cfg >> simp[]) >>
    Cases_on `step_inst inst s1`
    >- (
      rename1 `step_inst inst s1 = OK s1'` >>
      Cases_on `step_inst inst s2`
      >| [
        (rename1 `step_inst inst s2 = OK s2'` >>
         simp[] >>
         Cases_on `is_terminator inst.inst_opcode`
         >- (
           simp[] >>
           qpat_x_assum `_ = (res1,is_term)` mp_tac >>
           simp[pairTheory.PAIR_EQ] >> strip_tac >>
           FIRST
             [qpat_x_assum `OK _ = res1`
                (fn th => simp[SYM th, result_equiv_cfg_def]),
              qpat_x_assum `res1 = OK _`
                (fn th => simp[th, result_equiv_cfg_def])]
         )
         >- (
           simp[] >>
           qpat_x_assum `_ = (res1,is_term)` mp_tac >>
           simp[pairTheory.PAIR_EQ] >> strip_tac >>
           FIRST
             [qpat_x_assum `OK _ = res1`
                (fn th =>
                   simp[SYM th, result_equiv_cfg_def,
                        next_inst_state_equiv_cfg]),
              qpat_x_assum `res1 = OK _`
                (fn th =>
                   simp[th, result_equiv_cfg_def,
                        next_inst_state_equiv_cfg])] >>
           irule next_inst_state_equiv_cfg >> simp[] >>
           gvs[result_equiv_cfg_def]
         )),
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def]
      ]
    )
    >- (
      rename1 `step_inst inst s1 = Halt s1'` >>
      Cases_on `step_inst inst s2`
      >| [
        gvs[result_equiv_cfg_def],
        (rename1 `step_inst inst s2 = Halt s2'` >>
         simp[] >>
         qpat_x_assum `_ = (res1,is_term)` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         FIRST
           [qpat_x_assum `Halt _ = res1`
              (fn th => simp[SYM th, result_equiv_cfg_def]),
            qpat_x_assum `res1 = Halt _`
              (fn th => simp[th, result_equiv_cfg_def])]),
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def]
      ]
    )
    >- (
      rename1 `step_inst inst s1 = Revert s1'` >>
      Cases_on `step_inst inst s2`
      >| [
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        (rename1 `step_inst inst s2 = Revert s2'` >>
         simp[] >>
         qpat_x_assum `_ = (res1,is_term)` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         FIRST
           [qpat_x_assum `Revert _ = res1`
              (fn th => simp[SYM th, result_equiv_cfg_def]),
            qpat_x_assum `res1 = Revert _`
              (fn th => simp[th, result_equiv_cfg_def])]),
        gvs[result_equiv_cfg_def]
      ]
    )
    >- (
      rename1 `step_inst inst s1 = Error e1` >>
      Cases_on `step_inst inst s2`
      >| [
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        (rename1 `step_inst inst s2 = Error e2` >>
         simp[] >>
         qpat_x_assum `_ = (res1,is_term)` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         FIRST
           [qpat_x_assum `Error _ = res1`
              (fn th => simp[SYM th, result_equiv_cfg_def]),
            qpat_x_assum `res1 = Error _`
              (fn th => simp[th, result_equiv_cfg_def])])
      ]
    )
  )
QED

Theorem step_in_block_no_phi_equiv_cfg:
  !bb s1 s2 res1 is_term.
    step_in_block bb s1 = (res1, is_term) /\
    block_has_no_phi bb /\
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx
  ==>
    ?res2. step_in_block bb s2 = (res2, is_term) /\
           result_equiv_cfg res1 res2
Proof
  rpt strip_tac >>
  qpat_x_assum `s1.vs_inst_idx = s2.vs_inst_idx` (assume_tac o SYM) >>
  qpat_x_assum `step_in_block bb s1 = (res1, is_term)` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx`
  >- (
    strip_tac >>
    qexists_tac `Error "block not terminated"` >>
    qpat_x_assum `_ = (res1,is_term)` mp_tac >>
    simp[] >> strip_tac >>
    simp[result_equiv_cfg_def]
  )
  >- (
    rename1 `get_instruction bb _ = SOME inst` >>
    strip_tac >>
    simp[] >>
    `MEM inst bb.bb_instructions` by (
      qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
      simp[get_instruction_def] >> strip_tac >>
      metis_tac[listTheory.MEM_EL]
    ) >>
    `inst.inst_opcode <> PHI` by (metis_tac[block_has_no_phi_inst]) >>
    sg `result_equiv_cfg (step_inst inst s1) (step_inst inst s2)`
    >- (irule step_inst_state_equiv_cfg >> simp[]) >>
    Cases_on `step_inst inst s1`
    >- (
      rename1 `step_inst inst s1 = OK s1'` >>
      Cases_on `step_inst inst s2`
      >| [
        (rename1 `step_inst inst s2 = OK s2'` >>
         simp[] >>
         Cases_on `is_terminator inst.inst_opcode`
         >- (
           simp[] >>
           qpat_x_assum `_ = (res1,is_term)` mp_tac >>
           simp[pairTheory.PAIR_EQ] >> strip_tac >>
           FIRST
             [qpat_x_assum `OK _ = res1`
                (fn th => simp[SYM th, result_equiv_cfg_def]),
              qpat_x_assum `res1 = OK _`
                (fn th => simp[th, result_equiv_cfg_def])]
         )
         >- (
           simp[] >>
           qpat_x_assum `_ = (res1,is_term)` mp_tac >>
           simp[pairTheory.PAIR_EQ] >> strip_tac >>
           FIRST
             [qpat_x_assum `OK _ = res1`
                (fn th =>
                   simp[SYM th, result_equiv_cfg_def,
                        next_inst_state_equiv_cfg]),
              qpat_x_assum `res1 = OK _`
                (fn th =>
                   simp[th, result_equiv_cfg_def,
                        next_inst_state_equiv_cfg])] >>
           irule next_inst_state_equiv_cfg >> simp[] >>
           gvs[result_equiv_cfg_def]
         )),
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def]
      ]
    )
    >- (
      rename1 `step_inst inst s1 = Halt s1'` >>
      Cases_on `step_inst inst s2`
      >| [
        gvs[result_equiv_cfg_def],
        (rename1 `step_inst inst s2 = Halt s2'` >>
         simp[] >>
         qpat_x_assum `_ = (res1,is_term)` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         FIRST
           [qpat_x_assum `Halt _ = res1`
              (fn th => simp[SYM th, result_equiv_cfg_def]),
            qpat_x_assum `res1 = Halt _`
              (fn th => simp[th, result_equiv_cfg_def])]),
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def]
      ]
    )
    >- (
      rename1 `step_inst inst s1 = Revert s1'` >>
      Cases_on `step_inst inst s2`
      >| [
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        (rename1 `step_inst inst s2 = Revert s2'` >>
         simp[] >>
         qpat_x_assum `_ = (res1,is_term)` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         FIRST
           [qpat_x_assum `Revert _ = res1`
              (fn th => simp[SYM th, result_equiv_cfg_def]),
            qpat_x_assum `res1 = Revert _`
              (fn th => simp[th, result_equiv_cfg_def])]),
        gvs[result_equiv_cfg_def]
      ]
    )
    >- (
      rename1 `step_inst inst s1 = Error e1` >>
      Cases_on `step_inst inst s2`
      >| [
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        gvs[result_equiv_cfg_def],
        (rename1 `step_inst inst s2 = Error e2` >>
         simp[] >>
         qpat_x_assum `_ = (res1,is_term)` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         FIRST
           [qpat_x_assum `Error _ = res1`
              (fn th => simp[SYM th, result_equiv_cfg_def]),
            qpat_x_assum `res1 = Error _`
              (fn th => simp[th, result_equiv_cfg_def])])
      ]
    )
  )
QED

Theorem run_block_no_phi_equiv_cfg:
  !bb s1 s2.
    block_has_no_phi bb /\
    state_equiv_cfg s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx
  ==>
    result_equiv_cfg (run_block bb s1) (run_block bb s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  Cases_on `step_in_block bb s1` >>
  rename1 `step_in_block bb s1 = (q,r)` >>
  drule_all step_in_block_no_phi_equiv_cfg >> strip_tac >>
  rename1 `step_in_block bb s2 = (q2,r)` >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[] >>
  Cases_on `q` >> Cases_on `q2` >> gvs[result_equiv_cfg_def]
  >- (
    `v.vs_halted = v'.vs_halted` by fs[state_equiv_cfg_def] >>
    Cases_on `v.vs_halted` >> gvs[]
    >- simp[result_equiv_cfg_def]
    >- (
      Cases_on `r` >> gvs[]
      >- simp[result_equiv_cfg_def]
      >- (
        `v.vs_inst_idx = s1.vs_inst_idx + 1` by
          metis_tac[step_in_block_inst_idx_succ] >>
        `v'.vs_inst_idx = s2.vs_inst_idx + 1` by
          metis_tac[step_in_block_inst_idx_succ] >>
        `v.vs_inst_idx = v'.vs_inst_idx` by simp[] >>
        first_x_assum irule >>
        simp[]
      )
    )
  )
QED

Theorem run_block_state_equiv_cfg:
  !bb s1 s2.
    state_equiv_cfg s1 s2 /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx
  ==>
    result_equiv_cfg (run_block bb s1) (run_block bb s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  Cases_on `step_in_block bb s1` >>
  rename1 `step_in_block bb s1 = (q,r)` >>
  drule_all step_in_block_state_equiv_cfg >> strip_tac >>
  rename1 `step_in_block bb s2 = (q2,r)` >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[] >>
  Cases_on `q` >> Cases_on `q2` >> gvs[result_equiv_cfg_def]
  >- (
    `v.vs_halted = v'.vs_halted` by fs[state_equiv_cfg_def] >>
    Cases_on `v.vs_halted` >> gvs[]
    >- simp[result_equiv_cfg_def]
    >- (
      Cases_on `r` >> gvs[]
      >- simp[result_equiv_cfg_def]
      >- (
        `v.vs_inst_idx = s1.vs_inst_idx + 1` by
          metis_tac[step_in_block_inst_idx_succ] >>
        `v'.vs_inst_idx = s2.vs_inst_idx + 1` by
          metis_tac[step_in_block_inst_idx_succ] >>
        `v.vs_inst_idx = v'.vs_inst_idx` by simp[] >>
        `v.vs_prev_bb = s1.vs_prev_bb` by
          metis_tac[step_in_block_preserves_prev_bb] >>
        `v'.vs_prev_bb = s2.vs_prev_bb` by
          metis_tac[step_in_block_preserves_prev_bb] >>
        `v.vs_prev_bb = v'.vs_prev_bb` by simp[] >>
        first_x_assum irule >>
        simp[]
      )
    )
  )
QED

Theorem run_block_drop_equiv_cfg:
  !bb pref suff s k.
    bb.bb_instructions = pref ++ suff /\
    s.vs_inst_idx = LENGTH pref + k /\
    k <= LENGTH suff
  ==>
    result_equiv_cfg
      (run_block bb s)
      (run_block (bb with bb_instructions := suff) (s with vs_inst_idx := k))
Proof
  qx_gen_tac `bb` >> qx_gen_tac `pref` >> qx_gen_tac `suff` >>
  measureInduct_on `LENGTH suff - k` >>
  rpt strip_tac >> simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[step_in_block_def, get_instruction_def] >> simp[EL_APPEND2] >>
  Cases_on `k < LENGTH suff` >> gvs[result_equiv_cfg_def] >>
  qabbrev_tac `inst = EL k suff` >>
  `result_equiv_cfg (step_inst inst s) (step_inst inst (s with vs_inst_idx := k))` by
    (irule step_inst_state_equiv_cfg >> simp[state_equiv_cfg_def, var_equiv_def, lookup_var_def]) >>
  Cases_on `step_inst inst s` >> Cases_on `step_inst inst (s with vs_inst_idx := k)` >>
  gvs[result_equiv_cfg_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[]
  >- (`v.vs_halted = v'.vs_halted` by gvs[state_equiv_cfg_def] >>
      Cases_on `v.vs_halted` >> gvs[result_equiv_cfg_def])
  >- (
    `state_equiv_cfg (next_inst v) (next_inst v')` by (irule next_inst_state_equiv_cfg >> simp[]) >>
    `(next_inst v).vs_halted = (next_inst v').vs_halted` by gvs[state_equiv_cfg_def] >>
    Cases_on `(next_inst v).vs_halted` >> gvs[result_equiv_cfg_def] >>
    `v.vs_inst_idx = s.vs_inst_idx` by metis_tac[step_inst_preserves_inst_idx] >>
    `(next_inst v).vs_inst_idx = (k + 1) + LENGTH pref` by simp[venomStateTheory.next_inst_def] >>
    `v'.vs_inst_idx = k` by (drule_all step_inst_preserves_inst_idx >> simp[]) >>
    `(next_inst v').vs_inst_idx = k + 1` by simp[venomStateTheory.next_inst_def] >>
    irule result_equiv_cfg_trans >>
    qexists_tac `run_block (bb with bb_instructions := suff)
                           ((next_inst v) with vs_inst_idx := k + 1)` >>
    conj_tac
    >- (first_x_assum irule >> simp[])
    >- (irule run_block_state_equiv_cfg >>
        simp[venomStateTheory.next_inst_def] >>
        conj_tac
        >- (imp_res_tac step_inst_preserves_prev_bb >> gvs[])
        >- gvs[state_equiv_cfg_def, var_equiv_def, lookup_var_def])
  )
QED

(* run_block_fn_irrelevant removed - run_block no longer takes fn parameter *)

(* If run_block returns OK, the state is not halted *)
Theorem run_block_ok_not_halted:
  !bb s s'. run_block bb s = OK s' ==> ~s'.vs_halted
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >> pop_assum mp_tac >>
  simp[Once run_block_def] >> Cases_on `step_in_block bb s` >> simp[] >>
  Cases_on `q` >> simp[] >> rpt strip_tac >> gvs[]
  >- (
    qpat_x_assum `run_block _ _ = _` mp_tac >> simp[Once run_block_def] >>
    rpt strip_tac >> gvs[] >>
    Cases_on `v.vs_halted` >> gvs[] >> Cases_on `r` >> gvs[])
  >- (qpat_x_assum `run_block _ _ = _` mp_tac >> simp[Once run_block_def])
  >- (qpat_x_assum `run_block _ _ = _` mp_tac >> simp[Once run_block_def])
  >- (qpat_x_assum `run_block _ _ = _` mp_tac >> simp[Once run_block_def])
QED

(* Terminators that return OK with ~halted set inst_idx = 0 via jump_to *)
Theorem run_block_ok_inst_idx:
  !bb s s'.
    run_block bb s = OK s' /\ ~s'.vs_halted ==> s'.vs_inst_idx = 0
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_block _ _ = _` mp_tac >> simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
  >- ((* terminator case *)
    strip_tac >> gvs[] >>
    qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
    Cases_on `step_inst x s` >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    strip_tac >> gvs[] >>
    Cases_on `x.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]
    >- (fs[venomSemTheory.step_inst_def, AllCaseEqs(),
           venomStateTheory.jump_to_def] >> gvs[])
    >- (qpat_x_assum `step_inst _ _ = _` mp_tac >>
        simp[venomSemTheory.step_inst_def, AllCaseEqs(),
             venomStateTheory.jump_to_def] >> strip_tac >> gvs[])
    >- (qpat_x_assum `step_inst _ _ = _` mp_tac >>
        simp[venomSemTheory.step_inst_def, AllCaseEqs()])
    >- (rpt (qpat_x_assum `step_inst _ _ = _` mp_tac >>
             simp[venomSemTheory.step_inst_def, AllCaseEqs()]))
    >- (fs[venomSemTheory.step_inst_def, venomSemTheory.exec_result_distinct])
    >- (qpat_x_assum `step_inst _ _ = _` mp_tac >>
        simp[venomSemTheory.step_inst_def, venomSemTheory.exec_result_distinct])
    >- (rpt (qpat_x_assum `step_inst _ _ = _` mp_tac >>
             simp[venomSemTheory.step_inst_def, venomSemTheory.exec_result_distinct]))
    >- (qpat_x_assum `step_inst _ _ = _` mp_tac >>
        simp[venomSemTheory.step_inst_def, venomSemTheory.exec_result_distinct]))
  >- ((* non-terminator case - use IH *)
    strip_tac >>
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - v.vs_inst_idx` mp_tac) >>
    strip_tac >>
    `v.vs_inst_idx = s.vs_inst_idx + 1` by (drule step_in_block_inst_idx_succ >> simp[]) >>
    `s.vs_inst_idx < LENGTH bb.bb_instructions` by
      (qpat_x_assum `step_in_block _ _ = _` mp_tac >>
       simp[venomSemTheory.step_in_block_def, AllCaseEqs(),
            venomInstTheory.get_instruction_def]) >>
    first_x_assum irule >>
    conj_tac >- simp[] >>
    conj_tac >- simp[] >>
    qexistsl_tac [`bb`, `v`] >> simp[])
QED

val _ = export_theory();
