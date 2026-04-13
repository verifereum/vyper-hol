(*
 * Simplify CFG Pass — prev_bb equivalence toolkit
 *
 * States that agree on everything except vs_prev_bb.
 * Used for the PHI compensation argument in merge_step_equiv.
 *
 * Factored out from CollapseScript for build performance:
 * the 80-opcode case split in step_inst_base_prev_bb_equiv_other
 * is expensive but only needs to build once.
 *)

Theory simplifyCfgPrevBB
Ancestors
  simplifyCfgDefs stateEquiv venomExecSemantics venomExecProofs venomWf
  venomInst venomState cfgTransform stateEquivProps


(* Two states agree on everything except vs_prev_bb *)
Definition prev_bb_equiv_def:
  prev_bb_equiv s1 s2 <=>
    s1 with vs_prev_bb := s2.vs_prev_bb = s2
End

(* Lift prev_bb_equiv to exec_result *)
Definition result_prev_bb_equiv_def:
  result_prev_bb_equiv r1 r2 <=>
    case (r1, r2) of
    | (OK s1, OK s2) => prev_bb_equiv s1 s2
    | (Error e1, Error e2) => e1 = e2
    | (Halt h1, Halt h2) => prev_bb_equiv h1 h2
    | (Abort a1 h1, Abort a2 h2) => a1 = a2 /\ prev_bb_equiv h1 h2
    | (IntRet v1 s1, IntRet v2 s2) => v1 = v2 /\ prev_bb_equiv s1 s2
    | _ => F
End

(* prev_bb_equiv is reflexive *)
Theorem prev_bb_equiv_refl:
  !s. prev_bb_equiv s s
Proof
  rw[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* prev_bb_equiv is symmetric *)
Theorem prev_bb_equiv_sym:
  !s1 s2. prev_bb_equiv s1 s2 ==> prev_bb_equiv s2 s1
Proof
  rw[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* prev_bb_equiv implies execution_equiv {} *)
Theorem prev_bb_equiv_implies_exec_equiv:
  !s1 s2. prev_bb_equiv s1 s2 ==> execution_equiv {} s1 s2
Proof
  rw[prev_bb_equiv_def, execution_equiv_def, lookup_var_def] >>
  fs[venomStateTheory.venom_state_component_equality]
QED

(* result_prev_bb_equiv for non-OK results implies result_equiv {} *)
Theorem result_prev_bb_equiv_terminal_implies_result_equiv:
  !r1 r2. result_prev_bb_equiv r1 r2 /\
           (!s1 s2. r1 <> OK s1 \/ r2 <> OK s2) ==>
           result_equiv {} r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[result_prev_bb_equiv_def, result_equiv_def] >>
  rpt strip_tac >> imp_res_tac prev_bb_equiv_implies_exec_equiv
QED

(* ================================================================
   prev_bb commutation helpers — eval/update/state operations
   all commute with vs_prev_bb changes.
   ================================================================ *)

Theorem eval_op_prev_bb[local]:
  !op st pb. eval_operand op (st with vs_prev_bb := pb) = eval_operand op st
Proof Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_ops_prev_bb[local]:
  !ops st pb.
    eval_operands ops (st with vs_prev_bb := pb) = eval_operands ops st
Proof Induct >> simp[eval_operands_def, eval_op_prev_bb]
QED

Theorem update_var_prev_bb[local]:
  !x v st pb.
    update_var x v (st with vs_prev_bb := pb) =
    (update_var x v st) with vs_prev_bb := pb
Proof simp[update_var_def]
QED

Theorem halt_state_prev_bb[local]:
  !st pb.
    halt_state (st with vs_prev_bb := pb) =
    (halt_state st) with vs_prev_bb := pb
Proof simp[halt_state_def]
QED

Theorem revert_state_prev_bb[local]:
  !st pb.
    revert_state (st with vs_prev_bb := pb) =
    (revert_state st) with vs_prev_bb := pb
Proof simp[revert_state_def]
QED

Theorem set_returndata_prev_bb[local]:
  !rd st pb.
    set_returndata rd (st with vs_prev_bb := pb) =
    (set_returndata rd st) with vs_prev_bb := pb
Proof simp[set_returndata_def]
QED

Theorem write_mem_prev_bb[local]:
  !off bytes st pb.
    write_memory_with_expansion off bytes (st with vs_prev_bb := pb) =
    (write_memory_with_expansion off bytes st) with vs_prev_bb := pb
Proof simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem mstore_prev_bb[local]:
  !off v st pb.
    mstore off v (st with vs_prev_bb := pb) =
    (mstore off v st) with vs_prev_bb := pb
Proof simp[mstore_def, LET_THM]
QED

Theorem mstore8_prev_bb[local]:
  !off v st pb.
    mstore8 off v (st with vs_prev_bb := pb) =
    (mstore8 off v st) with vs_prev_bb := pb
Proof simp[mstore8_def, LET_THM]
QED

Theorem mcopy_prev_bb[local]:
  !d s sz st pb.
    mcopy d s sz (st with vs_prev_bb := pb) =
    (mcopy d s sz st) with vs_prev_bb := pb
Proof simp[mcopy_def, LET_THM, write_memory_with_expansion_def]
QED

Theorem sstore_prev_bb[local]:
  !k v st pb.
    sstore k v (st with vs_prev_bb := pb) =
    (sstore k v st) with vs_prev_bb := pb
Proof simp[sstore_def, contract_storage_def, LET_THM]
QED

Theorem tstore_prev_bb[local]:
  !k v st pb.
    tstore k v (st with vs_prev_bb := pb) =
    (tstore k v st) with vs_prev_bb := pb
Proof simp[tstore_def, contract_transient_def, LET_THM]
QED

Theorem mload_prev_bb[local]:
  !off st pb. mload off (st with vs_prev_bb := pb) = mload off st
Proof simp[mload_def]
QED

Theorem sload_prev_bb[local]:
  !k st pb. sload k (st with vs_prev_bb := pb) = sload k st
Proof simp[sload_def, contract_storage_def]
QED

Theorem tload_prev_bb[local]:
  !k st pb. tload k (st with vs_prev_bb := pb) = tload k st
Proof simp[tload_def, contract_transient_def]
QED

Theorem jump_to_prev_bb[local]:
  !lbl st pb.
    jump_to lbl (st with vs_prev_bb := pb) = jump_to lbl st
Proof simp[jump_to_def]
QED

Theorem prev_bb_equiv_update:
  !st pb1 pb2.
    prev_bb_equiv (st with vs_prev_bb := pb1) (st with vs_prev_bb := pb2)
Proof
  rw[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

Theorem prev_bb_equiv_set[local]:
  !st pb. prev_bb_equiv (st with vs_prev_bb := pb) st
Proof
  rw[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

Theorem prev_bb_equiv_update_idx:
  !s1 s2 n. prev_bb_equiv s1 s2 ==>
    prev_bb_equiv (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rw[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* exec_pure/read/write helpers *)
val pb_rw = [eval_op_prev_bb, eval_ops_prev_bb, update_var_prev_bb,
             halt_state_prev_bb, revert_state_prev_bb, set_returndata_prev_bb,
             write_mem_prev_bb, mstore_prev_bb, mstore8_prev_bb,
             mcopy_prev_bb, sstore_prev_bb, tstore_prev_bb,
             mload_prev_bb, sload_prev_bb, tload_prev_bb,
             jump_to_prev_bb, prev_bb_equiv_update];

Theorem exec_pure1_prev_bb[local]:
  !f inst st pb.
    exec_pure1 f inst (st with vs_prev_bb := pb) =
    case exec_pure1 f inst st of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt gen_tac >>
  simp[exec_pure1_def, eval_op_prev_bb, update_var_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem exec_pure2_prev_bb[local]:
  !f inst st pb.
    exec_pure2 f inst (st with vs_prev_bb := pb) =
    case exec_pure2 f inst st of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt gen_tac >>
  simp[exec_pure2_def, eval_op_prev_bb, update_var_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem exec_pure3_prev_bb[local]:
  !f inst st pb.
    exec_pure3 f inst (st with vs_prev_bb := pb) =
    case exec_pure3 f inst st of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt gen_tac >>
  simp[exec_pure3_def, eval_op_prev_bb, update_var_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem exec_read0_prev_bb[local]:
  !g inst st pb.
    (!st pb. g (st with vs_prev_bb := pb) = g st) ==>
    exec_read0 g inst (st with vs_prev_bb := pb) =
    case exec_read0 g inst st of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt strip_tac >>
  simp[exec_read0_def, update_var_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem exec_read1_prev_bb[local]:
  !g inst st pb.
    (!v st pb. g v (st with vs_prev_bb := pb) = g v st) ==>
    exec_read1 g inst (st with vs_prev_bb := pb) =
    case exec_read1 g inst st of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt strip_tac >>
  simp[exec_read1_def, eval_op_prev_bb, update_var_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem exec_write2_prev_bb[local]:
  !f inst st pb.
    (!v1 v2 st pb. f v1 v2 (st with vs_prev_bb := pb) =
                   (f v1 v2 st) with vs_prev_bb := pb) ==>
    exec_write2 f inst (st with vs_prev_bb := pb) =
    case exec_write2 f inst st of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt strip_tac >>
  simp[exec_write2_def, eval_op_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

(* External call helpers *)
Theorem venom_to_tx_params_prev_bb[local]:
  !st pb. venom_to_tx_params (st with vs_prev_bb := pb) = venom_to_tx_params st
Proof simp[venom_to_tx_params_def]
QED

Theorem make_venom_call_state_prev_bb[local]:
  !st t g v cd code is_s pb.
    make_venom_call_state (st with vs_prev_bb := pb) t g v cd code is_s =
    make_venom_call_state st t g v cd code is_s
Proof simp[make_venom_call_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem make_venom_delegatecall_state_prev_bb[local]:
  !st t g cd code is_s pb.
    make_venom_delegatecall_state (st with vs_prev_bb := pb) t g cd code is_s =
    make_venom_delegatecall_state st t g cd code is_s
Proof
  simp[make_venom_delegatecall_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem make_venom_create_state_prev_bb[local]:
  !st na g v ic pb.
    make_venom_create_state (st with vs_prev_bb := pb) na g v ic =
    make_venom_create_state st na g v ic
Proof simp[make_venom_create_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem extract_venom_result_prev_bb[local]:
  !st ov retOff retSize rr pb.
    extract_venom_result (st with vs_prev_bb := pb) ov retOff retSize rr =
    OPTION_MAP (\p. (FST p, (SND p) with vs_prev_bb := pb))
      (extract_venom_result st ov retOff retSize rr)
Proof
  rpt gen_tac >> simp[extract_venom_result_def, LET_THM] >>
  Cases_on `rr` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `h` >> Cases_on `t` >> simp[] >>
  Cases_on `x0` >>
  simp[write_memory_with_expansion_def, LET_THM,
       venomStateTheory.venom_state_component_equality] >>
  Cases_on `y` >>
  simp[write_memory_with_expansion_def, LET_THM,
       venomStateTheory.venom_state_component_equality]
QED

Theorem option_case_OPTION_MAP_prev_bb[local]:
  !f x n g.
    option_CASE (OPTION_MAP f x) n g = option_CASE x n (g o f)
Proof Cases_on `x` >> simp[]
QED

val ext_rw = [LET_THM, read_memory_def, extract_venom_result_prev_bb,
              option_case_OPTION_MAP_prev_bb, update_var_prev_bb,
              eval_op_prev_bb];

Theorem exec_ext_call_prev_bb[local]:
  !inst st gas addr value ao as_ ro rs is_s pb.
    exec_ext_call inst (st with vs_prev_bb := pb) gas addr value ao as_ ro rs is_s =
    case exec_ext_call inst st gas addr value ao as_ ro rs is_s of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | Halt s => Halt (s with vs_prev_bb := pb)
    | Abort a s => Abort a (s with vs_prev_bb := pb)
    | IntRet v s => IntRet v (s with vs_prev_bb := pb)
Proof
  rpt gen_tac >>
  simp([exec_ext_call_def, make_venom_call_state_prev_bb] @ ext_rw) >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[update_var_prev_bb, venomStateTheory.venom_state_component_equality]
QED

Theorem exec_delegatecall_prev_bb[local]:
  !inst st gas addr ao as_ ro rs pb.
    exec_delegatecall inst (st with vs_prev_bb := pb) gas addr ao as_ ro rs =
    case exec_delegatecall inst st gas addr ao as_ ro rs of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | Halt s => Halt (s with vs_prev_bb := pb)
    | Abort a s => Abort a (s with vs_prev_bb := pb)
    | IntRet v s => IntRet v (s with vs_prev_bb := pb)
Proof
  rpt gen_tac >>
  simp([exec_delegatecall_def, make_venom_delegatecall_state_prev_bb] @ ext_rw) >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[update_var_prev_bb, venomStateTheory.venom_state_component_equality]
QED

Theorem exec_create_prev_bb[local]:
  !inst st value offset sz salt_opt pb.
    exec_create inst (st with vs_prev_bb := pb) value offset sz salt_opt =
    case exec_create inst st value offset sz salt_opt of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | Halt s => Halt (s with vs_prev_bb := pb)
    | Abort a s => Abort a (s with vs_prev_bb := pb)
    | IntRet v s => IntRet v (s with vs_prev_bb := pb)
Proof
  rpt gen_tac >>
  simp([exec_create_def, make_venom_create_state_prev_bb] @ ext_rw) >>
  Cases_on `salt_opt` >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[update_var_prev_bb, venomStateTheory.venom_state_component_equality]
QED

Theorem exec_alloca_prev_bb[local]:
  !inst st alloc_size pb.
    exec_alloca inst (st with vs_prev_bb := pb) alloc_size =
    case exec_alloca inst st alloc_size of
    | OK s => OK (s with vs_prev_bb := pb)
    | Error e => Error e
    | r => r
Proof
  rpt gen_tac >> simp[exec_alloca_def, next_alloca_offset_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> simp[update_var_def,
    venomStateTheory.venom_state_component_equality]
QED

(* ================================================================
   MAIN: step_inst_base preserves prev_bb_equiv for non-PHI opcodes.
   ================================================================ *)

Theorem prev_bb_equiv_as_update:
  !s1 s2. prev_bb_equiv s1 s2 ==> s1 = s2 with vs_prev_bb := s1.vs_prev_bb
Proof
  rw[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* Case 1: pseudo non-PHI opcodes *)
Theorem step_inst_base_prev_bb_equiv_pseudo[local]:
  !inst s1 s2.
    inst.inst_opcode <> PHI /\ is_pseudo inst.inst_opcode /\
    prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  imp_res_tac prev_bb_equiv_as_update >> pop_assum SUBST1_TAC >>
  Cases_on `inst.inst_opcode` >> fs[is_pseudo_def] >>
  simp[step_inst_base_def, result_prev_bb_equiv_def,
       eval_op_prev_bb, update_var_prev_bb, prev_bb_equiv_update,
       prev_bb_equiv_set] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[prev_bb_equiv_update, prev_bb_equiv_set]
QED

(* Case 2: terminator opcodes *)
Theorem step_inst_base_prev_bb_equiv_term[local]:
  !inst s1 s2.
    is_terminator inst.inst_opcode /\ prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  imp_res_tac prev_bb_equiv_as_update >> pop_assum SUBST1_TAC >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  simp[step_inst_base_def, result_prev_bb_equiv_def,
       eval_op_prev_bb, eval_ops_prev_bb, update_var_prev_bb,
       halt_state_prev_bb, revert_state_prev_bb, set_returndata_prev_bb,
       jump_to_prev_bb, prev_bb_equiv_update, prev_bb_equiv_set, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[prev_bb_equiv_update, prev_bb_equiv_set, prev_bb_equiv_refl,
       venomStateTheory.venom_state_component_equality]
QED

(* Case 3: non-pseudo, non-terminator — 80 opcodes, expensive *)
Theorem step_inst_base_prev_bb_equiv_other[local]:
  !inst s1 s2.
    ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
    prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  imp_res_tac prev_bb_equiv_as_update >> pop_assum SUBST1_TAC >>
  Cases_on `inst.inst_opcode` >> fs[is_pseudo_def, is_terminator_def] >>
  simp[step_inst_base_def, result_prev_bb_equiv_def,
       eval_op_prev_bb, eval_ops_prev_bb, update_var_prev_bb,
       write_mem_prev_bb, mstore_prev_bb, mstore8_prev_bb,
       mcopy_prev_bb, sstore_prev_bb, tstore_prev_bb,
       mload_prev_bb, sload_prev_bb, tload_prev_bb,
       exec_pure1_prev_bb, exec_pure2_prev_bb, exec_pure3_prev_bb,
       exec_read0_prev_bb, exec_read1_prev_bb, exec_write2_prev_bb,
       exec_alloca_prev_bb, exec_ext_call_prev_bb,
       exec_delegatecall_prev_bb, exec_create_prev_bb,
       halt_state_prev_bb, revert_state_prev_bb, set_returndata_prev_bb,
       extract_venom_result_prev_bb,
       venom_to_tx_params_prev_bb,
       make_venom_call_state_prev_bb,
       make_venom_delegatecall_state_prev_bb,
       make_venom_create_state_prev_bb,
       option_case_OPTION_MAP_prev_bb,
       prev_bb_equiv_update, prev_bb_equiv_set, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[prev_bb_equiv_update, prev_bb_equiv_set, prev_bb_equiv_refl,
       venomStateTheory.venom_state_component_equality]
QED

(* Main theorem: combine all cases *)
Theorem step_inst_base_prev_bb_equiv:
  !inst s1 s2.
    inst.inst_opcode <> PHI /\ prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >>
  Cases_on `is_pseudo inst.inst_opcode` >>
  metis_tac[step_inst_base_prev_bb_equiv_pseudo,
            step_inst_base_prev_bb_equiv_term,
            step_inst_base_prev_bb_equiv_other]
QED

(* step_inst_base preserves vs_prev_bb for non-PHI non-terminator.
   Proof: case split on opcode. Non-terminator non-PHI opcodes use
   *_prev_bb helpers which show f(s with prev_bb := pb) = f(s) with prev_bb := pb,
   meaning prev_bb passes through unchanged. *)
Theorem step_inst_base_preserves_prev_bb:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode ==>
    v.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  (* Rewrite s as (s with vs_prev_bb := s.vs_prev_bb) — a no-op *)
  `s = s with vs_prev_bb := s.vs_prev_bb` by
    simp[venomStateTheory.venom_state_component_equality] >>
  pop_assum (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  (* Now the assumption has the form step_inst_base inst (s with vs_prev_bb := pb) = OK v *)
  Cases_on `is_pseudo inst.inst_opcode`
  >- (
    Cases_on `inst.inst_opcode` >> fs[is_pseudo_def, is_terminator_def] >>
    fs[step_inst_base_def, update_var_prev_bb] >>
    BasicProvers.EVERY_CASE_TAC >>
    fs[venomStateTheory.venom_state_component_equality]
  ) >>
  Cases_on `inst.inst_opcode` >>
  fs[is_pseudo_def, is_terminator_def, step_inst_base_def,
     eval_op_prev_bb, eval_ops_prev_bb, update_var_prev_bb,
     write_mem_prev_bb, mstore_prev_bb, mstore8_prev_bb,
     mcopy_prev_bb, sstore_prev_bb, tstore_prev_bb,
     mload_prev_bb, sload_prev_bb, tload_prev_bb,
     exec_pure1_prev_bb, exec_pure2_prev_bb, exec_pure3_prev_bb,
     exec_read0_prev_bb, exec_read1_prev_bb, exec_write2_prev_bb,
     exec_alloca_prev_bb, exec_ext_call_prev_bb,
     exec_delegatecall_prev_bb, exec_create_prev_bb,
     halt_state_prev_bb, revert_state_prev_bb, set_returndata_prev_bb,
     extract_venom_result_prev_bb,
     venom_to_tx_params_prev_bb,
     make_venom_call_state_prev_bb,
     make_venom_delegatecall_state_prev_bb,
     make_venom_create_state_prev_bb,
     option_case_OPTION_MAP_prev_bb, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[venomStateTheory.venom_state_component_equality]
QED

(* resolve_phi commutes with label substitution *)
Theorem resolve_phi_subst_label:
  !ops old new.
    old <> new /\ phi_well_formed ops /\ ~MEM (Label new) ops ==>
    resolve_phi new (MAP (subst_label_op old new) ops) = resolve_phi old ops
Proof
  ho_match_mp_tac venomWfTheory.phi_well_formed_ind >>
  rw[resolve_phi_def, subst_label_op_def, phi_well_formed_def] >>
  Cases_on `lbl = old` >> fs[resolve_phi_def]
QED

(* PHI with substituted labels: running the substituted PHI on s1
   (with vs_prev_bb = SOME new) and the original PHI on s2
   (with vs_prev_bb = SOME old) gives prev_bb_equiv results *)
Theorem step_phi_subst_prev_bb_equiv:
  !old new inst s1 s2.
    inst.inst_opcode = PHI /\
    old <> new /\
    phi_well_formed inst.inst_operands /\
    ~MEM (Label new) inst.inst_operands /\
    s1.vs_prev_bb = SOME new /\
    s2.vs_prev_bb = SOME old /\
    prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv
      (step_inst_base (subst_label_inst old new inst) s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `s1 = s2 with vs_prev_bb := SOME new`
    by fs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`inst.inst_operands`, `old`, `new`]
    mp_tac resolve_phi_subst_label >>
  simp[] >> DISCH_TAC >>
  simp[step_inst_base_def, subst_label_inst_def,
       result_prev_bb_equiv_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[eval_op_prev_bb, update_var_prev_bb, prev_bb_equiv_update,
     prev_bb_equiv_set,
     venomStateTheory.venom_state_component_equality]
QED

(* eval_one_phi with label substitution: same output/value on both sides *)
Theorem eval_one_phi_subst_prev_bb_equiv[local]:
  !old new inst s1 s2.
    inst.inst_opcode = PHI /\
    old <> new /\
    phi_well_formed inst.inst_operands /\
    ~MEM (Label new) inst.inst_operands /\
    s1.vs_prev_bb = SOME new /\
    s2.vs_prev_bb = SOME old /\
    prev_bb_equiv s1 s2 ==>
    eval_one_phi s1 (subst_label_inst old new inst) =
    eval_one_phi s2 inst
Proof
  rw[eval_one_phi_def, subst_label_inst_def] >>
  simp[] >>
  drule_all resolve_phi_subst_label >> strip_tac >> simp[] >>
  Cases_on `resolve_phi old inst.inst_operands` >> simp[] >>
  Cases_on `x` >>
  fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
     prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

(* eval_phis with label substitution preserves prev_bb_equiv.
   PHI prefix of bb1 = subst_label of PHI prefix of bb2. *)
Theorem eval_phis_subst_prev_bb_equiv:
  !insts1 insts2 s1 s2 old new.
    prev_bb_equiv s1 s2 /\
    s1.vs_prev_bb = SOME new /\
    s2.vs_prev_bb = SOME old /\
    old <> new /\
    LENGTH insts1 = LENGTH insts2 /\
    (!i. i < LENGTH insts2 ==>
         if (EL i insts2).inst_opcode = PHI then
           EL i insts1 = subst_label_inst old new (EL i insts2)
         else
           EL i insts1 = EL i insts2) /\
    EVERY (\inst. phi_well_formed inst.inst_operands)
          (FILTER (\inst. inst.inst_opcode = PHI) insts2) /\
    EVERY (\inst. ~MEM (Label new) inst.inst_operands)
          (FILTER (\inst. inst.inst_opcode = PHI) insts2) ==>
    result_prev_bb_equiv
      (eval_phis s1 insts1) (eval_phis s2 insts2)
Proof
  Induct_on `insts2` >> rpt gen_tac >> strip_tac
  >- (Cases_on `insts1` >> gvs[] >>
      gvs[eval_phis_def, result_prev_bb_equiv_def])
  \\
  Cases_on `insts1` >> gvs[] >>
  rename1 `result_prev_bb_equiv (eval_phis s1 (i1::t1)) _` >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
  >- (
    `i1 = subst_label_inst old new h` by (
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    pop_assum SUBST_ALL_TAC >>
    `(subst_label_inst old new h).inst_opcode = PHI`
      by rw[cfgTransformTheory.subst_label_inst_def] >>
    simp[eval_phis_def] >>
    drule_all eval_one_phi_subst_prev_bb_equiv >>
    disch_then (fn th => REWRITE_TAC [th]) >>
    Cases_on `eval_one_phi s2 h`
    >- simp[result_prev_bb_equiv_def]
    >>
    Cases_on `x` >> simp[] >>
    `result_prev_bb_equiv (eval_phis s1 t1) (eval_phis s2 insts2)` by (
      last_x_assum irule >> simp[] >>
      rpt strip_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
    ) >>
    strip_assume_tac
      (Q.SPECL [`s1`, `t1`]
               venomExecProofsTheory.eval_phis_ok_or_error) >>
    strip_assume_tac
      (Q.SPECL [`s2`, `insts2`]
               venomExecProofsTheory.eval_phis_ok_or_error) >>
    gvs[result_prev_bb_equiv_def] >>
    qpat_x_assum `prev_bb_equiv _ _` mp_tac >>
    simp[prev_bb_equiv_def, update_var_prev_bb,
         venomStateTheory.update_var_def,
         venomStateTheory.venom_state_component_equality]
  )
  \\
  `i1 = h` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[eval_phis_def, result_prev_bb_equiv_def]
QED

(* step_inst for non-PHI non-INVOKE preserves prev_bb_equiv *)
Theorem step_inst_prev_bb_equiv:
  !fuel ctx inst s1 s2.
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv (step_inst fuel ctx inst s1)
                         (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``step_inst fuel ctx inst s1 = step_inst_base inst s1``
    (fn th => REWRITE_TAC[th])
  >- (irule venomExecSemanticsTheory.step_inst_non_invoke >> simp[]) >>
  SUBGOAL_THEN ``step_inst fuel ctx inst s2 = step_inst_base inst s2``
    (fn th => REWRITE_TAC[th])
  >- (irule venomExecSemanticsTheory.step_inst_non_invoke >> simp[]) >>
  irule step_inst_base_prev_bb_equiv >> simp[]
QED

(* INVOKE preserves prev_bb_equiv: same instruction, different prev_bb *)
Theorem eval_operand_prev_bb[local]:
  !op s1 s2. prev_bb_equiv s1 s2 ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases >> rw[venomStateTheory.eval_operand_def,
              venomStateTheory.lookup_var_def] >>
  fs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
QED

Theorem eval_operands_prev_bb[local]:
  !ops s1 s2. prev_bb_equiv s1 s2 ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> rw[venomStateTheory.eval_operands_def] >>
  imp_res_tac eval_operand_prev_bb >> rw[] >>
  res_tac >> rw[]
QED

Theorem setup_callee_prev_bb[local]:
  !fn args s1 s2. prev_bb_equiv s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[venomExecSemanticsTheory.setup_callee_def,
     prev_bb_equiv_def,
     venomStateTheory.venom_state_component_equality]
QED

Theorem merge_callee_state_prev_bb[local]:
  !s1 s2 callee. prev_bb_equiv s1 s2 ==>
    prev_bb_equiv (merge_callee_state s1 callee)
                  (merge_callee_state s2 callee)
Proof
  rw[prev_bb_equiv_def, venomExecSemanticsTheory.merge_callee_state_def,
     venomStateTheory.venom_state_component_equality]
QED

Theorem update_var_prev_bb[local]:
  !v x s1 s2. prev_bb_equiv s1 s2 ==>
    prev_bb_equiv (update_var v x s1) (update_var v x s2)
Proof
  rw[prev_bb_equiv_def, venomStateTheory.update_var_def,
     venomStateTheory.venom_state_component_equality]
QED

Theorem FOLDL_update_var_prev_bb[local]:
  !pairs s1 s2. prev_bb_equiv s1 s2 ==>
    prev_bb_equiv
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> rw[listTheory.FOLDL] >>
  Cases_on `h` >> rw[listTheory.FOLDL] >>
  first_x_assum irule >> irule update_var_prev_bb >> rw[]
QED

Theorem bind_outputs_prev_bb_SOME[local]:
  !outs vals s1 s2 s1'. prev_bb_equiv s1 s2 /\
    bind_outputs outs vals s1 = SOME s1' ==>
    ?s2'. bind_outputs outs vals s2 = SOME s2' /\ prev_bb_equiv s1' s2'
Proof
  rw[venomExecSemanticsTheory.bind_outputs_def] >> rw[] >>
  irule_at Any FOLDL_update_var_prev_bb >> rw[]
QED

Theorem bind_outputs_prev_bb_NONE[local]:
  !outs vals s1 s2. prev_bb_equiv s1 s2 /\
    bind_outputs outs vals s1 = NONE ==>
    bind_outputs outs vals s2 = NONE
Proof
  rw[venomExecSemanticsTheory.bind_outputs_def]
QED

Theorem step_inst_invoke_prev_bb_equiv:
  !fuel ctx inst s1 s2.
    inst.inst_opcode = INVOKE /\ prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `!ops. eval_operands ops s1 = eval_operands ops s2` by
    (strip_tac >> irule eval_operands_prev_bb >> rw[]) >>
  `!fn args. setup_callee fn args s1 = setup_callee fn args s2` by
    (ntac 2 strip_tac >> irule setup_callee_prev_bb >> rw[]) >>
  ASM_REWRITE_TAC[venomExecSemanticsTheory.step_inst_def] >>
  BasicProvers.every_case_tac >>
  rw[result_prev_bb_equiv_def, prev_bb_equiv_refl] >>
  `prev_bb_equiv (merge_callee_state s1 v) (merge_callee_state s2 v)` by
    (irule merge_callee_state_prev_bb >> rw[]) >>
  (drule_all bind_outputs_prev_bb_SOME ORELSE
   drule_all bind_outputs_prev_bb_NONE) >> gvs[]
QED

(* step_inst preserves prev_bb_equiv for ALL opcodes except PHI.
   Subsumes step_inst_prev_bb_equiv (which excludes INVOKE). *)
Theorem step_inst_all_prev_bb_equiv:
  !fuel ctx inst s1 s2.
    inst.inst_opcode <> PHI /\ prev_bb_equiv s1 s2 ==>
    result_prev_bb_equiv
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule step_inst_invoke_prev_bb_equiv >> ASM_REWRITE_TAC[])
  >> irule step_inst_prev_bb_equiv >> ASM_REWRITE_TAC[]
QED

(* Instruction loop prev_bb_equiv: given a per-instruction
   result_prev_bb_equiv hypothesis for two blocks with the same
   length and terminator pattern, run_block_non_phis gives result_prev_bb_equiv. *)
Theorem run_block_non_phis_prev_bb_equiv_gen:
  !n fuel ctx bb1 bb2 s1 s2.
    n = LENGTH bb1.bb_instructions - s1.vs_inst_idx /\
    prev_bb_equiv s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i. i < LENGTH bb2.bb_instructions ==>
         is_terminator (EL i bb1.bb_instructions).inst_opcode =
         is_terminator (EL i bb2.bb_instructions).inst_opcode) /\
    (!i s1' s2'. i < LENGTH bb2.bb_instructions /\ prev_bb_equiv s1' s2' ==>
       result_prev_bb_equiv
         (step_inst fuel ctx (EL i bb1.bb_instructions) s1')
         (step_inst fuel ctx (EL i bb2.bb_instructions) s2'))
    ==>
    result_prev_bb_equiv
      (run_block_non_phis fuel ctx bb1 s1)
      (run_block_non_phis fuel ctx bb2 s2)
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `s1.vs_inst_idx < LENGTH bb1.bb_instructions`
  >- (
    (* idx < LENGTH: inductive case *)
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
    `s1.vs_inst_idx < LENGTH bb2.bb_instructions` by fs[] >>
    simp[venomInstTheory.get_instruction_def] >>
    (* Derive per-instruction step equiv *)
    qpat_assum `!i s1' s2'. _`
      (qspecl_then [`s2.vs_inst_idx`, `s1`, `s2`] mp_tac) >>
    (impl_tac >- simp[]) >> DISCH_TAC >>
    (* Case split on step results *)
    Cases_on `step_inst fuel ctx (EL s2.vs_inst_idx bb1.bb_instructions) s1` >>
    Cases_on `step_inst fuel ctx (EL s2.vs_inst_idx bb2.bb_instructions) s2` >>
    fs[result_prev_bb_equiv_def] >>
    TRY (simp[result_prev_bb_equiv_def] >> NO_TAC) >>
    (* Only OK-OK remains — case split on terminator *)
    Cases_on `is_terminator (EL s2.vs_inst_idx bb1.bb_instructions).inst_opcode`
    >- suspend "term" >>
    (* non-terminator: recurse via IH *)
    suspend "nonterm"
  ) >>
  (* base case: idx >= LENGTH *)
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[venomInstTheory.get_instruction_def] >>
  simp[result_prev_bb_equiv_def]
QED

Resume run_block_non_phis_prev_bb_equiv_gen[term]:
  (* Assumptions: is_terminator bb1[idx] = T, prev_bb_equiv v v',
     step_inst ... = OK v/v'. Goal: result_prev_bb_equiv of halted/ok *)
  rpt strip_tac >>
  (* Derive is_terminator bb2[idx] from biconditional *)
  `is_terminator (EL s2.vs_inst_idx bb2.bb_instructions).inst_opcode` by (
    qpat_x_assum `!i. _ ==> (is_terminator _ <=> _)`
      (qspec_then `s2.vs_inst_idx` mp_tac) >> simp[]
  ) >>
  asm_rewrite_tac[] >>
  (* prev_bb_equiv implies same vs_halted *)
  `v.vs_halted = v'.vs_halted` by (
    fs[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]
  ) >>
  Cases_on `v.vs_halted` >> asm_rewrite_tac[] >>
  simp[] >> fs[prev_bb_equiv_def]
QED

Resume run_block_non_phis_prev_bb_equiv_gen[nonterm]:
  rpt strip_tac >>
  `~is_terminator (EL s2.vs_inst_idx bb2.bb_instructions).inst_opcode` by (
    qpat_x_assum `!i. _ ==> (is_terminator _ <=> _)`
      (qspec_then `s2.vs_inst_idx` mp_tac) >> simp[]
  ) >>
  asm_rewrite_tac[] >> simp[] >>
  `prev_bb_equiv (v with vs_inst_idx := SUC s2.vs_inst_idx)
                 (v' with vs_inst_idx := SUC s2.vs_inst_idx)` by (
    irule prev_bb_equiv_update_idx >> simp[]
  ) >>
  qpat_x_assum `!m. m < _ ==> !fuel' ctx'. _`
    (qspec_then `LENGTH bb2.bb_instructions - (s2.vs_inst_idx + 1)` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb1`, `bb2`,
    `v with vs_inst_idx := SUC s2.vs_inst_idx`,
    `v' with vs_inst_idx := SUC s2.vs_inst_idx`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[]
QED

Finalise run_block_non_phis_prev_bb_equiv_gen;

(* run_block prev_bb_equiv wrapper.
   In main semantics, run_block = exec_block with inst_idx := 0.
   eval_phis premise kept for backward compat but unused. *)
Theorem run_block_prev_bb_equiv_gen:
  !fuel ctx bb1 bb2 s1 s2.
    prev_bb_equiv s1 s2 /\
    result_prev_bb_equiv
      (eval_phis s1 bb1.bb_instructions)
      (eval_phis s2 bb2.bb_instructions) /\
    phi_prefix_length bb1.bb_instructions =
      phi_prefix_length bb2.bb_instructions /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i. i < LENGTH bb2.bb_instructions ==>
         is_terminator (EL i bb1.bb_instructions).inst_opcode =
         is_terminator (EL i bb2.bb_instructions).inst_opcode) /\
    (!i s1' s2'. i < LENGTH bb2.bb_instructions /\ prev_bb_equiv s1' s2' ==>
       result_prev_bb_equiv
         (step_inst fuel ctx (EL i bb1.bb_instructions) s1')
         (step_inst fuel ctx (EL i bb2.bb_instructions) s2'))
    ==>
    result_prev_bb_equiv
      (run_block fuel ctx bb1 s1)
      (run_block fuel ctx bb2 s2)
(* TEMPORARILY CHEATED — parallel PHI: run_block_def now has eval_phis case.
   Original proof: simp[run_block_def] >> irule run_block_non_phis_prev_bb_equiv_gen
   >> simp[] >> irule prev_bb_equiv_update_idx >> simp[].
   Fix: handle eval_phis case using result_prev_bb_equiv assumption. *)
Proof cheat
QED

val _ = export_theory();
