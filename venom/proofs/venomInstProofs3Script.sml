(*
 * Per-Opcode State Preservation Lemmas (Part 3: Static Field Proofs 2)
 *
 * Accounts and memory field preservation. Classify opcodes before
 * rewriting only the selected, cached step equation.
 *
 * Split from venomInstProofsScript.sml for build timeout reasons.
 *)

Theory venomInstProofs3
Ancestors
  finite_map pred_set
  venomState venomExecSemantics venomInst venomEffects
  stateEquivProofs
  venomInstProofs1 venomInstProofs2

Theorem exec_pure1_memory_preserves:
  exec_pure1 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_pure1_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_read0_memory_preserves:
  exec_read0 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_read0_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_gas_memory_preserves:
  exec_gas y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_gas_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_read1_memory_preserves:
  exec_read1 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_read1_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_pure2_memory_preserves:
  exec_pure2 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_pure2_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_pure3_memory_preserves:
  exec_pure3 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_pure3_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

(* Index the exported equations without expanding the full opcode case. *)
val step_inst_base_opcode_rewrites = let
  fun key th = let
    val (_, body) = strip_forall (concl th)
    val (guard, _) = dest_imp body
  in rhs guard end
in map (fn th => (key th, th))
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs) end;

fun rewrite_step_inst_base_opcode eq = let
  val (_, rewrite) = valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq)))
    step_inst_base_opcode_rewrites)
in PURE_ONCE_REWRITE_TAC [MATCH_MP rewrite eq] end;

val step_inst_base_opcode_tac =
  qpat_assum `inst.inst_opcode = _` rewrite_step_inst_base_opcode;

(* No evaluation of memory, account or arithmetic payloads during pruning. *)
val account_memory_class_ss = bool_ss ++
  simpLib.type_ssfrag ``:opcode`` ++ simpLib.type_ssfrag ``:effect`` ++
  rewrites [is_terminator_def, is_alloca_op_def,
    write_effects_def, empty_effects_def, all_effects_def,
    IN_DIFF, IN_INSERT, NOT_IN_EMPTY];

(* Reduce envelopes and record projections, not values stored in the frame. *)
val account_memory_projection_ss = pure_ss ++ boolSimps.BOOL_ss ++
  simpLib.type_ssfrag ``:exec_result`` ++
  simpLib.type_ssfrag ``:operand`` ++
  simpLib.type_ssfrag ``:'a list`` ++ simpLib.type_ssfrag ``:'a option`` ++
  simpLib.type_ssfrag ``:'a # 'b`` ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM, LET_THM,
     update_var_def, exec_write2_def, mcopy_def, mstore_def, mstore8_def,
     write_memory_with_expansion_def, sstore_def, tstore_def,
     istore_shared_fields];

Theorem step_inst_base_preserves_account_memory_fields:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode ==>
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
     s'.vs_accounts = s.vs_accounts) /\
    (Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
     s'.vs_memory = s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  qpat_x_assum `~is_terminator _`
    (CHECK_ASSUME_TAC o SIMP_RULE account_memory_class_ss []) >>
  qpat_x_assum `~is_alloca_op _`
    (CHECK_ASSUME_TAC o SIMP_RULE account_memory_class_ss []) >>
  asm_simp_tac account_memory_class_ss [] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >>
  FIRST [
    drule exec_pure1_static_preserves >>
      imp_res_tac exec_pure1_memory_preserves >> asm_simp_tac bool_ss [],
    drule exec_read0_static_preserves >>
      imp_res_tac exec_read0_memory_preserves >> asm_simp_tac bool_ss [],
    drule exec_gas_static_preserves >>
      imp_res_tac exec_gas_memory_preserves >> asm_simp_tac bool_ss [],
    drule exec_read1_static_preserves >>
      imp_res_tac exec_read1_memory_preserves >> asm_simp_tac bool_ss [],
    drule exec_pure2_static_preserves >>
      imp_res_tac exec_pure2_memory_preserves >> asm_simp_tac bool_ss [],
    drule exec_pure3_static_preserves >>
      imp_res_tac exec_pure3_memory_preserves >> asm_simp_tac bool_ss [],
    qpat_x_assum `_ = OK s'` mp_tac >>
    simp_tac account_memory_projection_ss [AllCaseEqs()] >>
    rpt strip_tac >>
    FIRST [
      asm_simp_tac account_memory_projection_ss [] >> gvs[] >> NO_TAC,
      drule exec_ext_call_static_preserves >> asm_simp_tac bool_ss [],
      gvs[exec_create_def, extract_venom_result_def, AllCaseEqs(),
          write_memory_with_expansion_def, update_var_def] >>
      pairarg_tac >> gvs[]
    ]
  ]
QED

Theorem step_inst_base_preserves_accounts:
  (* A non-terminating, non-alloca instruction with no BALANCE or STORAGE
     write effects preserves the accounts field of the state. *)
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  metis_tac[step_inst_base_preserves_account_memory_fields]
QED

Theorem step_inst_base_preserves_memory:
  (* A non-terminating, non-alloca instruction with no MEMORY write effect
     preserves the memory field of the state. *)
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  metis_tac[step_inst_base_preserves_account_memory_fields]
QED
