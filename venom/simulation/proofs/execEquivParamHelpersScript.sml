(*
 * Parameterized Execution Equivalence — Step Inst Helpers
 *
 * Per-opcode step_inst_base preservation proofs.
 * Depends on execEquivParamBase for core helpers.
 *)

Theory execEquivParamHelpers
Ancestors
  execEquivParamBase
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
Libs
  finite_mapTheory listTheory rich_listTheory

open execEquivParamLib

(* ==========================================================================
   ML tactics (use Base theorems which are now in scope)
   ========================================================================== *)

fun vsr_eval_ops_tac () =
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> vsr_irule vsr_eval_operand >> simp[] >>
    rpt strip_tac >> gvs[])

fun vsr_eval_rewrite_tac () =
  vsr_eval_ops_tac () >>
  drule_all_then strip_assume_tac vsr_R_ok_fields >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[]

(* Cache dispatch and the exact read-data projection; never expand the whole
   VSR context while splitting an instruction's operand/result envelope. *)
val vsr_opcode_rewrites = map (fn th => let
  val (_, body) = strip_forall (concl th)
  val (guard, _) = dest_imp body
in (rhs guard, th) end)
  (CONJUNCTS step_inst_base_opcode_eqs);

val vsr_field_eqs = vsr_R_ok_fields |> SPEC_ALL |> UNDISCH |>
  CONJUNCTS |> map (GEN_ALL o DISCH_ALL);
val vsr_memory_eq = List.nth (vsr_field_eqs, 4);
val vsr_accounts_eq = List.nth (vsr_field_eqs, 3);
val vsr_params_eq = List.nth (vsr_field_eqs, 11);
val vsr_data_code_eq = LIST_CONJ (map (fn i => List.nth (vsr_field_eqs, i))
  [18, 20]);
val vsr_copy_data_eq = LIST_CONJ (map (fn i => List.nth (vsr_field_eqs, i))
  [0, 6]);
val vsr_log_data_eq = LIST_CONJ (map (fn i => List.nth (vsr_field_eqs, i))
  [0, 4, 16]);

val vsr_envelope_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [list_case_def, optionTheory.option_case_def, pairTheory.pair_case_thm,
   pairTheory.UNCURRY, TypeBase.case_def_of ``:operand``,
   MEM, LET_THM, lift_result_def];

fun vsr_opcode_tac () =
  qpat_assum `inst.inst_opcode = _` (fn eq => let
    val (_, th) = valOf (List.find
      (fn (key, _) => aconv key (rhs (concl eq))) vsr_opcode_rewrites)
  in PURE_ONCE_REWRITE_TAC [MATCH_MP th eq] end);

fun vsr_dispatch_tac () =
  vsr_opcode_tac () >> asm_simp_tac vsr_envelope_ss [] >>
  REPEAT (BasicProvers.PURE_TOP_CASE_TAC >>
          asm_simp_tac vsr_envelope_ss []);

fun vsr_envelope_tac () =
  vsr_eval_ops_tac () >> vsr_dispatch_tac ();

(* Project just the read expression from the residual frame.  Simplifying
   this congruence does not add every state selector to the assumptions. *)
val vsr_read_ss = srw_ss () ++ rewrites
  [vsr_frame_def, mload_def, sload_def, tload_def,
   contract_storage_def, contract_transient_def];

fun vsr_read_eq_tac () =
  drule_all vsr_R_ok_frame >>
  disch_then (fn eq => fn (asl, goal) => let
    val (value, _) = dest_eq goal
    val project = mk_abs (``s1 : venom_state``, value)
  in (mp_tac (AP_TERM project eq) >> simp_tac vsr_read_ss [])
       (asl, goal) end);

(* Shared terminal writes preserve R_term directly, without reconstructing
   every field of either state. *)
fun vsr_terminal_writes_tac () =
  PURE_REWRITE_TAC [halt_state_def, revert_state_def, set_returndata_def] >>
  vsr_irule vsr_halted_R_term >>
  FIRST [vsr_irule vsr_returndata_R_term, ALL_TAC] >>
  vsr_irule vsr_R_ok_R_term >> simp[];

(* ==========================================================================
   step_inst_base-level helpers
   ========================================================================== *)

Theorem vsr_step_inst_pure2:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ADD;SUB;MUL;Div;SDIV;Mod;SMOD;Exp;
      AND;OR;XOR;SHL;SHR;SAR;SIGNEXTEND;BYTE;EQ;LT;GT;SLT;SGT;OFFSET] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> vsr_opcode_tac () >> simp[] >>
  vsr_irule vsr_exec_pure2 >> simp[]
QED

Theorem vsr_step_inst_pure1:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [NOT;ISZERO] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (simp[step_inst_base_NOT] >>
      vsr_irule vsr_exec_pure1 >> simp[])
  >> simp[step_inst_base_ISZERO] >>
  vsr_irule vsr_exec_pure1 >> simp[]
QED

Theorem vsr_step_inst_pure3:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ADDMOD;MULMOD] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> vsr_opcode_tac () >> simp[] >>
  vsr_irule vsr_exec_pure3 >> simp[]
QED

Theorem vsr_step_inst_read0:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode
      [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;
       COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;
       BLOBBASEFEE;SELFBALANCE;CALLDATASIZE;RETURNDATASIZE;MEMTOP;
       CODESIZE] ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> vsr_opcode_tac () >> simp[] >>
  vsr_irule vsr_exec_read0 >> simp[] >> vsr_read_eq_tac ()
QED

Theorem vsr_step_inst_read1:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode
      [MLOAD;SLOAD;TLOAD;BLOCKHASH;BALANCE;CALLDATALOAD;
       EXTCODESIZE;BLOBHASH;ILOAD;DLOAD] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> vsr_opcode_tac () >> simp[] >>
  vsr_irule vsr_exec_read1 >> simp[] >> rpt gen_tac >> vsr_read_eq_tac ()
QED

Theorem vsr_step_inst_extcodehash:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = EXTCODEHASH /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> vsr_opcode_tac () >> simp[] >>
  vsr_irule vsr_exec_read1 >> simp[] >> rw[] >>
  imp_res_tac vsr_accounts_eq >> gvs[]
QED

Theorem vsr_step_inst_write2:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [MSTORE;MSTORE8;SSTORE;TSTORE] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> vsr_opcode_tac () >> simp[] >>
  vsr_irule vsr_exec_write2 >> simp[] >> rw[] >>
  FIRST [vsr_irule vsr_mstore, vsr_irule vsr_mstore8,
         vsr_irule vsr_sstore, vsr_irule vsr_tstore] >>
  simp[]
QED

Theorem vsr_step_inst_terminator:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [STOP;SINK] ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_dispatch_tac () >>
  vsr_terminal_writes_tac ()
QED

Theorem vsr_step_inst_return:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = RETURN /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> drule_all vsr_memory_eq >> strip_tac >>
  vsr_envelope_tac () >> vsr_terminal_writes_tac ()
QED

Theorem vsr_step_inst_revert:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = REVERT /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> drule_all vsr_memory_eq >> strip_tac >>
  vsr_envelope_tac () >> vsr_terminal_writes_tac ()
QED

Theorem vsr_step_inst_jmp:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = JMP /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> vsr_envelope_tac () >>
  vsr_irule vsr_jump_to >> simp[]
QED

Theorem vsr_step_inst_jnz:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = JNZ /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> vsr_envelope_tac () >>
  vsr_irule vsr_jump_to >> simp[]
QED

Theorem vsr_step_inst_control:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [JMP;JNZ] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >- (irule vsr_step_inst_jmp >> simp[]) >>
  irule vsr_step_inst_jnz >> simp[]
QED

Theorem vsr_step_inst_djmp:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = DJMP /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> vsr_envelope_tac () >>
  vsr_irule vsr_jump_to >> simp[]
QED

Theorem vsr_step_inst_ssa:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [PHI;ASSIGN;NOP] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_envelope_tac () >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_step_inst_assert:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_envelope_tac () >>
  vsr_terminal_writes_tac ()
QED

Theorem vsr_step_inst_sha3:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = SHA3 /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> drule_all vsr_memory_eq >> strip_tac >>
  vsr_envelope_tac () >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_step_inst_mcopy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = MCOPY /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> vsr_envelope_tac () >>
  vsr_irule vsr_mcopy >> simp[]
QED

Theorem vsr_step_inst_istore:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = ISTORE /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> vsr_envelope_tac () >>
  vsr_irule vsr_istore >> simp[]
QED

fun vsr_data_copy_operands_tac () =
  Cases_on `inst.inst_operands` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_dst::ops1` >>
  Cases_on `ops1` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_dst::op_src::ops2` >>
  Cases_on `ops2` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_dst::op_src::op_size::ops3` >>
  reverse (Cases_on `ops3`) >- simp[lift_result_def] >>
  simp[] >>
  Cases_on `eval_operand op_dst s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_src s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_size s2` >> gvs[lift_result_def]

Theorem vsr_step_inst_data_copy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [DLOADBYTES;CODECOPY] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac vsr_data_code_eq >> vsr_envelope_tac () >>
  vsr_irule vsr_write_memory >> simp[]
QED

fun vsr_extcodecopy_operands_tac () =
  Cases_on `inst.inst_operands` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_addr::ops1` >>
  Cases_on `ops1` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_addr::op_dst::ops2` >>
  Cases_on `ops2` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_addr::op_dst::op_src::ops3` >>
  Cases_on `ops3` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_addr::op_dst::op_src::op_size::ops4` >>
  reverse (Cases_on `ops4`) >- simp[lift_result_def] >>
  simp[] >>
  Cases_on `eval_operand op_addr s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_dst s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_src s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_size s2` >> gvs[lift_result_def]

Theorem vsr_step_inst_extcodecopy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = EXTCODECOPY /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> drule_all vsr_accounts_eq >> strip_tac >>
  vsr_envelope_tac () >>
  vsr_irule vsr_write_memory >> simp[]
QED

fun vsr_copy_operands_tac () =
  Cases_on `inst.inst_operands` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_dest::ops1` >>
  Cases_on `ops1` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_dest::op_offset::ops2` >>
  Cases_on `ops2` >- simp[lift_result_def] >>
  rename1 `inst.inst_operands = op_dest::op_offset::op_size::ops3` >>
  reverse (Cases_on `ops3`) >- simp[lift_result_def] >>
  simp[] >>
  Cases_on `eval_operand op_dest s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_offset s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_size s2` >> gvs[lift_result_def]

Theorem vsr_step_inst_copy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [CALLDATACOPY;RETURNDATACOPY] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac vsr_copy_data_eq >> vsr_envelope_tac () >>
  FIRST [vsr_terminal_writes_tac (),
         vsr_irule vsr_write_memory >> simp[]]
QED

(* OFFSET: now handled by vsr_step_inst_pure2 (same as ADD) *)

Theorem vsr_step_inst_param:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = PARAM ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> drule_all vsr_params_eq >> strip_tac >>
  vsr_dispatch_tac () >> vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_step_inst_ret:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = RET /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  `eval_operands inst.inst_operands s1 =
   eval_operands inst.inst_operands s2` by
    (vsr_irule vsr_eval_operands >> simp[]) >>
  vsr_dispatch_tac () >>
  vsr_irule vsr_R_ok_R_term >> simp[]
QED

Theorem vsr_step_inst_log:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = LOG /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac vsr_log_data_eq >> vsr_eval_ops_tac () >>
  vsr_opcode_tac () >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[lift_result_def] >>
  Cases_on `h` >> simp[lift_result_def] >>
  rename1 `Lit tc :: rest` >>
  `!op. MEM op rest ==> eval_operand op s1 = eval_operand op s2` by
    (rw[] >> first_x_assum (qspec_then `op` mp_tac) >> simp[]) >>
  IF_CASES_TAC >> simp[lift_result_def] >>
  `2 <= LENGTH rest` by simp[] >>
  `MEM (HD (REVERSE rest)) rest` by
    (once_rewrite_tac[GSYM MEM_REVERSE] >>
     Cases_on `REVERSE rest` >> fs[]) >>
  `MEM (EL 1 (REVERSE rest)) rest` by
    (once_rewrite_tac[GSYM MEM_REVERSE] >>
     irule rich_listTheory.EL_MEM >> simp[]) >>
  `eval_operand (HD (REVERSE rest)) s1 =
   eval_operand (HD (REVERSE rest)) s2` by res_tac >>
  `eval_operand (EL 1 (REVERSE rest)) s1 =
   eval_operand (EL 1 (REVERSE rest)) s2` by res_tac >>
  `eval_operands (DROP 2 (REVERSE rest)) s1 =
   eval_operands (DROP 2 (REVERSE rest)) s2` by (
    qsuff_tac `!ops. (!op. MEM op ops ==> eval_operand op s1 = eval_operand op s2) ==>
               eval_operands ops s1 = eval_operands ops s2`
    >- (disch_then irule >> rw[] >> res_tac >>
        metis_tac[MEM_DROP_IMP, MEM_REVERSE])
    >> Induct >> rw[eval_operands_def]) >>
  simp[] >>
  REPEAT (BasicProvers.PURE_TOP_CASE_TAC >>
          asm_simp_tac vsr_envelope_ss []) >>
  vsr_irule vsr_logs_R_ok >> simp[]
QED
