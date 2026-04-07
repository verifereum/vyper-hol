(*
 * Function Inliner — Clone NP Combiner
 *
 * Proves step_inst_base_clone_np by combining category helpers
 * (from CalleeSim) with ML-generated per-opcode theorems.
 * Also provides result_equiv_refl and result_equiv_trans.
 *
 * Three ML abstraction layers:
 *   mk_np_thm      — 0-2 operand opcodes: SIB + EVERY_CASE_TAC
 *   mk_seq_np      — 3+ operand non-ext opcodes: sequential eval + close
 *   mk_ext_call_np — ext call opcodes: sequential eval + fold + exec helper
 *)

Theory functionInlinerCloneNp
Ancestors
  functionInlinerCalleeSim functionInlinerCloneSim
  functionInlinerDefs
  venomExecSemantics venomInst stateEquiv stateEquivProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerDefsTheory functionInlinerCalleeSimTheory
     functionInlinerCloneSimTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     stateEquivTheory stateEquivPropsTheory

val rec_eq = venomStateTheory.venom_state_component_equality;

(* ================================================================
   Infrastructure: SIB precomputation
   ================================================================ *)

val inst_eq_lemma = prove(
  ``inst.inst_opcode = (opc:opcode) ==> inst = inst with inst_opcode := opc``,
  simp[instruction_component_equality]);

fun mk_cond_sib opc_tm =
  let
    val uncond = SIMP_CONV (srw_ss()) [step_inst_base_def]
      (``step_inst_base (inst with inst_opcode := ^opc_tm) (ss:venom_state)``)
    val inst_eq = UNDISCH (INST [``opc:opcode`` |-> opc_tm] inst_eq_lemma)
    val result = REWRITE_RULE [SYM inst_eq] uncond
  in DISCH (mk_eq(``(inst:instruction).inst_opcode``, opc_tm)) result end;

(* Special opcodes (handled by mk_np_thm/mk_copy_np/ext call Theorems) *)
val special_opcodes = [
  ("NOP", ``NOP``), ("ASSIGN", ``ASSIGN``), ("PHI", ``PHI``),
  ("JMP", ``JMP``), ("JNZ", ``JNZ``), ("DJMP", ``DJMP``),
  ("RETURN", ``RETURN``), ("REVERT", ``REVERT``),
  ("STOP", ``STOP``), ("SINK", ``SINK``), ("INVALID", ``INVALID``),
  ("SELFDESTRUCT", ``SELFDESTRUCT``),
  ("ASSERT", ``ASSERT``), ("ASSERT_UNREACHABLE", ``ASSERT_UNREACHABLE``),
  ("LOG", ``LOG``), ("SHA3", ``SHA3``),
  ("MCOPY", ``MCOPY``), ("CALLDATACOPY", ``CALLDATACOPY``),
  ("CODECOPY", ``CODECOPY``), ("EXTCODECOPY", ``EXTCODECOPY``),
  ("RETURNDATACOPY", ``RETURNDATACOPY``),
  ("ISTORE", ``ISTORE``), ("DLOADBYTES", ``DLOADBYTES``),
  ("CALL", ``CALL``), ("STATICCALL", ``STATICCALL``),
  ("DELEGATECALL", ``DELEGATECALL``),
  ("CREATE", ``CREATE``), ("CREATE2", ``CREATE2``)
];

(* Bulk opcodes by exec category (handled by mk_cat_np via category helpers) *)
val cat_pure2 =
  [("ADD",``ADD``), ("SUB",``SUB``), ("MUL",``MUL``),
   ("Div",``Div``), ("Mod",``Mod``), ("SDIV",``SDIV``),
   ("SMOD",``SMOD``), ("Exp",``Exp``), ("EQ",``EQ``),
   ("LT",``LT``), ("GT",``GT``), ("SLT",``SLT``),
   ("SGT",``SGT``), ("AND",``AND``), ("OR",``OR``),
   ("XOR",``XOR``), ("SHL",``SHL``), ("SHR",``SHR``),
   ("SAR",``SAR``), ("SIGNEXTEND",``SIGNEXTEND``),
   ("BYTE",``BYTE``), ("OFFSET",``OFFSET``)];
val cat_pure1 = [("ISZERO",``ISZERO``), ("NOT",``NOT``)];
val cat_pure3 = [("ADDMOD",``ADDMOD``), ("MULMOD",``MULMOD``)];
val cat_read0 =
  [("CALLER",``CALLER``), ("ADDRESS",``ADDRESS``),
   ("CALLVALUE",``CALLVALUE``), ("GAS",``GAS``),
   ("ORIGIN",``ORIGIN``), ("GASPRICE",``GASPRICE``),
   ("CHAINID",``CHAINID``), ("COINBASE",``COINBASE``),
   ("TIMESTAMP",``TIMESTAMP``), ("NUMBER",``NUMBER``),
   ("PREVRANDAO",``PREVRANDAO``), ("GASLIMIT",``GASLIMIT``),
   ("BASEFEE",``BASEFEE``), ("BLOBBASEFEE",``BLOBBASEFEE``),
   ("SELFBALANCE",``SELFBALANCE``),
   ("CALLDATASIZE",``CALLDATASIZE``),
   ("RETURNDATASIZE",``RETURNDATASIZE``),
   ("MSIZE",``MSIZE``), ("CODESIZE",``CODESIZE``)];
val cat_read1 =
  [("MLOAD",``MLOAD``), ("SLOAD",``SLOAD``), ("TLOAD",``TLOAD``),
   ("BLOCKHASH",``BLOCKHASH``), ("BLOBHASH",``BLOBHASH``),
   ("BALANCE",``BALANCE``), ("CALLDATALOAD",``CALLDATALOAD``),
   ("EXTCODESIZE",``EXTCODESIZE``), ("ILOAD",``ILOAD``),
   ("DLOAD",``DLOAD``), ("EXTCODEHASH",``EXTCODEHASH``)];
val cat_write2 =
  [("MSTORE",``MSTORE``), ("MSTORE8",``MSTORE8``), ("SSTORE",``SSTORE``), ("TSTORE",``TSTORE``)];

val all_opcodes = special_opcodes @
  cat_pure2 @ cat_pure1 @ cat_pure3 @
  cat_read0 @ cat_read1 @ cat_write2;

val _ = print "Pre-computing SIB reductions...\n";
val sib_table : (string * thm) list =
  map (fn (n,t) => let val _ = print ("  " ^ n ^ "\n")
                   in (n, mk_cond_sib t) end) all_opcodes;
val _ = print "Done.\n";

fun lookup_sib name =
  case List.find (fn (n,_) => n = name) sib_table of
    SOME (_,th) => th
  | NONE => raise Fail ("No precomputed sib for " ^ name);

(* Standard conclusion shape *)
val clone_np_concl = ``
  clone_rel_np prefix labels s_callee s_clone /\
  inst.inst_opcode = (opc:opcode) /\
  EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
  case step_inst_base inst s_callee of
    OK sc =>
      ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            OK sc' /\ clone_rel_np prefix labels sc sc'
  | Halt sc =>
      ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Halt sc' /\ shared_globals_np sc sc'
  | Abort a sc =>
      ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Abort a sc' /\ shared_globals_np sc sc'
  | _ => T
``;

(* ================================================================
   Layer 1: mk_np_thm — for 0-2 operand opcodes
   SIB + EVERY_CASE_TAC + custom closing tactic
   ================================================================ *)

fun mk_np_thm opc_tm sib_lemma extra_tac =
  let val concl_tm = subst [``opc:opcode`` |-> opc_tm] clone_np_concl
  in prove(gen_all concl_tm,
     rpt strip_tac >>
     simp[sib_lemma, clone_inst_opcode] >>
     BasicProvers.EVERY_CASE_TAC >> gvs[] >>
     extra_tac)
  end;

(* Reusable tactic fragments for mk_np_thm *)
val eval_tac =
  TRY (imp_res_tac eval_operand_clone_np_some >> gvs[]) >>
  TRY (imp_res_tac eval_operands_clone_np_some >> gvs[]);

val rel_close_tac =
  fs[clone_rel_np_def, shared_globals_np_def, rec_eq,
     update_var_def, FLOOKUP_UPDATE, FDOM_FUPDATE] >>
  rpt strip_tac >> TRY (Cases_on `v' = s` >> gvs[]) >>
  TRY (res_tac >> simp[]) >>
  TRY (imp_res_tac STRCAT_RIGHT_CANCEL >> gvs[]);

val globals_close_tac =
  fs[clone_rel_np_def, shared_globals_np_def, rec_eq,
     halt_state_def, revert_state_def, set_returndata_def,
     read_memory_def];

(* ================================================================
   Layer 2: mk_seq_np — for 3+ operand non-ext opcodes
   Sequential eval_operand resolution + custom close
   ================================================================ *)

(* mk_copy_np: for 3-4 operand memory-write opcodes.
   Uses EVERY_CASE_TAC to handle all operand list + eval cases at once,
   avoiding fragile variable name dependencies. *)
fun mk_copy_np name opc_tm close_tac =
  let
    val _ = print ("  " ^ name ^ "\n")
    val concl_tm = subst [``opc:opcode`` |-> opc_tm] clone_np_concl
  in prove(gen_all concl_tm,
     rpt strip_tac >>
     simp[lookup_sib name, clone_inst_opcode, clone_instruction_def] >>
     BasicProvers.EVERY_CASE_TAC >> gvs[] >>
     imp_res_tac eval_operand_clone_np_some >> gvs[] >>
     close_tac)
  end;

(* Close tactic for memory-write opcodes: shared globals preserved *)
val mem_write_close_tac =
  fs[clone_rel_np_def, shared_globals_np_def] >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM, read_memory_def,
       halt_state_def, set_returndata_def];

(* ================================================================
   Bridge: strengthen "| _ => T" to full Halt/Abort conclusions
   for exec functions that only return OK or Error.
   ================================================================ *)

(* Bridge: if exec_f only returns OK or Error, promote "| _ => T" to full form.
   Category helpers prove: clone_rel_np ==> case exec_f ... of OK => P | _ => T
   Combiner needs: case exec_f ... of OK => P | Halt => Q | Abort => R | _ => T
   Since exec_f never returns Halt/Abort/IntRet, the extra arms are vacuous. *)
Theorem ok_error_lift_np[local]:
  !f_callee f_clone prefix labels.
    ((?sc. f_callee = OK sc) \/ (?e. f_callee = Error e)) ==>
    ((case f_callee of
        OK sc => ?sc'. f_clone = OK sc' /\ clone_rel_np prefix labels sc sc'
      | _ => T) ==>
     (case f_callee of
        OK sc => ?sc'. f_clone = OK sc' /\ clone_rel_np prefix labels sc sc'
      | Halt sc => ?sc'. f_clone = Halt sc' /\ shared_globals_np sc sc'
      | Abort a sc => ?sc'. f_clone = Abort a sc' /\ shared_globals_np sc sc'
      | _ => T))
Proof
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* ================================================================
   Layer 2b: mk_cat_np — bulk opcodes via category helpers + bridge
   After SIB expansion, goal has exec_FOO form. Bridge promotes
   "| _ => T" to full Halt/Abort, then irule category helper.
   ================================================================ *)

(* Definitions needed to close category helper premises *)
val sg_np_read_defs = [shared_globals_np_def, mload_def, sload_def, tload_def,
                       contract_storage_def, contract_transient_def];
val sg_np_write_defs = [clone_rel_np_def, shared_globals_np_def,
                        mstore_def, mstore8_def, sstore_def, tstore_def,
                        contract_storage_def, contract_transient_def, LET_THM];

fun mk_cat_np name opc_tm cat_th cat_def close_tac =
  let
    val _ = print ("  " ^ name ^ "\n")
    val concl_tm = subst [``opc:opcode`` |-> opc_tm] clone_np_concl
  in prove(gen_all concl_tm,
     rpt strip_tac >>
     simp[lookup_sib name, clone_inst_opcode] >>
     irule ok_error_lift_np >>
     conj_tac >- (simp[cat_def] >> BasicProvers.EVERY_CASE_TAC) >>
     irule cat_th >>
     close_tac)
  end;

val _ = print "Generating bulk category clone_np theorems...\n";
local
  fun p2 (n,opc) = mk_cat_np n opc exec_pure2_clone_np exec_pure2_def (simp[])
  fun p1 (n,opc) = mk_cat_np n opc exec_pure1_clone_np exec_pure1_def (simp[])
  fun p3 (n,opc) = mk_cat_np n opc exec_pure3_clone_np exec_pure3_def (simp[])
  fun r0 (n,opc) = mk_cat_np n opc exec_read0_clone_np exec_read0_def
                      (simp[] >> gvs sg_np_read_defs)
  fun r1 (n,opc) = mk_cat_np n opc exec_read1_clone_np exec_read1_def
                      (simp[] >> gvs sg_np_read_defs)
  fun w2 (n,opc) = mk_cat_np n opc exec_write2_clone_np exec_write2_def
                      (rpt strip_tac >> gvs sg_np_write_defs)
in
  val sbc_np_cat_pure2 = map p2 cat_pure2
  val sbc_np_cat_pure1 = map p1 cat_pure1
  val sbc_np_cat_pure3 = map p3 cat_pure3
  val sbc_np_cat_read0 = map r0 cat_read0
  val sbc_np_cat_read1 = map r1 cat_read1
  val sbc_np_cat_write2 = map w2 cat_write2
end;
val sbc_np_category = sbc_np_cat_pure2 @ sbc_np_cat_pure1 @ sbc_np_cat_pure3 @
                      sbc_np_cat_read0 @ sbc_np_cat_read1 @ sbc_np_cat_write2;
val _ = print "Bulk category clone_np theorems generated.\n";

(* ================================================================
   Layer 3: ext call opcodes — as explicit Theorems
   Uses mono256 + bridge lemmas (ok_or_error + ext_call_np_lift).
   ================================================================ *)

fun mono256 th =
  let val tvs = type_vars_in_term (concl th)
  in INST_TYPE (map (fn tv => tv |-> ``:256``) tvs) th end;

Theorem exec_ext_call_ok_or_error[local]:
  !inst (ss:venom_state) (g:256 word) (a:256 word) (v:256 word)
   (ao:256 word) (as_:256 word) (ro:256 word) (rs:256 word) (st:bool).
    (?sc. exec_ext_call inst ss g a v ao as_ ro rs st = OK sc) \/
    (?e. exec_ext_call inst ss g a v ao as_ ro rs st = Error e)
Proof
  rpt gen_tac >> simp[exec_ext_call_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC
QED

Theorem exec_delegatecall_ok_or_error[local]:
  !inst (ss:venom_state) (g:256 word) (a:256 word)
   (ao:256 word) (as_:256 word) (ro:256 word) (rs:256 word).
    (?sc. exec_delegatecall inst ss g a ao as_ ro rs = OK sc) \/
    (?e. exec_delegatecall inst ss g a ao as_ ro rs = Error e)
Proof
  rpt gen_tac >> simp[exec_delegatecall_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC
QED

Theorem exec_create_ok_or_error[local]:
  !inst (ss:venom_state) (v:256 word) (ao:256 word) (as_:256 word)
   (salt_opt:256 word option).
    (?sc. exec_create inst ss v ao as_ salt_opt = OK sc) \/
    (?e. exec_create inst ss v ao as_ salt_opt = Error e)
Proof
  rpt gen_tac >> simp[exec_create_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC
QED

Theorem ext_call_np_lift[local]:
  !f_callee f_clone prefix labels.
    ((?sc. f_callee = OK sc) \/ (?e. f_callee = Error e)) ==>
    ((case f_callee of
        OK sc => ?sc'. f_clone = OK sc' /\ clone_rel_np prefix labels sc sc'
      | Halt v8 => T | Abort v9 v10 => T | IntRet v11 v12 => T
      | Error e => ?e'. f_clone = Error e') ==>
     (case f_callee of
        OK sc => ?sc'. f_clone = OK sc' /\ clone_rel_np prefix labels sc sc'
      | Halt sc => ?sc'. f_clone = Halt sc' /\ shared_globals_np sc sc'
      | Abort a sc => ?sc'. f_clone = Abort a sc' /\ shared_globals_np sc sc'
      | _ => T))
Proof
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* Shared tactics for ext call proofs: sequential operand eval + propagate *)
val seq_eval_1 =
  Cases_on `eval_operand h s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[];
val seq_eval_2 = seq_eval_1 >>
  Cases_on `eval_operand h' s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[];
val seq_eval_3 = seq_eval_2 >>
  Cases_on `eval_operand h'' s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[];
val seq_eval_4 = seq_eval_3 >>
  Cases_on `eval_operand h'3' s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[];
val seq_eval_6 = seq_eval_4 >>
  Cases_on `eval_operand h'4' s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[] >>
  Cases_on `eval_operand h'5' s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[];
val seq_eval_7 = seq_eval_6 >>
  Cases_on `eval_operand h'6' s_callee` >> fs[] >>
  imp_res_tac eval_operand_clone_np_some >> fs[];

(* List destructuring (alternating t/t').
   After Cases_on `inst.inst_operands`, cons gives h::t.
   Pattern: t -> h'::t', t' -> h''::t, t -> h'3'::t', etc.
   destruct_N destroys N cons cells, leaving remaining tail.
   The last tail var alternates: even N -> t', odd N -> t *)
val destruct_3 =
  Cases_on `inst.inst_operands` >> simp[] >>   (* h::t *)
  Cases_on `t` >> simp[] >>                    (* h'::t' *)
  Cases_on `t'` >> simp[] >>                   (* h''::t *)
  Cases_on `t` >> simp[];                      (* [] *)
val destruct_4 =
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >>                    (* h'3'::t' *)
  Cases_on `t'` >> simp[];                     (* [] *)
val destruct_6 =
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >>                    (* h'5'::t' -- tail is t' *)
  Cases_on `t'` >> simp[];                     (* [] *)
val destruct_7 =
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[];                      (* [] *)

(* Shared field assumptions *)
val call_ctx_eq =
  (SUBGOAL_THEN ``s_callee.vs_call_ctx = s_clone.vs_call_ctx``
    ASSUME_TAC >- fs[clone_rel_np_def, shared_globals_np_def]);
val accts_eq =
  (SUBGOAL_THEN ``s_callee.vs_accounts = s_clone.vs_accounts``
    ASSUME_TAC >- fs[clone_rel_np_def, shared_globals_np_def]);

(* ================================================================
   Per-opcode theorems
   ================================================================ *)
val _ = print "Generating per-opcode clone_np theorems...\n";

(* --- 0-2 operand simple opcodes --- *)
val sbc_np_NOP = (print "  NOP\n";
  mk_np_thm ``NOP`` (lookup_sib "NOP") ALL_TAC);
val sbc_np_ASSIGN = (print "  ASSIGN\n";
  mk_np_thm ``ASSIGN`` (lookup_sib "ASSIGN")
    (eval_tac >> irule update_var_clone_rel_np >> simp[]));
val sbc_np_PHI = (print "  PHI\n";
  mk_np_thm ``PHI`` (lookup_sib "PHI")
    (`s_clone.vs_prev_bb = OPTION_MAP (STRCAT prefix) s_callee.vs_prev_bb` by
       fs[clone_rel_np_def] >>
     Cases_on `s_callee.vs_prev_bb` >> gvs[] >>
     imp_res_tac resolve_phi_clone >> gvs[] >>
     Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
     imp_res_tac eval_operand_clone_np_some >> gvs[] >>
     irule update_var_clone_rel_np >> simp[]));

fun mk_jmp_np name opc_tm = (print ("  " ^ name ^ "\n");
  mk_np_thm opc_tm (lookup_sib name)
    (gvs[EVERY_DEF, clone_operand_def] >>
     TRY (imp_res_tac eval_operand_clone_np_some >> gvs[]) >>
     simp[jump_to_def] >> rel_close_tac));
val sbc_np_JMP = mk_jmp_np "JMP" ``JMP``;
val sbc_np_JNZ = mk_jmp_np "JNZ" ``JNZ``;

fun mk_assert_np name opc_tm = (print ("  " ^ name ^ "\n");
  mk_np_thm opc_tm (lookup_sib name) (eval_tac >> globals_close_tac));
val sbc_np_ASSERT = mk_assert_np "ASSERT" ``ASSERT``;
val sbc_np_ASSERT_UNREACHABLE = mk_assert_np "ASSERT_UNREACHABLE" ``ASSERT_UNREACHABLE``;

fun mk_halt_np name opc_tm = (print ("  " ^ name ^ "\n");
  mk_np_thm opc_tm (lookup_sib name) globals_close_tac);
val sbc_np_STOP = mk_halt_np "STOP" ``STOP``;
val sbc_np_SINK = mk_halt_np "SINK" ``SINK``;
val sbc_np_INVALID = mk_halt_np "INVALID" ``INVALID``;

fun mk_ret_np name opc_tm = (print ("  " ^ name ^ "\n");
  mk_np_thm opc_tm (lookup_sib name) (eval_tac >> globals_close_tac));
val sbc_np_RETURN = mk_ret_np "RETURN" ``RETURN``;
val sbc_np_REVERT = mk_ret_np "REVERT" ``REVERT``;

val sbc_np_SELFDESTRUCT = (print "  SELFDESTRUCT\n";
  mk_np_thm ``SELFDESTRUCT`` (lookup_sib "SELFDESTRUCT")
    (eval_tac >> fs[halt_state_def, clone_rel_np_def, shared_globals_np_def, rec_eq]));

val sbc_np_SHA3 = (print "  SHA3\n";
  mk_np_thm ``SHA3`` (lookup_sib "SHA3") (eval_tac >> rel_close_tac));

val sbc_np_ISTORE = (print "  ISTORE\n";
  mk_np_thm ``ISTORE`` (lookup_sib "ISTORE") (eval_tac >> rel_close_tac));

(* --- DJMP: variable-length label list (custom) --- *)
val extract_labels_clone = prove(``
  !ops prefix labels.
    EVERY (\op. !l. op = Label l ==> MEM l labels) ops ==>
    extract_labels (MAP (clone_operand prefix labels) ops) =
    OPTION_MAP (MAP (STRCAT prefix)) (extract_labels ops)
``,
  Induct >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def, clone_operand_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  Cases_on `extract_labels (MAP (clone_operand prefix labels) ops)` >>
  Cases_on `extract_labels ops` >> gvs[]);

val sbc_np_DJMP = let
  val _ = print "  DJMP\n"
  val concl_tm = subst [``opc:opcode`` |-> ``DJMP``] clone_np_concl
in prove(gen_all concl_tm,
  rpt strip_tac >>
  simp[lookup_sib "DJMP", clone_inst_opcode, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `eval_operand h s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  `EVERY (\op. !l. op = Label l ==> MEM l labels) t` by
    fs[EVERY_DEF] >>
  imp_res_tac extract_labels_clone >>
  Cases_on `extract_labels t` >> simp[] >>
  simp[LET_THM, jump_to_def, EL_MAP] >>
  IF_CASES_TAC >> simp[] >>
  rel_close_tac)
end;

(* --- LOG: variable-length topic list (custom) --- *)
val sbc_np_LOG = let
  val _ = print "  LOG\n"
  val concl_tm = subst [``opc:opcode`` |-> ``LOG``] clone_np_concl
in prove(gen_all concl_tm,
  rpt strip_tac >>
  simp[lookup_sib "LOG", clone_inst_opcode, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[clone_operand_def] >>
  simp[LET_THM, LENGTH_MAP] >>
  IF_CASES_TAC >> simp[] >>
  (* Destructure t to get HD, EL 1, DROP 2 *)
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  simp[clone_operand_def, MAP_DROP] >>
  (* Split all eval cases, then propagate clone results *)
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac eval_operand_clone_np_some >>
  imp_res_tac eval_operands_clone_np_some >>
  gvs[] >>
  fs[clone_rel_np_def, shared_globals_np_def, rec_eq])
end;

(* --- 3-4 operand memory-write opcodes (EVERY_CASE_TAC + close) --- *)
val sbc_np_MCOPY = mk_copy_np "MCOPY" ``MCOPY`` mem_write_close_tac;
val sbc_np_CALLDATACOPY = mk_copy_np "CALLDATACOPY" ``CALLDATACOPY`` mem_write_close_tac;
val sbc_np_CODECOPY = mk_copy_np "CODECOPY" ``CODECOPY`` mem_write_close_tac;
val sbc_np_EXTCODECOPY = mk_copy_np "EXTCODECOPY" ``EXTCODECOPY`` mem_write_close_tac;
val sbc_np_RETURNDATACOPY = let
  val _ = print "  RETURNDATACOPY\n"
  val concl_tm = subst [``opc:opcode`` |-> ``RETURNDATACOPY``] clone_np_concl
in prove(gen_all concl_tm,
  rpt strip_tac >>
  simp[lookup_sib "RETURNDATACOPY", clone_inst_opcode, clone_instruction_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac eval_operand_clone_np_some >> gvs[] >>
  (* RETURNDATACOPY has if-branch on vs_returndata length — shared field *)
  (SUBGOAL_THEN ``s_callee.vs_returndata = s_clone.vs_returndata``
    ASSUME_TAC >- fs[clone_rel_np_def, shared_globals_np_def]) >>
  gvs[] >>
  mem_write_close_tac)
end;
val sbc_np_DLOADBYTES = mk_copy_np "DLOADBYTES" ``DLOADBYTES`` mem_write_close_tac;

(* --- Ext call opcodes as Theorems (not ML prove) --- *)
(* Shared ext call proof structure: setup >> SIB >> destruct >> eval >> bridge >> drule *)
Theorem sbc_np_CALL_thm[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    inst.inst_opcode = CALL /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            OK sc' /\ clone_rel_np prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Halt sc' /\ shared_globals_np sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Abort a sc' /\ shared_globals_np sc sc'
    | _ => T
Proof
  rpt strip_tac >> call_ctx_eq >>
  simp[lookup_sib "CALL", clone_inst_opcode, clone_inst_operands] >>
  destruct_7 >> seq_eval_7 >>
  irule ext_call_np_lift >>
  conj_tac >- (irule exec_ext_call_ok_or_error) >>
  drule (mono256 exec_ext_call_clone_np) >>
  disch_then (qspecl_then [`inst`, `x`, `x'`, `x''`, `x'3'`, `x'4'`, `x'5'`, `x'6'`,
    `s_clone.vs_call_ctx.cc_static`] mp_tac) >>
  simp[]
QED

Theorem sbc_np_STATICCALL_thm[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    inst.inst_opcode = STATICCALL /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            OK sc' /\ clone_rel_np prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Halt sc' /\ shared_globals_np sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Abort a sc' /\ shared_globals_np sc sc'
    | _ => T
Proof
  rpt strip_tac >> call_ctx_eq >>
  simp[lookup_sib "STATICCALL", clone_inst_opcode, clone_inst_operands] >>
  destruct_6 >> seq_eval_6 >>
  irule ext_call_np_lift >>
  conj_tac >- (irule exec_ext_call_ok_or_error) >>
  drule (mono256 exec_ext_call_clone_np) >>
  disch_then (qspecl_then [`inst`, `x`, `x'`, `0w`, `x''`, `x'3'`, `x'4'`, `x'5'`,
    `T`] mp_tac) >>
  simp[]
QED

Theorem sbc_np_DELEGATECALL_thm[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    inst.inst_opcode = DELEGATECALL /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            OK sc' /\ clone_rel_np prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Halt sc' /\ shared_globals_np sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Abort a sc' /\ shared_globals_np sc sc'
    | _ => T
Proof
  rpt strip_tac >> call_ctx_eq >> accts_eq >>
  simp[lookup_sib "DELEGATECALL", clone_inst_opcode, clone_inst_operands] >>
  destruct_6 >> seq_eval_6 >>
  irule ext_call_np_lift >>
  conj_tac >- (irule exec_delegatecall_ok_or_error) >>
  drule (mono256 exec_delegatecall_clone_np) >>
  disch_then (qspecl_then [`inst`, `x`, `x'`, `x''`, `x'3'`, `x'4'`, `x'5'`] mp_tac) >>
  simp[]
QED

Theorem sbc_np_CREATE_thm[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    inst.inst_opcode = CREATE /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            OK sc' /\ clone_rel_np prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Halt sc' /\ shared_globals_np sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Abort a sc' /\ shared_globals_np sc sc'
    | _ => T
Proof
  rpt strip_tac >> call_ctx_eq >> accts_eq >>
  simp[lookup_sib "CREATE", clone_inst_opcode, clone_inst_operands] >>
  destruct_3 >> seq_eval_3 >>
  irule ext_call_np_lift >>
  conj_tac >- (irule exec_create_ok_or_error) >>
  drule (mono256 exec_create_clone_np) >>
  disch_then (qspecl_then [`inst`, `x`, `x'`, `x''`, `NONE:256 word option`] mp_tac) >>
  simp[]
QED

Theorem sbc_np_CREATE2_thm[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    inst.inst_opcode = CREATE2 /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            OK sc' /\ clone_rel_np prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Halt sc' /\ shared_globals_np sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
            Abort a sc' /\ shared_globals_np sc sc'
    | _ => T
Proof
  rpt strip_tac >> call_ctx_eq >> accts_eq >>
  simp[lookup_sib "CREATE2", clone_inst_opcode, clone_inst_operands] >>
  destruct_4 >> seq_eval_4 >>
  irule ext_call_np_lift >>
  conj_tac >- (irule exec_create_ok_or_error) >>
  drule (mono256 exec_create_clone_np) >>
  disch_then (qspecl_then [`inst`, `x`, `x'`, `x''`, `SOME (x'3':256 word)`] mp_tac) >>
  simp[]
QED

val _ = print "Per-opcode clone_np theorems generated.\n";

(* ================================================================
   Combiner: step_inst_base_clone_np
   ================================================================ *)

(* Collect all per-opcode theorems: special + category + ext calls *)
val sbc_np_thms = [
  sbc_np_NOP, sbc_np_ASSIGN, sbc_np_PHI,
  sbc_np_JMP, sbc_np_JNZ, sbc_np_DJMP,
  sbc_np_ASSERT, sbc_np_ASSERT_UNREACHABLE,
  sbc_np_STOP, sbc_np_SINK, sbc_np_INVALID,
  sbc_np_RETURN, sbc_np_REVERT, sbc_np_SELFDESTRUCT,
  sbc_np_LOG, sbc_np_SHA3,
  sbc_np_CALL_thm, sbc_np_STATICCALL_thm, sbc_np_DELEGATECALL_thm,
  sbc_np_CREATE_thm, sbc_np_CREATE2_thm,
  sbc_np_MCOPY, sbc_np_CALLDATACOPY, sbc_np_CODECOPY,
  sbc_np_EXTCODECOPY, sbc_np_RETURNDATACOPY,
  sbc_np_ISTORE, sbc_np_DLOADBYTES
] @ sbc_np_category;

Theorem step_inst_base_clone_np:
  !prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> PARAM /\ inst.inst_opcode <> RET /\
    inst.inst_opcode <> ALLOCA /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc =>
        ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
              OK sc' /\ clone_rel_np prefix labels sc sc'
    | Halt sc =>
        ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
              Halt sc' /\ shared_globals_np sc sc'
    | Abort a sc =>
        ?sc'. step_inst_base (clone_instruction prefix labels inst) s_clone =
              Abort a sc' /\ shared_globals_np sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  FIRST_PROVE (
    map (fn th => (mp_tac (SPEC_ALL th) >> (impl_tac >- simp[]) >> simp[]))
      sbc_np_thms
  )
QED

(* ================================================================
   General result_equiv reflexivity and transitivity
   ================================================================ *)

Theorem result_equiv_refl:
  !excl r. result_equiv excl r r
Proof
  gen_tac >> Cases >> simp[result_equiv_def, state_equiv_refl, execution_equiv_refl]
QED

Theorem result_equiv_trans:
  !excl r1 r2 r3.
    result_equiv excl r1 r2 /\ result_equiv excl r2 r3 ==>
    result_equiv excl r1 r3
Proof
  gen_tac >> Cases >> Cases >> Cases >>
  simp[result_equiv_def] >>
  metis_tac[state_equiv_trans, execution_equiv_trans]
QED

val _ = export_theory();
