(*
 * Function Inliner — Category Opcode Clone Theorems
 *
 * ML-generated per-opcode clone theorems for all 59 category opcodes
 * (pure2, pure1, pure3, read0, read1, write2).
 *
 * Optimization: step_inst_base reductions are pre-computed once (~30s total)
 * as conditional rewrites [inst.inst_opcode = OPC ==> step_inst_base inst ss = ...].
 * Each per-opcode theorem uses simp with the precomputed lemma (~0.7s each).
 *)

Theory functionInlinerCategory
Ancestors
  functionInlinerCloneSim functionInlinerDefs
  venomExecSemantics venomInst venomState stateEquiv

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory

open functionInlinerDefsTheory functionInlinerCloneSimTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     stateEquivTheory

(* lift_oe: weaken terminal case from clone_rel to shared_globals *)
val lift_oe = Q.prove(
  `(!a sc. f <> Abort a sc) /\ (!v sc. f <> IntRet v sc) /\
   (!sc. f <> Halt sc) /\
   (case f of
      OK sc => ?sc'. g = OK sc' /\ clone_rel p l sc sc'
    | Halt _ => T | Abort _ _ => T | IntRet _ _ => T
    | Error e => ?e'. g = Error e') ==>
   (case f of
      OK sc => ?sc'. g = OK sc' /\ clone_rel p l sc sc'
    | Halt sc => ?sc'. g = Halt sc' /\ shared_globals sc sc'
    | Abort a sc => ?sc'. g = Abort a sc' /\ shared_globals sc sc'
    | IntRet v sc => T
    | Error e => ?e'. g = Error e')`,
  Cases_on `f` >> simp[]);

(* Pre-compute conditional step_inst_base reductions.
   Form: inst.inst_opcode = OPC ==> step_inst_base inst ss = exec_catN op inst ss
   Works for both original and cloned instructions (via clone_inst_opcode). *)
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

(* Opcode name/term pairs by category *)
val opcode_names_p2 =
  [("ADD",``ADD``), ("SUB",``SUB``), ("MUL",``MUL``),
   ("Div",``Div``), ("Mod",``Mod``), ("SDIV",``SDIV``),
   ("SMOD",``SMOD``), ("Exp",``Exp``), ("EQ",``EQ``),
   ("LT",``LT``), ("GT",``GT``), ("SLT",``SLT``),
   ("SGT",``SGT``), ("AND",``AND``), ("OR",``OR``),
   ("XOR",``XOR``), ("SHL",``SHL``), ("SHR",``SHR``),
   ("SAR",``SAR``), ("SIGNEXTEND",``SIGNEXTEND``),
   ("BYTE",``BYTE``)];
val opcode_names_p1 = [("ISZERO",``ISZERO``), ("NOT",``NOT``)];
val opcode_names_p3 = [("ADDMOD",``ADDMOD``), ("MULMOD",``MULMOD``)];
val opcode_names_r0 =
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
val opcode_names_r1 =
  [("MLOAD",``MLOAD``), ("SLOAD",``SLOAD``), ("TLOAD",``TLOAD``),
   ("BLOCKHASH",``BLOCKHASH``), ("BLOBHASH",``BLOBHASH``),
   ("BALANCE",``BALANCE``), ("CALLDATALOAD",``CALLDATALOAD``),
   ("EXTCODESIZE",``EXTCODESIZE``), ("ILOAD",``ILOAD``),
   ("DLOAD",``DLOAD``), ("EXTCODEHASH",``EXTCODEHASH``)];
val opcode_names_w2 =
  [("MSTORE",``MSTORE``), ("MSTORE8",``MSTORE8``), ("SSTORE",``SSTORE``), ("TSTORE",``TSTORE``)];

val all_opcodes =
  opcode_names_p2 @ opcode_names_p1 @ opcode_names_p3 @
  opcode_names_r0 @ opcode_names_r1 @ opcode_names_w2;

val _ = print "Pre-computing step_inst_base reductions...\n";
val sib_table : (string * thm) list =
  map (fn (n,t) => let val _ = print ("  " ^ n ^ "\n")
                   in (n, mk_cond_sib t) end) all_opcodes;
val _ = print "Done.\n";

fun lookup_sib name =
  case List.find (fn (n,_) => n = name) sib_table of
    SOME (_,th) => th
  | NONE => raise Fail ("No precomputed sib for " ^ name);

(* --- ML theorem generator for category opcodes ---
   Proof structure:
   1. rpt strip_tac (get inst.inst_opcode = OPC and clone_rel in context)
   2. simp[sib_cond, clone_inst_opcode] (reduce both step_inst_base calls)
   3. irule lift_oe + prove impossibility goals + irule clone_thm *)

fun mk_sbc_thm opc sib_lemma clone_thm cat_def extra_tac =
  let val concl_tm =
    ``clone_rel prefix labels s_callee s_clone /\
      inst.inst_opcode = ^opc ==>
      (case step_inst_base inst s_callee of
         OK sc =>
           ?sc'. step_inst_base (clone_instruction prefix labels inst)
                   s_clone = OK sc' /\
                 clone_rel prefix labels sc sc'
       | Halt sc =>
           ?sc'. step_inst_base (clone_instruction prefix labels inst)
                   s_clone = Halt sc' /\
                 shared_globals sc sc'
       | Abort a sc =>
           ?sc'. step_inst_base (clone_instruction prefix labels inst)
                   s_clone = Abort a sc' /\
                 shared_globals sc sc'
       | IntRet v sc => T
       | Error e =>
           ?e'. step_inst_base (clone_instruction prefix labels inst)
                  s_clone = Error e')``
  in prove(gen_all concl_tm,
     rpt strip_tac >>
     simp[sib_lemma, clone_inst_opcode] >>
     irule lift_oe >>
     CONJ_TAC >- (simp[cat_def] >> BasicProvers.EVERY_CASE_TAC) >>
     CONJ_TAC >- (simp[cat_def] >> BasicProvers.EVERY_CASE_TAC) >>
     CONJ_TAC >- (simp[cat_def] >> BasicProvers.EVERY_CASE_TAC) >>
     irule clone_thm >> simp[] >> extra_tac)
  end;

(* Definitions needed to close shared_globals obligations *)
val sg_read_defs = [shared_globals_def, mload_def, sload_def, tload_def,
                    contract_storage_def, contract_transient_def];
val sg_write_defs = [clone_rel_def, shared_globals_def, mstore_def,
                     mstore8_def, sstore_def, tstore_def,
                     contract_storage_def, contract_transient_def, LET_THM];

(* Generate and save all 59 category-opcode clone theorems *)
local
  fun p2 (n,opc) = mk_sbc_thm opc (lookup_sib n)
                      exec_pure2_clone exec_pure2_def ALL_TAC
  fun p1 (n,opc) = mk_sbc_thm opc (lookup_sib n)
                      exec_pure1_clone exec_pure1_def ALL_TAC
  fun p3 (n,opc) = mk_sbc_thm opc (lookup_sib n)
                      exec_pure3_clone exec_pure3_def ALL_TAC
  fun r0 (n,opc) = mk_sbc_thm opc (lookup_sib n)
                      exec_read0_clone exec_read0_def (gvs sg_read_defs)
  fun r1 (n,opc) = mk_sbc_thm opc (lookup_sib n)
                      exec_read1_clone exec_read1_def (gvs sg_read_defs)
  fun w2 (n,opc) = mk_sbc_thm opc (lookup_sib n)
                      exec_write2_clone exec_write2_def
                      (rpt strip_tac >> gvs sg_write_defs)

  fun gen_and_save name gen pair =
    save_thm("sbc_" ^ name, gen pair)
in
  val category_thms =
    map (fn p as (n,_) => gen_and_save n p2 p) opcode_names_p2 @
    map (fn p as (n,_) => gen_and_save n p1 p) opcode_names_p1 @
    map (fn p as (n,_) => gen_and_save n p3 p) opcode_names_p3 @
    map (fn p as (n,_) => gen_and_save n r0 p) opcode_names_r0 @
    map (fn p as (n,_) => gen_and_save n r1 p) opcode_names_r1 @
    map (fn p as (n,_) => gen_and_save n w2 p) opcode_names_w2
end;

val _ = export_theory();
