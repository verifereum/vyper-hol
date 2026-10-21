(*
 * Per-opcode clauses of step_inst_base, from step_inst_base_opcode_eqs.
 *
 * step_inst_base is one case over every opcode.  simp[step_inst_base_def]
 * simplifies all of its arms before it reduces the case; rewriting the case
 * to the known opcode's arm first avoids that.
 *
 * TOP-LEVEL:
 *   opcode_clause OPC
 *     |- !inst s. inst.inst_opcode = OPC ==> step_inst_base inst s = <arm>
 *   simp_opcode_clause OPC
 *     opcode_clause OPC with its arm simplified by srw_ss().
 *   STEP_INST_BASE_OPCODE_SIMP_CONV
 *     ``step_inst_base i s`` |-> |- step_inst_base i s = <arm>, with the arm
 *     simplified by srw_ss(), for an i whose opcode srw_ss() reduces to a
 *     constructor, such as ``inst with inst_opcode := OPC``.
 *   with_opcode_clause k
 *     Runs k on the clauses for every assumption x.inst_opcode = OPC,
 *     e.g. after Cases_on `inst.inst_opcode`; fails if there is none.  The
 *     simplifier discharges each clause's condition from its assumption and,
 *     unlike a rewrite with the assumption itself, keeps it for later steps.
 *     Use it in place of the step_inst_base_def argument:
 *       fs[step_inst_base_def]       ~>  with_opcode_clause fs
 *       gvs[step_inst_base_def, ths] ~>  with_opcode_clause (fn c => gvs (c @ ths))
 *)
structure stepInstBaseLib :> sig
  val opcode_clause : Term.term -> Thm.thm
  val simp_opcode_clause : Term.term -> Thm.thm
  val STEP_INST_BASE_OPCODE_SIMP_CONV : Conv.conv
  val with_opcode_clause : (Thm.thm list -> Abbrev.tactic) -> Abbrev.tactic
end = struct

open HolKernel boolLib bossLib
open venomInstTheory venomExecSemanticsTheory

val ERR = mk_HOL_ERR "stepInstBaseLib"

val inst_var = mk_var ("inst", ``:instruction``)
val s_var = mk_var ("s", ``:venom_state``)
val opcode_of_tm = ``instruction_inst_opcode``

fun clause_opcode th = rhs (fst (dest_imp (concl th)))

(* Requantified over inst_var and s_var in that order, which
   STEP_INST_BASE_OPCODE_CONV specializes. *)
val clauses = map (fn th => let val th' = SPEC_ALL th
                            in (clause_opcode th', GENL [inst_var, s_var] th') end)
  (CONJUNCTS step_inst_base_opcode_eqs)

fun opcode_clause opc =
  case List.find (fn (k, _) => aconv k opc) clauses of
    SOME (_, th) => th
  | NONE => raise ERR "opcode_clause"
      ("expected an opcode constructor, got " ^ term_to_string opc)

fun STEP_INST_BASE_OPCODE_CONV tm = let
  val (f, args) = strip_comb tm
  val _ = same_const f ``step_inst_base`` andalso length args = 2 orelse
    raise ERR "STEP_INST_BASE_OPCODE_CONV"
      ("expected step_inst_base i s, got " ^ term_to_string tm)
  val i = hd args
  val opc_eq = QCONV (SIMP_CONV (srw_ss()) []) (mk_comb (opcode_of_tm, i))
in MP (SPECL args (opcode_clause (rhs (concl opc_eq)))) opc_eq end

val SIMP_ARM_CONV = RAND_CONV (QCONV (SIMP_CONV (srw_ss()) []))

fun simp_opcode_clause opc =
  CONV_RULE (STRIP_QUANT_CONV (RAND_CONV SIMP_ARM_CONV)) (opcode_clause opc)

val STEP_INST_BASE_OPCODE_SIMP_CONV =
  STEP_INST_BASE_OPCODE_CONV THENC SIMP_ARM_CONV

fun opcode_of_eq tm = let
  val (l, r) = dest_eq tm
in
  if same_const (rator l) opcode_of_tm andalso TypeBase.is_constructor r
  then SOME r else NONE
end handle HOL_ERR _ => NONE

(* Every opcode assumption, not the first: with two of them, the first may
   belong to another instruction, and k (usually simp) would succeed without
   the clause the goal needs. *)
fun with_opcode_clause k (asl, g) = let
  val opcs = op_mk_set aconv (List.mapPartial opcode_of_eq asl)
in
  if null opcs then raise ERR "with_opcode_clause" "no opcode assumption"
  else k (map opcode_clause opcs) (asl, g)
end

end
