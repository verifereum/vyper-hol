(*
 * Per-opcode clauses of step_inst_base, built without the simplifier.
 *
 * step_inst_base is one case over every opcode.  simp[step_inst_base_def]
 * simplifies all of its arms before it reduces the case (~0.3 s a call);
 * rewriting the case to the known opcode's arm first takes ~0.01 s.
 *
 * TOP-LEVEL:
 *   opcode_clause OPC
 *     |- !inst s. inst.inst_opcode = OPC ==> step_inst_base inst s = <arm>
 *   STEP_INST_BASE_OPCODE_CONV
 *     ``step_inst_base i s`` |-> |- step_inst_base i s = <arm>, for an i
 *     whose opcode srw_ss() reduces to a constructor, such as
 *     ``inst with inst_opcode := OPC``.
 *   STEP_INST_BASE_OPCODE_TAC
 *     Rewrites each step_inst_base i s in the goal that
 *     STEP_INST_BASE_OPCODE_CONV can, e.g. i = ``mk_inst id OPC ops outs``.
 *   with_opcode_clause k
 *     Runs k [opcode_clause OPC] for an assumption x.inst_opcode = OPC,
 *     e.g. after Cases_on `inst.inst_opcode`.  The simplifier discharges
 *     the clause's condition from that assumption and, unlike a rewrite
 *     with the assumption itself, keeps it for later steps.
 *     Use it in place of the step_inst_base_def argument:
 *       fs[step_inst_base_def]       ~>  with_opcode_clause fs
 *       gvs[step_inst_base_def, ths] ~>  with_opcode_clause (fn c => gvs (c @ ths))
 *)
structure stepInstBaseLib :> sig
  val opcode_clause : Term.term -> Thm.thm
  val STEP_INST_BASE_OPCODE_CONV : Conv.conv
  val STEP_INST_BASE_OPCODE_TAC : Abbrev.tactic
  val with_opcode_clause : (Thm.thm list -> Abbrev.tactic) -> Abbrev.tactic
end = struct

open HolKernel boolLib bossLib
open venomInstTheory venomExecSemanticsTheory

val ERR = mk_HOL_ERR "stepInstBaseLib"

val inst_var = mk_var ("inst", ``:instruction``)
val s_var = mk_var ("s", ``:venom_state``)
val opcode_of_tm = ``instruction_inst_opcode``

val expanded = PURE_ONCE_REWRITE_CONV [step_inst_base_def]
  (list_mk_comb (``step_inst_base``, [inst_var, s_var]))

fun build_clause opc = let
  val eq = ASSUME (mk_eq (mk_comb (opcode_of_tm, inst_var), opc))
  val arm = CONV_RULE (RAND_CONV (REWRITE_CONV [opcode_case_def]))
    (SUBS [eq] expanded)
in GENL [inst_var, s_var] (DISCH (concl eq) arm) end

(* Clauses built so far, by constructor name: a proof that splits on the
   opcode asks for the same clause once per use of its per-case tactic. *)
val clauses : (string * thm) list ref = ref []

fun opcode_clause opc =
  if not (TypeBase.is_constructor opc andalso type_of opc = ``:opcode``) then
    raise ERR "opcode_clause"
      ("expected an opcode constructor, got " ^ term_to_string opc)
  else let
    val name = fst (dest_const opc)
  in
    case Lib.assoc1 name (!clauses) of
      SOME (_, th) => th
    | NONE => let val th = build_clause opc
              in clauses := (name, th) :: !clauses; th end
  end

fun STEP_INST_BASE_OPCODE_CONV tm = let
  val (f, args) = strip_comb tm
  val _ = same_const f ``step_inst_base`` andalso length args = 2 orelse
    raise ERR "STEP_INST_BASE_OPCODE_CONV"
      ("expected step_inst_base i s, got " ^ term_to_string tm)
  val i = hd args
  val opc_eq = QCONV (SIMP_CONV (srw_ss()) []) (mk_comb (opcode_of_tm, i))
in MP (SPECL args (opcode_clause (rhs (concl opc_eq)))) opc_eq end

val STEP_INST_BASE_OPCODE_TAC = CONV_TAC (DEPTH_CONV STEP_INST_BASE_OPCODE_CONV)

fun opcode_of_eq th = let
  val (l, r) = dest_eq (concl th)
in
  if same_const (rator l) opcode_of_tm andalso TypeBase.is_constructor r
  then SOME r else NONE
end handle HOL_ERR _ => NONE

fun with_opcode_clause k = first_assum (fn eq =>
  case opcode_of_eq eq of
    SOME opc => k [opcode_clause opc]
  | NONE => NO_TAC)

end
