(* Term syntax for the fixed outer cut.  These are ML values, not HOL
   constants: composing phases need not change the enclosing observer. *)
structure bodyFullAbiDecodeCutPathLib =
struct
open HolKernel boolLib bossLib
open compileEnvTheory venomStateTheory venomExecSemanticsTheory
     abiEncoderObserverTheory exprSimAbiGasBridgeTheory relationTheory

(* The two incarnations of an entry label are distinguished by block
   history, not by comparing the numeric or textual labels. *)
val shadow_cursor = ``\L start x.
  (if x.cs_blocks = start.cs_blocks then L else x.cs_current_bb,
   LENGTH x.cs_current_insts)``;

val shadow_path = ``\ctx obs cut. RTC (abi_observer_step ctx obs cut)``;

(* Arguments: fixed observer and cut, relabelling, shadow input, phase
   endpoint cursor, and the original outcome already selected by the post. *)
val shadow_result = ``\ctx obs cut L entry u cursor r.
  (?v w. r = OK v /\ ~w.vs_halted /\
         (w.vs_current_bb,w.vs_inst_idx) = cursor /\
         frag_relabel_state L entry w v /\ (^shadow_path) ctx obs cut u w) \/
  (?v w k. r = Abort Revert_abort v /\ frag_relabel_state L entry w v /\
           run_from k ctx obs u = Abort Revert_abort w)``;

(* Extend ?r Gf tnf. Q by a certificate abstracted over r.  Freshen all
   three binders against the certificate so unrelated free variables in it
   stay free.  Projecting out the new conjunct must give exactly the old post
   modulo alpha and beta conversion. *)
fun extend_post post cert =
  let
    val beta = rhs o concl o QCONV (REDEPTH_CONV BETA_CONV)
    val (old, body) = strip_exists (beta post)
    val _ = if length old = 3 then () else
              raise Fail "CutPath.extend_post: expected outcome and two ghosts"
    fun fresh [] _ = []
      | fresh (v::vs) avoid =
          let val v' = variant avoid v
          in v' :: fresh vs (v' :: avoid) end
    val vars = fresh old (old @ free_vars post @ free_vars cert)
    val core = subst (ListPair.mapEq (op |->) (old, vars)) body
    val extra = rhs (concl (BETA_CONV (mk_comb (cert, hd vars))))
    val extended = list_mk_exists (vars, mk_conj (core, extra))
    val (binders, both) = strip_exists extended
    val projected = list_mk_exists (binders, fst (dest_conj both))
  in
    if aconv (beta projected) (beta post) then extended else
      raise Fail "CutPath.extend_post: projection changed the post"
  end
end
