(*
 * Tactics for chaining emit_op fragments (lowering proofs)
 *
 * elim_lit, forward_all_evals, collapse_run and chain_step: the steps of a
 * proof that runs a sequence of emit_op / emit_void instructions to its
 * result, shared by arithmeticProps and exprSimArrayIndex.
 *)
structure emitTacticsLib =
struct

open HolKernel boolLib bossLib
open emitHelperPropsTheory exprLoweringPropsTheory

(* elim_lit n th: For emit_op_X_correct theorems, specialize the n-th operand
   (1-indexed) to be a Lit, eliminating its eval_operand conjunct.
   This allows drule_all to work without needing eval_operand (Lit w) ss
   as an explicit assumption.
   Example: elim_lit 2 emit_op_SLT_correct — SLT with Lit second arg *)
fun elim_lit n th =
  let
    val (vars, _) = strip_forall (concl th)
    val op_var = List.nth (vars, n-1)
    val v_var = List.nth (vars, n+1)
    val lit_const = prim_mk_const{Name="Lit",Thy="venomState"}
  in
    th |> SPEC_ALL
       |> INST [op_var |-> mk_comb(lit_const, v_var)]
       |> SIMP_RULE (srw_ss()) [eval_operand_lit]
       |> GENL (List.filter (fn v => not (aconv v op_var)) vars)
  end;

(* forward_all_evals: For each preservation fact
     ∀op w. eval_operand op ss_old = SOME w ⇒ eval_operand op ss_new = SOME w
   in the assumptions (from oldest to newest), apply it to all matching
   eval_operand facts and add the forwarded versions. Multiple passes
   ensure transitive forwarding through chains of states. *)
fun forward_all_evals (asl, g) : Context.t -> goal list * validation =
  let
    fun is_pres t =
      (let val (vs, body) = strip_forall t
       in length vs = 2 andalso is_imp body andalso
          let val (ant, _) = dest_imp body
              val (lhs_t, _) = dest_eq ant
              val (f, _) = strip_comb lhs_t
          in fst (dest_const f) = "eval_operand"
          end
       end) handle _ => false
    fun is_eval t =
      (not (is_forall t) andalso
       let val (lhs_t, rhs_t) = dest_eq t
           val (f, _) = strip_comb lhs_t
           val (some_c, _) = dest_comb rhs_t
       in fst (dest_const f) = "eval_operand" andalso
          fst (dest_const some_c) = "SOME"
       end) handle _ => false
    (* Process oldest preservation facts first for transitive forwarding *)
    val pres_list = rev (List.filter is_pres asl)
    fun apply_one_pres pres_t (asl', g') =
      let val pres_th = ASSUME pres_t
          val evals = List.filter is_eval asl'
          fun forward_one eval_t (asl'', g'') =
            (let val new_th = MATCH_MP (SPEC_ALL pres_th) (ASSUME eval_t)
                 val new_concl = concl new_th
             in if List.exists (aconv new_concl) asl''
                then ALL_TAC (asl'', g'')
                else assume_tac new_th (asl'', g'')
             end handle _ => ALL_TAC (asl'', g''))
      in EVERY (map forward_one evals) (asl', g')
      end
  in
    EVERY (map apply_one_pres pres_list) (asl, g)
  end;

(* collapse_run: given thm `A = B`, find assumption `B = OK s`, produce `A = OK s` *)
fun collapse_run (eq_th : thm) : tactic = fn (asl, g) =>
  let val rhs_tm = rhs (concl eq_th)
      fun matches_rhs a =
        (aconv (lhs (concl (ASSUME a))) rhs_tm) handle _ => false
  in case List.find matches_rhs asl of
       SOME a_str => assume_tac (TRANS eq_th (ASSUME a_str)) (asl, g)
     | NONE => raise mk_HOL_ERR "collapse_run" "collapse_run" "no matching run"
  end;

(* chain_step th: Forward all eval_operand preservation facts, apply an
   emit_op_*_correct theorem via drule_all, then chain with existing
   run_inst_seq prefix via imp_res_tac emit_op_extends + run_inst_seq_chain.
   Uses collapse_run instead of asm_rewrite_tac[] to avoid APPEND looping. *)
fun chain_step th : tactic =
  forward_all_evals >>
  drule_all th >> strip_tac >>
  TRY (imp_res_tac emit_op_extends >>
       drule_all run_inst_seq_chain >> strip_tac >>
       qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run);

end
