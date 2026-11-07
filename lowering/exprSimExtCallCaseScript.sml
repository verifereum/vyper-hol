(*
 * Expression simulation: extcall and staticcall, as one case lemma
 *
 * extcall/staticcall in SOME oracle mode, including reverts and
 * default_return_value (#553).  The source evaluates the target, then the
 * positional arguments without reading them (eval_expr_results), then the
 * keyword operands, and reads the arguments last; the hypotheses of
 * compile_extcall_case give the operands' judgments in that order, as the
 * body induction's hypotheses do (bodySimCallCases's body_extcall_case).
 * exprSimCallExtcall and bodySimCallExtcall derive the two piece theorems
 * from it.
 *
 * TOP-LEVEL:
 *   compile_extcall_case — extcall's expr_sim_case and expr_vv_case from
 *     its operands' judgments
 *
 * Why it holds: the call request agrees with the source's.  The selector is
 * cenv.ce_method_id, which expr_sim_inv pins to function_selector of the
 * declared ABI types; the calldata is the selector followed by the arguments
 * encoded at their own lowered types, at the encoded length (vyper#5127),
 * as build_ext_calldata sends; a storage, transient or immutable argument is
 * read at its own declared type (vyper#5239).  The extcodesize check and the
 * void result are keyed on return_type = NoneT on both sides, and typing
 * rules out default_return_value on a void call.  The call itself is an
 * oracle step (extCallOracleStep: venom_call_request_source,
 * exec_ext_call_oracle_step), as for send (exprSimSend).  A revert copies
 * the returndata and REVERTs; empty returndata with a default takes the
 * default after the code recheck; otherwise the returndata is decoded with
 * the bounded memory decoder.
 *)

Theory exprSimExtCallCase
Ancestors
  list rich_list loweringPosts supportedExprTraverse exprSimHypsDefs exprSimHyps vyperAST
  vyperInterpreter

(* A storage or transient pointer an effect-free operand leaves reads live
   slots at es': no byte of the slots it reads is dead but those its own
   type leaves dead (storage_read_live). *)
Theorem vv_post_storage_live:
  !ctx func cenv cx e es sa sb s0 es' tv vv s t p w tvt.
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ~expr_has_effect e /\
    vv = LocatedValue t p /\
    eval_operand p.ptr_operand s = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tvt ==>
    (p.ptr_location = LocStorage ==>
     storage_read_live cx F (get_storage cx es' F) w tvt) /\
    (p.ptr_location = LocTransient ==>
     storage_read_live cx T (get_storage cx es' T) w tvt)
Proof
  rpt strip_tac >> gvs[vv_post_def] >> metis_tac[]
QED

(* Source boundary: positional locations are read only after kwargs. *)
Theorem eval_extcall_stages:
  eval_expr cx (Call ann (ExtCall static skip sig opts) args dflt) =
    do target <- eval_exprs cx (TAKE 1 args);
       results <- eval_expr_results cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args));
       kwargs <- eval_exprs cx (DROP (1 + LENGTH (FST (SND sig))) args);
       vs <- read_results cx results;
       eval_ext_call cx static skip sig opts (target ++ vs ++ kwargs)
    od
Proof
  simp[Once evaluate_def]
QED

Theorem compile_extcall_case:
  !nocalls ctx func cenv cx ann is_static skip sig opts args dflt.
    exprs_case nocalls ctx func cenv cx (TAKE 1 args) /\
    (!s target t.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) ==>
       results_case nocalls ctx func cenv cx
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 args))) /\
    (!s target t s' results t'.
       eval_exprs cx (TAKE 1 args) s = (INL target, t) /\
       eval_expr_results cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 args)) s' =
         (INL results, t') ==>
       exprs_case nocalls ctx func cenv cx
         (DROP (1 + LENGTH (FST (SND sig))) args)) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx
      (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  cheat
QED
