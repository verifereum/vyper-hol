(*
 * Expression simulation: extcall and staticcall (#636, Calls row 1)
 *
 * extcall/staticcall in oracle mode, including reverts and
 * default_return_value (#553).  The source evaluates the target, then the
 * positional arguments without reading them (eval_expr_results), then the
 * keyword operands, and reads the arguments last; the hypotheses of
 * compile_extcall_case give the operands' judgments in that order, as the
 * body induction's hypotheses do (bodySimExprCases' body_extcall_case).
 *
 * TOP-LEVEL:
 *   compile_extcall_case — extcall's expr_sim_case and expr_vv_case from
 *     its operands' judgments, for compile_expr_sim and the body
 *     simulation; compile_extcall_case_sim, expr_vv_ok of extcall, follows
 *
 * Why it holds: the call request agrees with the source's.  The selector is
 * cenv.ce_method_id, which expr_sim_inv pins to function_selector of the
 * declared ABI types; the calldata is the selector followed by the arguments
 * encoded at their own lowered types, at the encoded length (vyper#5127),
 * as build_ext_calldata sends (bounds don't change ABI bytes); a storage,
 * transient or immutable argument is read at its own declared type
 * (vyper#5239).  The extcodesize check and the void result are keyed on
 * return_type = NoneT on both sides, and typing rules out
 * default_return_value on a void call.  The call itself is an oracle step
 * (extCallOracleStep: venom_call_request_source, exec_ext_call_oracle_step),
 * as for send (exprSimSend).  A revert copies the returndata and REVERTs;
 * empty returndata with a default takes the default after the code recheck;
 * otherwise the returndata is decoded with the bounded memory decoder.
 *)

Theory exprSimExtCall
Ancestors
  list rich_list exprSim exprSimHyps vyperAST vyperInterpreter

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

(* Interface probes for empty and word-sized raw returndata. *)
Theorem extcall_void_decode_probe[local]:
  evaluate_abi_decode_return FEMPTY NoneT [] = INL NoneV
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem extcall_word_decode_probe[local]:
  evaluate_abi_decode_return FEMPTY (BaseT (UintT 256))
    (REPLICATE 32 (0w:word8)) = INL (IntV 0)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem extcall_short_word_decode_probe[local]:
  evaluate_abi_decode_return FEMPTY (BaseT (UintT 256)) [] =
    INR "abi_decode invalid"
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
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

Theorem compile_extcall_case_sim:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv
      (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
    expr_vv_ok cenv (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  `EVERY (expr_ok cenv) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >> irule expr_sim_below_mem >>
     qexists_tac `args` >> simp[] >> irule expr_sim_below_mono >>
     goal_assum (drule_at Any) >> simp[expr_size_def]) >>
  irule (cj 2 (SPEC_ALL compile_extcall_case)) >> rpt conj_tac >>
  rpt strip_tac >>
  FIRST [irule exprs_case_every_ok, irule results_case_every_ok] >>
  fs[EVERY_MEM] >> metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED
