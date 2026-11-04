(* Scratch: tail_merge is the identity on a wf function with two
   identical halting blocks; it merges only when inst_ids repeat. *)
Theory tmNoopWitness
Ancestors
  tailMergeDefs cfgTransform venomWf venomInst

Definition tw_inst_def:
  tw_inst id op args outs =
    <| inst_id := id; inst_opcode := op; inst_operands := args;
       inst_outputs := outs |>
End

Definition tw_fn_def:
  tw_fn bid =
    (ARB:ir_function) with fn_blocks :=
      [<| bb_label := "entry";
          bb_instructions :=
            [tw_inst 0 JNZ [Lit 1w; Label "a"; Label "b"] []] |>;
       <| bb_label := "a"; bb_instructions := [tw_inst 1 STOP [] []] |>;
       <| bb_label := "b"; bb_instructions := [tw_inst bid STOP [] []] |>]
End

Theorem tw_self_contained[local]:
  EVERY (\i. i.inst_opcode <> PHI /\ i.inst_operands = []) bb.bb_instructions ==>
  bb_self_contained bb
Proof
  rw[bb_self_contained_def, listTheory.EVERY_EL] >> gvs[]
QED

Theorem tw_reach[local]:
  reachable (tw_fn n) "a" /\ reachable (tw_fn n) "b"
Proof
  rw[reachable_def] >> qexists_tac `"entry"` >>
  (conj_tac >- EVAL_TAC) >>
  irule relationTheory.RTC_SINGLE >>
  simp[fn_succ_def,
       Once (EVAL ``lookup_block "entry" (tw_fn n).fn_blocks``)] >>
  EVAL_TAC
QED

val tw_conv = computeLib.RESTR_EVAL_CONV [``bb_self_contained``, ``reachable``];
val tw_reach_n = CONV_RULE tw_conv tw_reach;

Theorem tail_merge_noop_on_wf_witness:
  wf_function (tw_fn 2) /\ tail_merge_fn (tw_fn 2) = tw_fn 2
Proof
  CONV_TAC tw_conv >> simp[tw_self_contained, tw_reach_n] >> EVAL_TAC
QED

Theorem tail_merge_merges_only_dup_ids:
  ~wf_function (tw_fn 1) /\ LENGTH (tail_merge_fn (tw_fn 1)).fn_blocks = 2
Proof
  CONV_TAC tw_conv >> simp[tw_self_contained, tw_reach_n] >> EVAL_TAC
QED
