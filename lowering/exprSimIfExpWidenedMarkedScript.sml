Theory exprSimIfExpWidenedMarked
Ancestors
  exprSimIfExpWidenedArm exprSimAbiGasBridge exprSimHash
  loweringPosts exprLoweringProps compileEnv venomState venomExecSemantics

Theorem expr_post_returndata:
  expr_post ctx func ce cx e es sa sb s0 ee v op
    (s with vs_returndata := rd) <=>
  expr_post ctx func ce cx e es sa sb s0 ee v op s
Proof
  Cases_on `op` >> simp[expr_post_def, hash_returndata_state_rel, expr_val_rel_def,
    expr_val_at_def, expr_val_own_def, locals_kept_def,
    eval_operand_def, lookup_var_def, local_region_def]
QED

(* A raw compiler state need not keep its entry label fresh. *)
Theorem typed_adapter_entry_label_probe[local]:
  let sa = (ARB:compile_state) with
    <| cs_current_bb := "@typed_dyn_cond_0"; cs_current_insts := [];
       cs_blocks := []; cs_next_label := 0; cs_next_var := 0;
       cs_next_id := 0 |> in
  let sb = SND (compile_ifexp_arm
    ((ARB:compile_env) with ce_struct_fields := FEMPTY)
    (ArrayT (BaseT (UintT 256)) (Dynamic 2))
    (ArrayT (BaseT (UintT 8)) (Dynamic 1))
    (StackValue (ArrayT (BaseT (UintT 8)) (Dynamic 1)) (Lit 32w)) sa) in
  ~frag_gas_free sa sb
Proof
  EVAL_TAC
QED

(* Removing an old ALLOCA from an observer does not preserve local backing. *)
Theorem local_backed_observer_loss_probe[local]:
  let s = (ARB:venom_state) with
      vs_allocas := FEMPTY |+ (0, (0,32)) in
  let fn = (ARB:ir_function) with fn_blocks :=
      [<|bb_label := "entry";
         bb_instructions := [mk_inst 0 ALLOCA [Lit 32w] ["p"]]|>] in
  let observer = fn with fn_blocks := [] in
  local_backed fn "p" s 0 32 /\
  ~local_backed observer "p" s 0 32
Proof
  EVAL_TAC >> simp[]
QED
