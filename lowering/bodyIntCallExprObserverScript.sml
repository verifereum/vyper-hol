Theory bodyIntCallExprObserver
Ancestors
  abiEncoderObserver bodyIntCallObserverFrame fragExec compileEnv
  venomInst venomExecSemantics venomExecProofs list rich_list

(* One package definition keeps completed-block ordering and the appended
   STOP identical in all containment, lookup and later region certificates.
   Unrelated function metadata is retained from a supplied template. *)
Definition expr_stop_function_def:
  expr_stop_function sa sb id template = template with fn_blocks :=
    <| bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []] |> ::
    emitted_blocks sa sb
End

Theorem expr_stop_function_lookup:
  lookup_block sb.cs_current_bb (expr_stop_function sa sb id template).fn_blocks =
    SOME <| bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []] |>
Proof
  simp[expr_stop_function_def, lookup_block_def, FIND_thm]
QED

Theorem expr_stop_function_stop:
  ?bb. lookup_block sb.cs_current_bb (expr_stop_function sa sb id template).fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sb.cs_current_insts) = SOME (mk_inst id STOP [] [])
Proof
  simp[expr_stop_function_lookup, get_instruction_def, EL_APPEND_EQN]
QED

Theorem expr_stop_function_has_code:
  ALL_DISTINCT (sb.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) ==>
  fn_has_code sa sb (expr_stop_function sa sb id template)
Proof
  strip_tac >> rw[fn_has_code_def]
  >- (irule MEM_lookup_block >>
      simp[expr_stop_function_def]) >>
  simp[expr_stop_function_lookup, IS_PREFIX_APPEND]
QED

Theorem expr_stop_function_empty:
  fn_has_code sa sa (expr_stop_function sa sa id template)
Proof
  irule expr_stop_function_has_code >> simp[emitted_blocks_def]
QED

Theorem expr_stop_function_same_block:
  sa.cs_current_bb = sb.cs_current_bb /\ emitted_blocks sa sb = [] ==>
  fn_has_code sa sb (expr_stop_function sa sb id template)
Proof
  strip_tac >> irule expr_stop_function_has_code >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "STOP packaging has unproved dependencies"
  end) [expr_stop_function_lookup, expr_stop_function_stop,
        expr_stop_function_has_code, expr_stop_function_empty,
        expr_stop_function_same_block];
