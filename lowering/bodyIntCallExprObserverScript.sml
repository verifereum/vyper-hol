Theory bodyIntCallExprObserver
Ancestors
  abiEncoderObserver bodyIntCallObserverFrame fragExec compileEnv
  venomInst venomExecSemantics venomExecProofs venomInstProofs venomWf list rich_list

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

(* This certificate mentions only static instruction successors. Jump entry is
   after the target's PHIs, whereas a sequential edge retains the block. *)
Theorem syntactic_region_closed:
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    inst_wf inst /\
    (~is_terminator inst.inst_opcode ==> (lbl,SUC idx) IN R) /\
    (!dest target. is_terminator inst.inst_opcode /\
      MEM dest (get_successors inst) /\
      lookup_block dest fn.fn_blocks = SOME target ==>
      (dest,phi_prefix_length target.bb_instructions) IN R)) ==>
  observer_region_closed ctx fn cut R
Proof
  strip_tac >> rw[observer_region_closed_def, abi_observer_step_def] >>
  qpat_assum `!lbl idx bb inst. _` (drule_all_then strip_assume_tac)
  >- (drule_all step_preserves_control_flow >> strip_tac >> simp[]) >>
  `step_inst_base inst s = OK middle` by gvs[step_inst_non_invoke] >>
  drule_all step_inst_base_term_succs >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem expr_stop_function_region_safe:
  (!lbl idx bb inst.
    (lbl,idx) IN R /\
    (lbl,idx) <> (sb.cs_current_bb,LENGTH sb.cs_current_insts) /\
    lookup_block lbl (expr_stop_function sa sb id template).fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    inst.inst_opcode <> INVOKE /\
    (!s h. ~s.vs_halted ==> step_inst_base inst s <> Halt h) /\
    (!s middle. ~s.vs_halted /\ step_inst_base inst s = OK middle ==>
      ~middle.vs_halted)) ==>
  observer_region_safe (expr_stop_function sa sb id template)
    (sb.cs_current_bb,LENGTH sb.cs_current_insts) R
Proof
  strip_tac >> simp[observer_region_safe_def] >> conj_tac
  >- (simp[expr_stop_function_lookup, get_instruction_def, EL_APPEND_EQN] >>
      qexists_tac `id` >> simp[]) >>
  first_x_assum mp_tac >> simp[]
QED

(* The same syntactic opcode inventory can supply the frame premise without
   restricting any instruction in the old prefix or outside the region. *)
Theorem syntactic_region_readonly:
  EVERY readonly_opcode ops /\
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    MEM inst.inst_opcode ops) ==>
  (!lbl idx bb inst.
    (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==>
    readonly_opcode inst.inst_opcode)
Proof
  simp[EVERY_MEM] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Syntactic region certificate has unproved dependencies"
  end) [syntactic_region_closed, expr_stop_function_region_safe,
        syntactic_region_readonly];
