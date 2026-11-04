(* SCRATCH: counterexamples to load_elim_function_correct as stated.
   Not for merging. *)
Theory loadElimCex
Ancestors
  loadElimDefs venomExecSemantics venomState venomWf basePtrDefs finite_map stateEquiv
Libs
  wordsLib

Definition mk_i_def:
  mk_i id op ops outs =
    <| inst_id := id; inst_opcode := op; inst_operands := ops;
       inst_outputs := outs |>
End

(* A: SSA, run started at block b (not the entry). a loads slot 0 into y,
   so the pass rewrites b's load to x = y; a run started at b never set y. *)
Definition cexA_fn_def:
  cexA_fn = mk_raw_function "f"
    [<| bb_label := "e";
        bb_instructions := [mk_i 1 JMP [Label "a"] []] |>;
     <| bb_label := "a";
        bb_instructions :=
          [mk_i 2 SLOAD [Lit 0w] ["y"];
           mk_i 3 JMP [Label "b"] []] |>;
     <| bb_label := "b";
        bb_instructions :=
          [mk_i 4 SLOAD [Lit 0w] ["x"];
           mk_i 5 JNZ [Var "x"; Label "c"; Label "d"] []] |>;
     <| bb_label := "c"; bb_instructions := [mk_i 6 STOP [] []] |>;
     <| bb_label := "d"; bb_instructions := [mk_i 7 INVALID [] []] |>]
End

(* B: not SSA, run started at the entry. v is redefined between the two
   loads, but the lattice still maps slot 0 to v. *)
Definition cexB_fn_def:
  cexB_fn = mk_raw_function "f"
    [<| bb_label := "e";
        bb_instructions :=
          [mk_i 1 SLOAD [Lit 0w] ["v"];
           mk_i 2 ADD [Lit 1w; Lit 1w] ["v"];
           mk_i 3 SLOAD [Lit 0w] ["x"];
           mk_i 4 JNZ [Var "x"; Label "c"; Label "d"] []] |>;
     <| bb_label := "c"; bb_instructions := [mk_i 5 STOP [] []] |>;
     <| bb_label := "d"; bb_instructions := [mk_i 6 INVALID [] []] |>]
End

Definition rd_def:
  rd r = case r of Halt _ => 1n | Abort _ _ => 2 | OK _ => 0 | IntRet _ _ => 3 | Error _ => 4
End

val _ = computeLib.del_consts
  [``memory_alias_analyze``, ``storage_alias_analyze``,
   ``transient_alias_analyze``];
val _ = computeLib.add_funs
  [finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FUN_FMAP_EMPTY];
(* The worklist's "changed" test compares a block's old and new boundary
   lattices; decide it when they are syntactically equal. *)
fun aconv_eq_conv tm =
  let val (l, r) = dest_eq tm in
    if aconv l r then EQT_INTRO (REFL l)
    else if null (free_vars l) andalso null (free_vars r) then
      let val th = (REWR_CONV fmap_EXT THENC EVAL) tm
          val rhs = boolSyntax.rhs (concl th) in
        if aconv rhs T orelse aconv rhs F then th else raise Conv.UNCHANGED
      end
    else raise Conv.UNCHANGED
  end;
val _ = computeLib.add_convs
  [(``$= : (load_key, operand list) fmap -> (load_key, operand list) fmap -> bool``,
    2, aconv_eq_conv)];

Theorem bp_ptr_sound_empty:
  !s. bp_ptr_sound FEMPTY s
Proof
  simp[bp_ptr_sound_def, bp_get_ptrs_def]
QED

Theorem bp_ptrs_bounded_empty:
  !fn s. bp_ptrs_bounded FEMPTY fn s
Proof
  rw[bp_ptrs_bounded_def, bp_segment_from_ops_def] >>
  BasicProvers.every_case_tac >> gvs[bp_ptr_from_op_def, bp_get_ptrs_def, memLocDefsTheory.ml_undefined_def]
QED

Theorem cexA_premises:
  fn_inst_wf cexA_fn /\ wf_function cexA_fn /\ ssa_form cexA_fn /\
  bp_analyze (cfg_analyze cexA_fn) cexA_fn = FEMPTY
Proof
  EVAL_TAC
QED

Theorem cexB_premises:
  fn_inst_wf cexB_fn /\ wf_function cexB_fn /\
  bp_analyze (cfg_analyze cexB_fn) cexB_fn = FEMPTY
Proof
  EVAL_TAC
QED

Theorem cexB_orig_run:
  rd (run_blocks 10 (mk_venom_context [] NONE) cexB_fn (init_venom_state "e")) = 2
Proof
  EVAL_TAC
QED

Theorem cexB_new_run:
  rd (run_blocks 10 (mk_venom_context [] NONE) (load_elim_function cexB_fn)
        (init_venom_state "e")) = 1
Proof
  EVAL_TAC
QED

Theorem rd_2:
  rd r = 2 ==> ?a s. r = Abort a s
Proof
  Cases_on `r` >> simp[rd_def]
QED

Theorem rd_1:
  rd r = 1 ==> ?s. r = Halt s
Proof
  Cases_on `r` >> simp[rd_def]
QED

(* The statement of load_elim_function_correct, as it stands, is false. *)
Theorem load_elim_function_correct_false:
  ~(!fuel (ir_ctx:num) ctx fn s bp.
      fn_inst_wf fn /\ s.vs_inst_idx = 0 /\
      bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s ==>
      ?fresh.
      (?e. run_blocks fuel ctx fn s = Error e) \/
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (load_elim_function fn) s))
Proof
  strip_tac >>
  first_x_assum (qspecl_then [`10`, `0`, `mk_venom_context [] NONE`, `cexB_fn`,
                              `init_venom_state "e"`, `FEMPTY`] mp_tac) >>
  simp[cexB_premises, bp_ptr_sound_empty, bp_ptrs_bounded_empty] >>
  conj_tac >- EVAL_TAC >>
  strip_assume_tac (MATCH_MP rd_2 cexB_orig_run) >>
  strip_assume_tac (MATCH_MP rd_1 cexB_new_run) >>
  simp[lift_result_def]
QED

