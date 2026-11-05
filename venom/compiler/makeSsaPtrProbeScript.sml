(* Scratch probe: MakeSSA on a pointer variable redefined by a non-pointer
   in a block the run never takes. *)
Theory makeSsaPtrProbe
Ancestors
  makeSsaCurrentDefs ptrDiscipline pointerConfinedDefs venomInst list
  pred_set

Definition pp_inst_def:
  pp_inst id opc ops outs =
    <| inst_id := id; inst_opcode := opc;
       inst_operands := ops; inst_outputs := outs |>
End

Definition pp_supply_def:
  pp_supply =
    <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1;2;3;4;5;6];
       irs_used_vars := ["v";"x"];
       irs_used_labels := ["E";"B";"C";"D"] |>
End

Definition pp_fn_def:
  pp_fn = mk_raw_function "probe"
    [<| bb_label := "E"; bb_instructions :=
        [pp_inst 0 ALLOCA [Lit 32w] ["v"];
         pp_inst 1 JNZ [Lit 0w; Label "B"; Label "C"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [pp_inst 2 ASSIGN [Lit 5w] ["v"];
         pp_inst 3 JMP [Label "D"] []] |>;
     <| bb_label := "C"; bb_instructions :=
        [pp_inst 4 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [pp_inst 5 MLOAD [Var "v"] ["x"];
         pp_inst 6 STOP [] []] |>]
End

Theorem pp_out_thm = EVAL ``FST (make_ssa_current_fn pp_supply pp_fn)``

Theorem pp_out_roots:
  !P. ptr_roots P (FST (make_ssa_current_fn pp_supply pp_fn)) = {"v"}
Proof
  simp[pp_out_thm, ptr_roots_def, alloca_roots_def, EXTENSION, fn_insts_def,
       fn_insts_blocks_def, inst_output_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM] >>
  metis_tac[]
QED

Theorem pp_out_use_vars:
  pointer_use_vars (FST (make_ssa_current_fn pp_supply pp_fn)) ["v"] =
  ["v"; "formal_var_0"]
Proof
  simp[pp_out_thm, pointer_use_vars_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC
QED

Theorem pp_out_pv:
  !P. fn_pv P (FST (make_ssa_current_fn pp_supply pp_fn)) =
      {"v"; "formal_var_0"}
Proof
  simp[fn_pv_def, pp_out_roots, pointer_derived_vars_def,
       SET_TO_LIST_SING, pp_out_use_vars]
QED

Theorem pp_out_pdv:
  pointer_derived_vars (FST (make_ssa_current_fn pp_supply pp_fn)) {"v"} =
  {"v"; "formal_var_0"}
Proof
  simp[pointer_derived_vars_def, SET_TO_LIST_SING, pp_out_use_vars]
QED

(* The PHI MakeSSA places at D merges the alloca pointer "v" with
   "formal_var_1", the renamed literal from the never-taken block B. *)
Theorem pp_out_not_phi_pv_all_var:
  ~phi_pv_all_var (FST (make_ssa_current_fn pp_supply pp_fn)) {"v"}
Proof
  simp[phi_pv_all_var_def, pp_out_pdv] >>
  simp[pp_out_thm, RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem pp_out_not_fn_ptr_ok:
  !P. ~fn_ptr_ok P (FST (make_ssa_current_fn pp_supply pp_fn))
Proof
  rw[fn_ptr_ok_def, pp_out_roots, pp_out_not_phi_pv_all_var]
QED

(* The input's roots and uses. Before fn_ptr_ok's definition clause the
   input met fn_ptr_ok (K {}); the clause rejects B's v = ASSIGN 5. *)
Theorem pp_in_roots:
  ptr_roots (K {}) pp_fn = {"v"}
Proof
  simp[pp_fn_def, pp_inst_def, mk_raw_function_def, ptr_roots_def,
       alloca_roots_def, EXTENSION, fn_insts_def, fn_insts_blocks_def,
       inst_output_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem pp_in_use_vars:
  pointer_use_vars pp_fn ["v"] = ["v"]
Proof
  simp[pointer_use_vars_def] >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC
QED

(* Second probe: a variable that is both a PARAM (at a pointer position)
   and an ALLOCA output.  Every definition of it is a pointer root, but
   renaming splits the roots, and the merging PHI's output derives from
   both an alloca root and a non-alloca root, which the write exclusion
   forbids. *)
Definition pp2_supply_def:
  pp2_supply =
    <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1;2;3;4;5;6];
       irs_used_vars := ["p"];
       irs_used_labels := ["f";"A";"B";"D"] |>
End

Definition pp2_fn_def:
  pp2_fn = mk_raw_function "f"
    [<| bb_label := "f"; bb_instructions :=
        [pp_inst 0 PARAM [Lit 0w] ["p"];
         pp_inst 1 JNZ [Lit 0w; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [pp_inst 2 ALLOCA [Lit 32w] ["p"];
         pp_inst 3 JMP [Label "D"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [pp_inst 4 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [pp_inst 5 MSTORE [Var "p"; Lit 0w] [];
         pp_inst 6 STOP [] []] |>]
End

Theorem pp2_out_thm = EVAL ``FST (make_ssa_current_fn pp2_supply pp2_fn)``

Theorem pp2_out_alloca_roots:
  alloca_roots (FST (make_ssa_current_fn pp2_supply pp2_fn)) = {"formal_var_1"}
Proof
  simp[pp2_out_thm, alloca_roots_def, EXTENSION, fn_insts_def,
       fn_insts_blocks_def, inst_output_def, LEFT_AND_OVER_OR,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem pp2_out_roots:
  ptr_roots P (FST (make_ssa_current_fn pp2_supply pp2_fn)) =
  if 0 IN P "f" then {"formal_var_1"; "p"} else {"formal_var_1"}
Proof
  simp[ptr_roots_def, pp2_out_alloca_roots] >>
  simp[pp2_out_thm, EXTENSION, fn_insts_def, fn_insts_blocks_def,
       inst_output_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  rw[] >> metis_tac[]
QED

Theorem pp2_out_use_vars:
  pointer_use_vars (FST (make_ssa_current_fn pp2_supply pp2_fn))
    ["formal_var_1"] = ["formal_var_1"; "formal_var_0"] /\
  pointer_use_vars (FST (make_ssa_current_fn pp2_supply pp2_fn))
    ["p"] = ["p"; "formal_var_0"]
Proof
  simp[pp2_out_thm, pointer_use_vars_def] >> conj_tac >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC
QED

Theorem pp2_out_pdv:
  pointer_derived_vars (FST (make_ssa_current_fn pp2_supply pp2_fn))
    {"formal_var_1"} = {"formal_var_1"; "formal_var_0"} /\
  pointer_derived_vars (FST (make_ssa_current_fn pp2_supply pp2_fn))
    {"p"} = {"p"; "formal_var_0"}
Proof
  simp[pointer_derived_vars_def, SET_TO_LIST_SING, pp2_out_use_vars]
QED

(* Without the PARAM as a root, the PHI mixes a pointer with p. *)
Theorem pp2_out_not_phi_pv_all_var:
  ~phi_pv_all_var (FST (make_ssa_current_fn pp2_supply pp2_fn))
     {"formal_var_1"}
Proof
  simp[phi_pv_all_var_def, pp2_out_pdv] >>
  simp[pp2_out_thm, RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM]
QED

(* With it, the store address derives from both kinds of root. *)
Theorem pp2_out_write_mixed:
  ?inst ops v.
    MEM inst (fn_insts (FST (make_ssa_current_fn pp2_supply pp2_fn))) /\
    mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    v IN pointer_derived_vars (FST (make_ssa_current_fn pp2_supply pp2_fn))
           {"formal_var_1"} /\
    v IN pointer_derived_vars (FST (make_ssa_current_fn pp2_supply pp2_fn))
           {"p"}
Proof
  simp[pp2_out_pdv] >>
  simp[pp2_out_thm, fn_insts_def, fn_insts_blocks_def, RIGHT_AND_OVER_OR,
       LEFT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[]
QED

Theorem pp2_out_not_fn_ptr_ok:
  !P. ~fn_ptr_ok P (FST (make_ssa_current_fn pp2_supply pp2_fn))
Proof
  gen_tac >> Cases_on `0 IN P "f"`
  >- (`ptr_roots P (FST (make_ssa_current_fn pp2_supply pp2_fn)) DIFF
       alloca_roots (FST (make_ssa_current_fn pp2_supply pp2_fn)) = {"p"}`
        by (simp[pp2_out_roots, pp2_out_alloca_roots, EXTENSION] >> rw[EQ_IMP_THM] >> gvs[]) >>
      simp[fn_ptr_ok_def] >> strip_tac >>
      strip_assume_tac pp2_out_write_mixed >>
      gvs[pp2_out_alloca_roots] >> metis_tac[]) >>
  simp[fn_ptr_ok_def, pp2_out_roots, pp2_out_not_phi_pv_all_var]
QED

(* The input's roots and uses, position 0 a pointer parameter. Before
   fn_ptr_ok's definition clause the input met fn_ptr_ok (K {0}); the
   clause rejects the PARAM output p, which is also an ALLOCA output. *)
Theorem pp2_in_roots:
  alloca_roots pp2_fn = {"p"} /\ ptr_roots (K {0}) pp2_fn = {"p"}
Proof
  simp[pp2_fn_def, pp_inst_def, mk_raw_function_def, ptr_roots_def,
       alloca_roots_def, EXTENSION, fn_insts_def, fn_insts_blocks_def,
       inst_output_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem pp2_in_use_vars:
  pointer_use_vars pp2_fn ["p"] = ["p"] /\ pointer_use_vars pp2_fn [] = []
Proof
  simp[pointer_use_vars_def] >> conj_tac >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC >>
  ONCE_REWRITE_TAC [WhileTheory.OWHILE_THM] >> EVAL_TAC
QED
