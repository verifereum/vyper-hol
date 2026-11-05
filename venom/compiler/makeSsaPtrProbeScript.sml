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

(* The input meets the syntactic half for P = K {}. *)
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

Theorem pp_in_fn_ptr_ok:
  fn_ptr_ok (K {}) pp_fn
Proof
  simp[fn_ptr_ok_def, fn_pv_def, pp_in_roots, pointer_derived_vars_def,
       SET_TO_LIST_SING, pp_in_use_vars, affine_pointer_ops_def,
       phi_pv_all_var_def, ptr_use_ok_def] >>
  simp[pp_fn_def, pp_inst_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, DISJ_IMP_THM, FORALL_AND_THM,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> rw[] >> gvs[]
QED
