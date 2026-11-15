(* Concrete witnesses for memory-read barriers and DLOAD use rewriting. *)
Theory mmMergeWitness
Ancestors
  cfgWf
  mmTransformSupply venomInst finite_map venomWf venomFnScheduleRunner
  o1PassLift unitMemInv contextCodegenRel ctxLookupAgreeHelpers
Libs
  wordsLib finite_mapLib

val () = computeLib.add_funs [finite_mapTheory.FLOOKUP_UPDATE];

Definition mm_barrier_block_def:
  mm_barrier_block = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 1 MLOAD [Lit 0w] ["a"];
     mk_inst 2 MSTORE [Lit 128w; Var "a"] [];
     mk_inst 3 SHA3 [Lit 128w; Lit 32w] ["hash"];
     mk_inst 4 MLOAD [Lit 32w] ["b"];
     mk_inst 5 MSTORE [Lit 160w; Var "b"] [];
     mk_inst 6 STOP [] []] |>
End

Theorem mm_memory_read_barrier_witness:
  MAP (\cg. cg.cg_length)
    (scan_block (dfg_build_function
       (mk_raw_function "f" [mm_barrier_block]))
       Mem2Mem mm_barrier_block).ss_flushed = [32; 32]
Proof
  EVAL_TAC
QED

Theorem mm_memzero_read_barrier_witness:
  MAP (\cg. cg.cg_length)
    (scan_block_memzero dfg
      <| bb_label := "entry"; bb_instructions :=
         [mk_inst 1 MSTORE [Lit 0w; Lit 0w] [];
          mk_inst 2 MLOAD [Lit 0w] ["read"];
          mk_inst 3 MSTORE [Lit 32w; Lit 0w] []] |>).
      mz_flushed = [32; 32]
Proof
  EVAL_TAC
QED

Theorem mm_calldata_read_barrier_witness:
  MAP (\cg. cg.cg_length)
    (scan_block dfg CalldataMerge
      <| bb_label := "entry"; bb_instructions :=
         [mk_inst 1 CALLDATACOPY [Lit 128w; Lit 0w; Lit 32w] [];
          mk_inst 2 MLOAD [Lit 128w] ["read"];
          mk_inst 3 CALLDATACOPY [Lit 160w; Lit 32w; Lit 32w] []] |>).
      ss_flushed = [32; 32]
Proof
  EVAL_TAC
QED

Definition mm_cross_block_function_def:
  mm_cross_block_function = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 ASSIGN [Lit 32w] ["src"];
        mk_inst 2 DLOAD [Var "src"] ["value"];
        mk_inst 3 JMP [Label "store"] []] |>;
     <| bb_label := "store"; bb_instructions :=
       [mk_inst 4 MSTORE [Lit 0w; Var "value"] [];
        mk_inst 5 STOP [] []] |>]
End

Theorem mm_cross_block_dload_witness:
  MAP (\bb. MAP (\inst. (inst.inst_opcode, inst.inst_operands))
                 bb.bb_instructions)
    (transform_function mm_cross_block_function).fn_blocks =
    [[(ASSIGN, [Lit 32w]); (NOP, []); (JMP, [Label "store"])];
     [(DLOADBYTES, [Lit 0w; Var "src"; Lit 32w]); (STOP, [])]]
Proof
  EVAL_TAC
QED

Theorem mm_dload_self_destination_witness:
  transform_function (mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 DLOAD [Lit 0w] ["value"];
        mk_inst 2 MSTORE [Var "value"; Var "value"] [];
        mk_inst 3 STOP [] []] |>]) =
  mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 DLOAD [Lit 0w] ["value"];
        mk_inst 2 MSTORE [Var "value"; Var "value"] [];
        mk_inst 3 STOP [] []] |>]
Proof
  EVAL_TAC
QED

(* The store block is visited before its producer. Python updates it
   later, without rerunning the merge scan over its two adjacent copies. *)
Definition mm_backward_update_function_def:
  mm_backward_update_function = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 JMP [Label "load"] []] |>;
     <| bb_label := "store"; bb_instructions :=
       [mk_inst 2 MSTORE [Lit 0w; Var "value"] [];
        mk_inst 3 DLOADBYTES [Lit 32w; Lit 32w; Lit 32w] [];
        mk_inst 4 STOP [] []] |>;
     <| bb_label := "load"; bb_instructions :=
       [mk_inst 5 DLOAD [Lit 0w] ["value"];
        mk_inst 6 JMP [Label "store"] []] |>]
End

Theorem mm_dload_backward_update_witness:
  MAP (\bb. MAP (\inst. (inst.inst_opcode, inst.inst_operands))
                 bb.bb_instructions)
    (transform_function mm_backward_update_function).fn_blocks =
    [[(JMP, [Label "load"])];
     [(DLOADBYTES, [Lit 0w; Lit 0w; Lit 32w]);
      (DLOADBYTES, [Lit 32w; Lit 32w; Lit 32w]); (STOP, [])];
     [(NOP, []); (JMP, [Label "store"])]]
Proof
  EVAL_TAC
QED

Theorem mm_supply_cross_block_witness:
  transform_function_supply supply mm_cross_block_function =
    (transform_function mm_cross_block_function, supply) /\
  transform_function_supply supply mm_backward_update_function =
    (transform_function mm_backward_update_function, supply)
Proof
  EVAL_TAC
QED

Theorem mm_copy_read_after_write_witness:
  MAP (\cg. cg.cg_length)
    (scan_block dfg Mem2Mem
      <| bb_label := "entry"; bb_instructions :=
         [mk_inst 1 MCOPY [Lit 32w; Lit 0w; Lit 32w] [];
          mk_inst 2 MCOPY [Lit 64w; Lit 32w; Lit 32w] []] |>).
      ss_flushed = [32; 32]
Proof
  EVAL_TAC
QED

Theorem mm_adjacent_copies_merge_witness:
  MAP (\cg. (cg.cg_dst, cg.cg_src, cg.cg_length))
    (scan_block dfg Mem2Mem
      <| bb_label := "entry"; bb_instructions :=
         [mk_inst 1 MCOPY [Lit 128w; Lit 0w; Lit 32w] [];
          mk_inst 2 MCOPY [Lit 160w; Lit 32w; Lit 32w] []] |>).
      ss_flushed = [(128, 0, 64)]
Proof
  EVAL_TAC
QED

Definition mm_adjacent_copy_function_def:
  mm_adjacent_copy_function = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 MCOPY [Lit 128w; Lit 0w; Lit 32w] [];
        mk_inst 2 MCOPY [Lit 160w; Lit 32w; Lit 32w] [];
        mk_inst 3 STOP [] []] |>]
End

Definition mm_copy_supply_def:
  mm_copy_supply = <| irs_next_inst := 4; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [1;2;3];
    irs_used_vars := []; irs_used_labels := ["f";"entry"] |>
End

Theorem mm_copy_fixture_wf:
  fn_inst_wf mm_adjacent_copy_function /\
  wf_function mm_adjacent_copy_function /\
  wf_ssa mm_adjacent_copy_function /\
  ir_supply_covers_fn mm_copy_supply mm_adjacent_copy_function /\
  fn_entry_state mm_adjacent_copy_function (init_venom_state "entry")
Proof
  EVAL_TAC >> rw[] >> gvs[]
QED

Theorem mm_copy_fixture_all_reachable:
  all_reachable mm_adjacent_copy_function
Proof
  simp[all_reachable_def, mm_adjacent_copy_function_def,
       mk_raw_function_def, fn_reachable_def, fn_entry_label_def, entry_block_def]
QED

Theorem mm_copy_fixture_bound:
  EVERY (\i. !st. static_mem_ok 192 ctx mm_adjacent_copy_function i st)
    (fn_insts mm_adjacent_copy_function)
Proof
  simp[mm_adjacent_copy_function_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, static_mem_ok_def] >>
  rpt conj_tac >> gen_tac >> disj2_tac >> EVAL_TAC
QED

Theorem mm_copy_fixture_reachability:
  reachability_closed
    (\c f i t. f = mm_adjacent_copy_function /\ active_inst f i t) ctx
Proof
  simp[reachability_closed_def] >> rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE)
    (fn_insts mm_adjacent_copy_function)` by EVAL_TAC >>
  drule_all EVERY_active_inst >> simp[]
QED

Theorem mm_copy_fixture_entry_inv:
  fn_entry_inv
    (\c f i t. f = mm_adjacent_copy_function /\ active_inst f i t)
    ctx mm_adjacent_copy_function (init_venom_state "entry")
Proof
  simp[fn_entry_inv_def]
QED

Theorem mm_supply_merges_copy_witness:
  transform_function_supply mm_copy_supply mm_adjacent_copy_function =
    (mk_raw_function "f"
      [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 1 NOP [] [];
         mk_inst 2 MCOPY [Lit 128w; Lit 0w; Lit 64w] [];
         mk_inst 3 STOP [] []] |>], mm_copy_supply)
Proof
  EVAL_TAC
QED

(* Every premise of mm_function_correct holds for a terminating function
   whose two copies are actually merged. This witness uses only definitions,
   so it does not depend on the correctness proof it checks for vacuity. *)
Theorem mm_correctness_premises_allow_merge:
  ?Inv fn' supply'.
    fn_inst_wf mm_adjacent_copy_function /\
    wf_function mm_adjacent_copy_function /\ wf_ssa mm_adjacent_copy_function /\
    all_reachable mm_adjacent_copy_function /\
    ir_supply_covers_fn mm_copy_supply mm_adjacent_copy_function /\
    fn_entry_state mm_adjacent_copy_function (init_venom_state "entry") /\
    LENGTH (init_venom_state "entry").vs_call_ctx.cc_calldata < dimword (:256) /\
    192 < dimword (:256) /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx mm_adjacent_copy_function (init_venom_state "entry") /\
    (!inst st. Inv ctx mm_adjacent_copy_function inst st ==>
      static_mem_ok 192 ctx mm_adjacent_copy_function inst st) /\
    transform_function_supply mm_copy_supply mm_adjacent_copy_function =
      (fn', supply') /\
    fn' <> mm_adjacent_copy_function /\
    terminates (run_function 1 ctx mm_adjacent_copy_function
      (init_venom_state "entry"))
Proof
  `!inst st. active_inst mm_adjacent_copy_function inst st ==>
     static_mem_ok 192 ctx mm_adjacent_copy_function inst st` by
    (rpt strip_tac >>
     mp_tac mm_copy_fixture_bound >> strip_tac >>
     drule_all EVERY_active_inst >> simp[]) >>
  qexists_tac `\c f i t. f = mm_adjacent_copy_function /\ active_inst f i t` >>
  simp[mm_copy_fixture_wf, mm_copy_fixture_all_reachable, mm_copy_fixture_reachability,
       mm_copy_fixture_entry_inv, mm_supply_merges_copy_witness] >>
  EVAL_TAC
QED
