(* Concrete witnesses for memory-read barriers and DLOAD use rewriting. *)
Theory mmMergeWitness
Ancestors
  mmTransformSupply venomInst finite_map
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
