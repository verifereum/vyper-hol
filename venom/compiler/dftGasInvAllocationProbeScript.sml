Theory dftGasInvAllocationProbe
Ancestors
  dftDefs dftScheduleOrder venomWf venomInst

Definition inv_alloc_probe_def:
  inv_alloc_probe = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ALLOCA [Lit 32w] ["a"];
     mk_inst 1 ADD [Lit 2w; Lit 3w] ["v"];
     mk_inst 2 STOP [] []] |>
End

Theorem inv_alloc_probe_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_alloc_probe).bb_instructions = [0;1;2]
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_alloc_after_probe_def:
  inv_alloc_after_probe = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ADD [Lit 2w; Lit 3w] ["v"];
     mk_inst 1 ALLOCA [Lit 32w] ["a"];
     mk_inst 2 STOP [] []] |>
End

Theorem inv_alloc_after_probe_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_alloc_after_probe).bb_instructions = [0;1;2]
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_two_alloc_probe_def:
  inv_two_alloc_probe = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ALLOCA [Lit 32w] ["a"];
     mk_inst 1 ALLOCA [Lit 64w] ["b"];
     mk_inst 2 STOP [] []] |>
End

Theorem inv_two_alloc_probe_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_two_alloc_probe).bb_instructions = [0;1;2]
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_alloc_use_probe_def:
  inv_alloc_use_probe = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ALLOCA [Lit 32w] ["a"];
     mk_inst 1 ADD [Lit 2w; Lit 3w] ["v"];
     mk_inst 2 MSTORE [Var "a"; Lit 0w] [];
     mk_inst 3 STOP [] []] |>
End

Theorem inv_alloc_use_probe_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_alloc_use_probe).bb_instructions = [1;0;2;3]
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_alloc_probe_fn_def:
  inv_alloc_probe_fn = mk_raw_function "probe" [inv_alloc_use_probe]
End

Theorem inv_alloc_use_inversion:
  MAP (\i. i.inst_id) inv_alloc_use_probe.bb_instructions = [0;1;2;3] /\
  id_before (MAP (\i. i.inst_id) inv_alloc_use_probe.bb_instructions) 0 1 /\
  id_before (MAP (\i. i.inst_id)
    (dft_block [] inv_alloc_use_probe).bb_instructions) 1 0 /\
  is_barrier (mk_inst 0 ALLOCA [Lit 32w] ["a"])
Proof
  simp[inv_alloc_use_probe_schedule] >> EVAL_TAC >> simp[] >>
  conj_tac >> qexistsl_tac [`0`,`1`] >> simp[]
QED

Theorem inv_alloc_use_local_wf:
  EVERY inst_wf inv_alloc_use_probe.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) inv_alloc_use_probe.bb_instructions) /\
  MEM inv_alloc_use_probe inv_alloc_probe_fn.fn_blocks /\
  wf_function inv_alloc_probe_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem inv_alloc_use_ssa:
  wf_ssa inv_alloc_probe_fn
Proof
  simp[wf_ssa_def] >> conj_tac
  >- (EVAL_TAC >> simp[]) >>
  rw[def_dominates_uses_def, inv_alloc_probe_fn_def,
     inv_alloc_use_probe_def, mk_raw_function_def, mk_inst_def] >>
  simp[def_available_at_def] >>
  qexists_tac `mk_inst 0 ALLOCA [Lit 32w] ["a"]` >>
  simp[mk_inst_def] >> conj_tac >- (simp[fn_dominates_def, fn_reachable_def, fn_entry_label_def,
                    entry_block_def, relationTheory.RTC_REFL] >>
               Cases_on `path` >> simp[]) >>
  qexistsl_tac [`0`,`2`] >> simp[]
QED

Theorem inv_alloc_use_fn_schedule:
  MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    (dft_fn inv_alloc_probe_fn).fn_blocks = [[1;0;2;3]]
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_alloc_effect_probe_def:
  inv_alloc_effect_probe = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ALLOCA [Lit 32w] ["a"];
     mk_inst 1 MSTORE [Lit 0w; Lit 1w] [];
     mk_inst 2 MSTORE [Var "a"; Lit 0w] [];
     mk_inst 3 STOP [] []] |>
End

Theorem inv_alloc_effect_probe_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_alloc_effect_probe).bb_instructions = [1;0;2;3]
Proof
  EVAL_TAC >> simp[]
QED

Definition inv_two_alloc_use_probe_def:
  inv_two_alloc_use_probe = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ALLOCA [Lit 32w] ["a"];
     mk_inst 1 ALLOCA [Lit 64w] ["b"];
     mk_inst 2 MSTORE [Var "a"; Lit 0w] [];
     mk_inst 3 STOP [] []] |>
End

Theorem inv_two_alloc_use_probe_schedule:
  MAP (\i. i.inst_id) (dft_block [] inv_two_alloc_use_probe).bb_instructions = [1;0;2;3]
Proof
  EVAL_TAC >> simp[]
QED

Theorem inv_alloc_effect_inversion:
  id_before (MAP (\i. i.inst_id) inv_alloc_effect_probe.bb_instructions) 0 1 /\
  id_before (MAP (\i. i.inst_id)
    (dft_block [] inv_alloc_effect_probe).bb_instructions) 1 0
Proof
  simp[inv_alloc_effect_probe_schedule] >> EVAL_TAC >> simp[] >>
  conj_tac >> qexistsl_tac [`0`,`1`] >> simp[]
QED

Theorem inv_two_alloc_use_inversion:
  id_before (MAP (\i. i.inst_id) inv_two_alloc_use_probe.bb_instructions) 0 1 /\
  id_before (MAP (\i. i.inst_id)
    (dft_block [] inv_two_alloc_use_probe).bb_instructions) 1 0
Proof
  simp[inv_two_alloc_use_probe_schedule] >> EVAL_TAC >> simp[] >>
  conj_tac >> qexistsl_tac [`0`,`1`] >> simp[]
QED

Theorem inv_alloc_probe_family_wf:
  EVERY (\bb. EVERY inst_wf bb.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    [inv_alloc_probe; inv_alloc_after_probe; inv_two_alloc_probe;
     inv_alloc_use_probe; inv_alloc_effect_probe; inv_two_alloc_use_probe]
Proof
  EVAL_TAC >> simp[]
QED

Theorem inv_alloc_probe_sources:
  MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    [inv_alloc_probe; inv_alloc_after_probe; inv_two_alloc_probe;
     inv_alloc_use_probe; inv_alloc_effect_probe; inv_two_alloc_use_probe] =
    [[0;1;2]; [0;1;2]; [0;1;2]; [0;1;2;3]; [0;1;2;3]; [0;1;2;3]]
Proof
  EVAL_TAC >> simp[]
QED

Theorem inv_alloc_inversion_opcodes:
  MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions)
    [inv_alloc_use_probe; inv_alloc_effect_probe; inv_two_alloc_use_probe] =
    [[ALLOCA; ADD; MSTORE; STOP];
     [ALLOCA; MSTORE; MSTORE; STOP];
     [ALLOCA; ALLOCA; MSTORE; STOP]] /\
  is_barrier (mk_inst 1 ALLOCA [Lit 64w] ["b"])
Proof
  EVAL_TAC >> simp[]
QED
