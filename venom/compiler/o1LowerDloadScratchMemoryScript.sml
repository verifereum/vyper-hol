Theory o1LowerDloadScratchMemory
Ancestors
  o1LowerDloadJointRelation o1LowerDloadRelocationKernel regularCallEmitSim finite_map

Theorem ld_memory_agree_scratch_write:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\
  FLOOKUP X key = SOME (aid,c) /\ LENGTH bs <= 32 ==>
  ld_memory_agree sites lo mask s.vs_memory
    (write_memory_with_expansion c bs t).vs_memory
Proof
  strip_tac >>
  `lo <= c` by metis_tac[ld_joint_geometry_def] >>
  fs[ld_memory_agree_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(c <= i /\ i < c + LENGTH bs)` by decide_tac >>
      simp[read_byte_write_memory_with_expansion]) >>
  rpt strip_tac >>
  rename1 `FLOOKUP sites id = SOME (b,d,z)` >>
  `0 < z` by decide_tac >>
  `d+z <= c \/ c+32 <= d` by
    metis_tac[ld_joint_geometry_def] >>
  `~(c <= d+j /\ d+j < c + LENGTH bs)` by decide_tac >>
  simp[read_byte_write_memory_with_expansion] >> metis_tac[]
QED
