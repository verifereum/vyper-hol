(* Actual ALLOCA sites, rather than arbitrary recorded IDs, bound writes. *)
Theory abiDecodeMemActualFrame
Ancestors
  abiDecodeMemMembers abiDecoderFrame abiDecoderFrameCompose
  calldataDynOwned allocationGrowth
  venomState venomInst finite_map pred_set list arithmetic

val actual_footprint = ``\func lo hi (m:num |-> (num # num)) fp.
  !p n. MEM (p,n) fp <=> ?inst.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    lo <= inst.inst_id /\ inst.inst_id < hi /\
    FLOOKUP m inst.inst_id = SOME (p,n)``;

val actual_ids = ``{id | ?inst.
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = id}``;

Theorem abi_decode_actual_footprint_exists:
  !func lo hi m. ?fp. ^actual_footprint func lo hi m fp
Proof
  rpt gen_tac >>
  qspecl_then [`lo`,`hi`,`DRESTRICT m ^actual_ids`] strip_assume_tac
    abi_decode_mem_owned_footprint_exists >>
  qexists_tac `fp` >> simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem abi_decode_actual_output_frame:
  abi_decode_frame d sz s t ==>
  ?fp. ^actual_footprint func lo hi t.vs_allocas fp /\
    abi_decode_footprint_frame ((d,sz)::fp) s t
Proof
  strip_tac >>
  qspecl_then [`func`,`lo`,`hi`,`t.vs_allocas`] strip_assume_tac
    abi_decode_actual_footprint_exists >>
  qexists_tac `fp` >> asm_rewrite_tac[] >>
  irule abi_decode_footprint_frame_weaken >> qexists_tac `[(d,sz)]` >>
  simp[GSYM abi_decode_frame_footprint] >> rpt strip_tac >>
  qexistsl_tac [`d`,`sz`] >> simp[]
QED

Theorem abi_decode_actual_frames_compose:
  abi_decode_footprint_frame ((d1,n1)::fp1) s t /\
  abi_decode_footprint_frame ((d2,n2)::fp2) t u /\
  ^actual_footprint func lo mid t.vs_allocas fp1 /\
  ^actual_footprint func mid hi u.vs_allocas fp2 /\
  (!id. lo <= id /\ id < mid ==>
    FLOOKUP u.vs_allocas id = FLOOKUP t.vs_allocas id) /\
  lo <= mid /\ mid <= hi /\
  out <= d1 /\ d1+n1 <= out+sz /\ out <= d2 /\ d2+n2 <= out+sz ==>
  ?fp. ^actual_footprint func lo hi u.vs_allocas fp /\
    abi_decode_footprint_frame ((out,sz)::fp) s u
Proof
  strip_tac >> fs[abi_decode_footprint_frame_def] >>
  mp_tac (Q.INST
    [`s` |-> `s with vs_allocas := DRESTRICT s.vs_allocas ^actual_ids`,
     `t` |-> `t with vs_allocas := DRESTRICT t.vs_allocas ^actual_ids`,
     `u` |-> `u with vs_allocas := DRESTRICT u.vs_allocas ^actual_ids`]
    abi_decode_mem_owned_frames_compose) >>
  simp_tac (srw_ss()) [abi_decode_footprint_frame_def, FLOOKUP_DRESTRICT] >>
  (impl_tac >-
    (asm_rewrite_tac[] >> rpt conj_tac
     >- metis_tac[] >- metis_tac[] >> rw[])) >>
  strip_tac >> qexists_tac `fp` >>
  fs[abi_decode_footprint_frame_def] >> metis_tac[]
QED

Theorem abi_decode_actual_frame_accumulate:
  abi_decode_footprint_frame ((d,sz)::old) s t /\
  abi_decode_footprint_frame ((e,esz)::child) t u /\
  ^actual_footprint func lo hi t.vs_allocas old /\
  ^actual_footprint func child_lo child_hi u.vs_allocas child /\
  allocation_growth t u /\ lo <= child_lo /\ child_hi <= hi /\
  d <= e /\ e+esz <= d+sz ==>
  ?fp. ^actual_footprint func lo hi u.vs_allocas fp /\
    abi_decode_footprint_frame ((d,sz)::fp) s u
Proof
  strip_tac >>
  qspecl_then [`func`,`lo`,`hi`,`u.vs_allocas`] strip_assume_tac
    abi_decode_actual_footprint_exists >>
  `abi_decode_footprint_frame ((d,sz)::(old++child)) s u` by
    metis_tac[calldata_footprint_accumulate] >>
  `!p n. MEM (p,n) old ==> MEM (p,n) fp` by
    (rpt strip_tac >>
     `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       lo <= inst.inst_id /\ inst.inst_id < hi /\
       FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n)` by metis_tac[] >>
     `FLOOKUP u.vs_allocas inst.inst_id = SOME (p,n)` by
       metis_tac[allocation_growth_old] >> metis_tac[]) >>
  `!p n. MEM (p,n) child ==> MEM (p,n) fp` by
    (rpt strip_tac >>
     `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       child_lo <= inst.inst_id /\ inst.inst_id < child_hi /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (p,n)` by metis_tac[] >>
     `lo <= inst.inst_id /\ inst.inst_id < hi` by decide_tac >> metis_tac[]) >>
  qexists_tac `fp` >> asm_rewrite_tac[] >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `(d,sz)::(old++child)` >> asm_rewrite_tac[] >>
  simp[MEM_APPEND] >> rpt strip_tac >>
  qexistsl_tac [`d'`,`sz'`] >> simp[]
QED
