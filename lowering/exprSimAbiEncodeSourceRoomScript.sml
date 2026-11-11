(* Bridge-local allocation room, without registration in the execution context. *)
Theory exprSimAbiEncodeSourceRoom
Ancestors
  exprSimAbiEncodeWindowRoom exprSimAbiEncodeBoundaryProbe
  venomWf venomInst

Theorem abi_encode_bridge_alloca_distinct[local]:
  fn_inst_ids_distinct func ==>
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func))
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  simp[fn_inst_ids_distinct_def, fn_insts_def] >>
  disch_tac >> irule listTheory.FILTER_ALL_DISTINCT >>
  irule (INST_TYPE [beta |-> ``:num``] listTheory.ALL_DISTINCT_MAP) >>
  qexists_tac `\i. i.inst_id` >> asm_rewrite_tac[]
QED

Theorem abi_encode_bridge_local_room:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) ==>
  alloca_room (ctx with ctx_functions := [obs]) obs s
Proof
  strip_tac >> irule abi_encode_relabel_registered_room >>
  simp[abi_encode_bridge_alloca_distinct] >> metis_tac[]
QED

Theorem abi_encode_bridge_window_run:
  !dst src ei st out st' ctx func obs initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' obs /\ fn_inst_ids_distinct obs /\
    obs.fn_name = func.fn_name /\
    (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
         i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
    alloca_inv initial /\ alloca_room ctx func initial /\
    sb + source_cap <= initial.vs_alloca_next /\
    d + LENGTH (enc at av) <= initial.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (sb,source_cap) (d,LENGTH (enc at av)) /\
    (!inst b sz.
      MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (sb,source_cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,LENGTH (enc at av))] initial actual /\
      alloca_inv actual /\
      alloca_room (ctx with ctx_functions := [obs]) obs actual /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
             lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\
      actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx obs initial actual
Proof
  rpt strip_tac >>
  `alloca_room (ctx with ctx_functions := [obs]) obs initial` by
    (irule abi_encode_bridge_local_room >> metis_tac[]) >>
  drule compile_abi_encode_to_buf_window_run_room >>
  rpt (disch_then drule) >> simp[]
QED
