(* Registered shared calldata and tuple windows for the external-call encoder. *)
Theory extcallEncoderWindowMemory
Ancestors
  abiEncoderWindowContract externalReturnEncoderSites externalReturnOutputAlloc
  allocaSiteResource exprLoweringProps compileEnv venomMemDefs finite_map pred_set
  emitHelper context fragExec abiEncoderProps

Theorem extcall_registered_encoder_window_pre:
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w (b+32)) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  FLOOKUP s.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
  FLOOKUP s.vs_allocas tuple_id = SOME (sb,cap) /\ buf_id <> tuple_id /\
  LENGTH (enc at av) <= args_size /\
  (!inst p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,n) ==>
    inst.inst_id <> buf_id /\ inst.inst_id <> tuple_id /\ n = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap (b+32) s
Proof
  rpt strip_tac >>
  `sb + cap <= s.vs_alloca_next /\
   b + (MAX args_size ret_size + 32) <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `venomMemDefs$regions_disjoint (sb,cap) (b,MAX args_size ret_size+32)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (sb,cap) (b+32,LENGTH (enc at av))` by
    (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     qpat_x_assum `LENGTH (enc at av) <= args_size` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >>
     rpt strip_tac >> simp_tac std_ss [] >> decide_tac) >>
  `b+32+LENGTH (enc at av) <= s.vs_alloca_next` by
    (qpat_x_assum `b + (MAX _ _ + 32) <= _` mp_tac >>
     qpat_x_assum `LENGTH (enc at av) <= args_size` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac std_ss [arithmeticTheory.MAX_DEF] >> decide_tac) >>
  rewrite_tac [abi_encoder_window_pre_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse (rpt conj_tac) >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `inst.inst_id <> buf_id /\ inst.inst_id <> tuple_id /\ sz = 32` by
    metis_tac[] >>
  `venomMemDefs$regions_disjoint (sb,cap) (b',sz) /\
   venomMemDefs$regions_disjoint (b,MAX args_size ret_size+32) (b',sz)` by
    (conj_tac >> irule alloca_site_registered_disjoint >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `venomMemDefs$regions_disjoint (b,_) (b',sz)` mp_tac >>
  qpat_x_assum `LENGTH (enc at av) <= args_size` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def,
    arithmeticTheory.MAX_DEF] >>
  rpt strip_tac >> simp_tac std_ss [] >> decide_tac
QED

(* The two ids are exactly the starts of shared and tuple allocations.
   Intervening selector/store/ADD fragments supply the two ci_mono facts. *)
Theorem extcall_encoder_registered_scratch:
  compile_alloc_buffer shared_size shared = (buf,allocated) /\
  ci_mono allocated tuple /\
  compile_alloc_buffer tuple_size tuple = (argbuf,stored) /\
  ci_mono stored st /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\
  FLOOKUP s.vs_allocas shared.cs_next_id = SOME (b,shared_size) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids st en /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,n) ==>
  inst.inst_id <> shared.cs_next_id /\
  inst.inst_id <> tuple.cs_next_id /\ n = 32
Proof
  strip_tac >>
  `allocated.cs_next_id = shared.cs_next_id + 1 /\
   stored.cs_next_id = tuple.cs_next_id + 1` by
    (qpat_x_assum `compile_alloc_buffer shared_size _ = _` mp_tac >>
     qpat_x_assum `compile_alloc_buffer tuple_size _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `inst.inst_id <> shared.cs_next_id /\
   inst.inst_id <> tuple.cs_next_id` by
    (qpat_x_assum `inst.inst_id IN frag_ids st en` mp_tac >>
     qpat_x_assum `ci_mono allocated tuple` mp_tac >>
     qpat_x_assum `ci_mono stored st` mp_tac >>
     simp_tac std_ss [frag_ids_def, ci_mono_def, IN_GSPEC_IFF] >>
     rpt strip_tac >> decide_tac) >>
  `inst.inst_operands = [Lit 32w]` by
    metis_tac[encoder_function_alloca_shape] >>
  `shared_size <= shared_size` by simp_tac std_ss [] >>
  drule_all return_output_registered_scratch >>
  metis_tac[]
QED
