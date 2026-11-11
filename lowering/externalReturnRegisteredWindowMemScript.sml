(* Encoder windows whose source is owned by a registered allocation. *)
Theory externalReturnRegisteredWindowMem
Ancestors
  externalReturnDestinationMem externalReturnEncoderSites
  registeredAllocationWindow abiEncoderWindowContract abiEncoderProps
  loweringHalt exprLoweringProps localPtrsProps allocaSiteResource compileEnv venomMemDefs finite_map pred_set words

Theorem registered_encoder_allocate_window:
  compile_alloc_buffer n sa = (buf,st) /\ fn_has_code sa st func /\
  compile_abi_encode_to_buf buf.buf_operand src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  FLOOKUP s.vs_allocas parent = SOME (p,m) /\
  parent <> sa.cs_next_id /\ parent NOTIN frag_ids st en /\ cap <= m /\
  eval_operand src s = SOME (n2w p) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  abi_encoder_window_input ei at av p cap s.vs_memory /\
  abi_encoder_admissible ei /\ LENGTH (enc at av) <= n /\ n < dimword (:256) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==> sz = n) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u d. mem_cont_sim ctx func s u /\
    abi_encoder_window_pre ctx func st en buf.buf_operand src ei at av p cap d u
Proof
  strip_tac >> drule_all return_destination_alloc_mem_cont >>
  disch_then (qx_choose_then `u` (qx_choose_then `d` strip_assume_tac)) >>
  `FLOOKUP u.vs_allocas parent = SOME (p,m)` by metis_tac[] >>
  `sa.cs_next_id NOTIN frag_ids st en` by
    metis_tac[allocated_encoder_site_excluded] >>
  `eval_operand src u = SOME (n2w p)` by metis_tac[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at st x` by
    metis_tac[] >>
  `p + cap <= u.vs_alloca_next` by
    (drule_all alloca_site_registered_below >> decide_tac) >>
  `venomMemDefs$regions_disjoint (p,cap) (d,n)` by
    (irule registered_allocation_subwindow_disjoint >>
     qexistsl_tac [`sa.cs_next_id`, `{sa.cs_next_id}`, `m`, `parent`, `u`] >> simp[]) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (p,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)` by
    suspend "scratch" >>
  qexistsl_tac [`u`, `d`] >> conj_tac >- first_assum ACCEPT_TAC >>
  suspend "assembly"
QED

Resume registered_encoder_allocate_window[scratch]:
  rpt gen_tac >> strip_tac >>
  `inst.inst_id <> sa.cs_next_id` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule registered_allocation_subwindow_disjoint >>
      qexistsl_tac [`inst.inst_id`, `frag_ids st en`, `m`, `parent`, `u`] >> simp[]) >>
  irule registered_allocation_subwindow_disjoint >>
  qexistsl_tac [`inst.inst_id`, `frag_ids st en`, `n`, `sa.cs_next_id`, `u`] >> simp[]
QED

Resume registered_encoder_allocate_window[assembly]:
  `venomMemDefs$regions_disjoint (p,cap) (d,LENGTH (enc at av))` by
    (qpat_x_assum `venomMemDefs$regions_disjoint (p,cap) (d,n)` mp_tac >>
     qpat_x_assum `LENGTH (enc at av) <= n` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def,
       Excl "LENGTH_EQ_NUM_compute"] >> decide_tac) >>
  pure_rewrite_tac [abi_encoder_window_pre_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Finalise registered_encoder_allocate_window
