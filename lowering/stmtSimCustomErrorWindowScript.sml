(* Registered source and shifted payload destination for custom errors. *)
Theory stmtSimCustomErrorWindow
Ancestors
  registeredAllocationWindow abiEncoderWindowContract abiEncoderRegisteredEffect
  allocaSiteResource abiEncoderProps venomMemDefs finite_map pred_set list words

Theorem custom_error_registered_payload_window:
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  FLOOKUP s.vs_allocas parent = SOME (p,n) /\
  FLOOKUP s.vs_allocas dest = SOME (d,B+32) /\ parent <> dest /\
  parent NOTIN frag_ids st en /\ dest NOTIN frag_ids st en /\ cap <= n /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand dst s = SOME (n2w (d+32)) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  abi_encoder_window_input ei at av p cap s.vs_memory /\
  abi_encoder_admissible ei /\ LENGTH (enc at av) <= B /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_window_pre ctx func st en dst src ei at av p cap (d+32) s
Proof
  strip_tac >>
  `p+n <= s.vs_alloca_next /\ d+(B+32) <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `venomMemDefs$regions_disjoint (p,n) (d,B+32)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (p,cap) (d+32,LENGTH (enc at av))` by
    (qpat_x_assum `venomMemDefs$regions_disjoint (p,n) _` mp_tac >>
     qpat_x_assum `cap <= n` mp_tac >>
     qpat_x_assum `LENGTH (enc at av) <= B` mp_tac >>
     simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def,
       Excl "LENGTH_EQ_NUM_compute"] >> decide_tac) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (p,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d+32,LENGTH (enc at av)) (b,sz)` by
    suspend "scratch" >>
  pure_rewrite_tac [abi_encoder_window_pre_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Resume custom_error_registered_payload_window[scratch]:
  rpt gen_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (p,cap) (b,sz)` by
    (irule registered_allocation_subwindow_disjoint >>
     qexistsl_tac [`inst.inst_id`, `frag_ids st en`, `n`, `parent`, `s`] >> simp[]) >>
  `venomMemDefs$regions_disjoint (d,B+32) (b,sz)` by
    (irule registered_allocation_subwindow_disjoint >>
     qexistsl_tac [`inst.inst_id`, `frag_ids st en`, `B+32`, `dest`, `s`] >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,B+32) _` mp_tac >>
  qpat_x_assum `LENGTH (enc at av) <= B` mp_tac >>
  simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def,
    Excl "LENGTH_EQ_NUM_compute"] >> decide_tac
QED
Finalise custom_error_registered_payload_window

Theorem custom_error_payload_effect_absorb:
  abi_encoder_registered_effect ids [(d+32,k)] s t /\ ids SUBSET larger /\
  dest IN larger /\ FLOOKUP t.vs_allocas dest = SOME (d,B+32) /\ k <= B ==>
  abi_encoder_registered_effect larger [] s t
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def, SUBSET_DEF, EVERY_DEF] >>
  strip_tac >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!a. _ ==> mem_bytes_at _ _ _ = _` irule >>
  reverse conj_tac
  >- (simp_tac (srw_ss()) [] >>
      qpat_x_assum `!i b sz. _` (qspecl_then [`dest`,`d`,`B+32`] mp_tac) >>
      qpat_x_assum `k <= B` mp_tac >>
      asm_rewrite_tac[] >> decide_tac) >>
  metis_tac[]
QED
