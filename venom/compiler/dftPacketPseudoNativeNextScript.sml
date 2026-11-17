Theory dftPacketPseudoNativeNext
Ancestors
  dftPacketNativeContinuation dftPacketOrdinaryTrace
  dftGasFromListTraceDefs venomInstProofs venomInst venomState rich_list arithmetic

Theorem dft_packet_pseudo_native_next:
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  is_pseudo inst.inst_opcode /\ step_inst g C8 inst s = OK t /\
  s1 = t with vs_inst_idx := SUC s.vs_inst_idx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt s1.vs_inst_idx = SOME i1 ==>
  SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,i1.inst_id),fn,i1,s1) /\
  trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry)) = obs
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    ~is_terminator inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  drule_all native_trace_blocks_continuation >> strip_tac >> gvs[] >>
  drule_all dft_ordinary_trace_cons >>
  disch_then (qspecl_then [`p`,`N-d`,`fn`,`d`] assume_tac) >>
  `?tail. trace_block p d (N-d) C8 fn bt
      (t with vs_inst_idx := SUC s.vs_inst_idx) =
      ((p,d,i1.inst_id),fn,i1,t with vs_inst_idx := SUC s.vs_inst_idx)::tail` by
    (simp[Once (cj 2 trace_defs)] >> metis_tac[]) >>
  gvs[] >>
  `SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by
    (qpat_x_assum `DROP j _ = _` (mp_tac o AP_TERM ``LENGTH : list_visit list -> num``) >>
     simp[] >> decide_tac) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `DROP j _ = _`
       (mp_tac o AP_TERM ``EL 1 : list_visit list -> list_visit``) >>
     simp[listTheory.EL_DROP, ADD1]) >>
  simp[TAKE_SUC_BY_TAKE, SNOC_APPEND, trace_gas_def, MAP_APPEND,
       FLAT_APPEND, visit_gas_def]
QED
