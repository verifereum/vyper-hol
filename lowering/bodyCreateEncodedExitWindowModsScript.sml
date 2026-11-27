(* Join the preserved prefix and the encoded constructor payload at one cut. *)
Theory bodyCreateEncodedExitWindowMods
Ancestors
  bodyAbiTupleBufferResourcesMods bodyAbiTupleBufferStateMods
  allocaSiteResource memoryReadProps arithmetic

Theorem create_encoded_exit_window_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root dst (LENGTH prefix) prefix fin z Gz tz /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  mem_bytes_at (pbase + LENGTH prefix) (LENGTH bytes) z.vs_memory = bytes /\
  (!j. pbase + LENGTH prefix <= j /\ j < pbase + LENGTH prefix + LENGTH bytes ==>
       j NOTIN tz.t_mem) ==>
  pbase + capacity <= z.vs_alloca_next /\
  read_memory pbase (LENGTH prefix + LENGTH bytes) z = prefix ++ bytes /\
  (!j. pbase <= j /\ j < pbase + LENGTH prefix + LENGTH bytes ==>
       j NOTIN tz.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_inv z` by
    (drule_all_then (ACCEPT_TAC o CONJUNCT1) abi_tuple_buffer_resources_mods) >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (MAP_EVERY assume_tac o CONJUNCTS o
     SIMP_RULE bool_ss [abi_tuple_buffer_state_mods_def, ADD_SUB]) >>
  conj_tac
  >- (irule alloca_site_registered_below >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists `shared` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (pure_once_rewrite_tac[read_memory_split] >>
      qpat_assum `read_memory pbase (LENGTH prefix) z = prefix`
        (fn th => pure_rewrite_tac[th]) >>
      pure_rewrite_tac[read_memory_eq_mem_bytes_at] >>
      simp[]) >>
  gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `j < pbase + LENGTH prefix`
  >- (qpat_assum `!i. pbase <= i /\ i < pbase + LENGTH prefix ==> _` irule >>
      asm_rewrite_tac[]) >>
  qpat_assum `!i. pbase + LENGTH prefix <= i /\ _ ==> _` irule >>
  decide_tac
QED
