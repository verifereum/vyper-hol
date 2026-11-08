(* One counted encoder exit, with recovered resources and the selector frame. *)
Theory exprExtRequestEncoderEndpoint
Ancestors
  exprExtRequestEncoderFrame exprExtRequestEncoderResource
  abiEncoderWindowContract abiEncoderRegisteredEffect exprLoweringProps fragGasMode

Theorem extrequest_encoder_run_resources:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  fmp_room ctx func s /\
  owner < st.cs_next_id /\
  FLOOKUP s.vs_allocas owner = SOME (baddr,sz) /\
  baddr <= p /\ p + n <= baddr + sz /\
  venomMemDefs$regions_disjoint (p,n) (d,LENGTH (enc at av)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc at av))] s t /\
    alloca_inv t /\ alloca_room ctx func t /\ fmp_room ctx func t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
       lookup_var x t = SOME w) /\
    window_alloca_growth s t /\
    (!i b k. i IN window_alloca_sites func (frag_ids st en) /\
       FLOOKUP t.vs_allocas i = SOME (b,k) ==> k = 32) /\
    t.vs_labels = s.vs_labels /\
    t.vs_alloca_next + pending_alloca_size func t <=
      s.vs_alloca_next + pending_alloca_size func s /\
    t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    FLOOKUP t.vs_allocas owner = SOME (baddr,sz) /\
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >> drule_all abi_encoder_window_run_fmp >> strip_tac >>
  `alloca_room ctx func t` by
    (drule abi_encoder_window_pre_resources >> strip_tac >>
     qpat_x_assum `alloca_room ctx func s` mp_tac >>
     simp[alloca_room_def]) >>
  `fmp_room ctx func t` by metis_tac[fmp_room_static_charge] >>
  `FLOOKUP t.vs_allocas owner = SOME (baddr,sz)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule abi_encoder_window_effect_bytes >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en)`,
    `[(d,LENGTH (enc at av))]`] >> simp[] >>
  rpt strip_tac >> irule extrequest_encoder_registered_window >>
  qpat_assum `FLOOKUP t.vs_allocas owner = SOME (baddr,sz)` (irule_at Any) >>
  qpat_assum `FLOOKUP t.vs_allocas id = SOME (b,sz')` (irule_at Any) >>
  qexistsl_tac [`st`, `en`] >> fs[window_alloca_sites_def]
QED
