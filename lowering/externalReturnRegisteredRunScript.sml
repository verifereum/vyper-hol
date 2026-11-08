(* Execute an ABI encoder using allocation-site ownership. No ghost execution
   of the encoder is asserted by this ordinary-execution boundary. *)
Theory externalReturnRegisteredRun
Ancestors externalReturnAllocPtr abiEncoderWindowRun allocaSiteResource

Theorem registered_window_geometry[local]:
  alloca_inv initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_size) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_cap <= source_size /\ output_cap <= output_size /\ source_id <> output_id ==>
  sb + source_cap <= initial.vs_alloca_next /\
  d + output_cap <= initial.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,source_cap) (d,output_cap)
Proof
  strip_tac >>
  `sb + source_size <= initial.vs_alloca_next` by
    (irule alloca_site_registered_below >> metis_tac[]) >>
  `d + output_size <= initial.vs_alloca_next` by
    (irule alloca_site_registered_below >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (sb,source_size) (d,output_size)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem compile_abi_encode_to_buf_registered_window_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_inv initial /\ alloca_room ctx func initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_size) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_cap <= source_size /\ LENGTH (enc at av) <= output_size /\
  source_id <> output_id /\ source_id NOTIN frag_ids st st' /\
  output_id NOTIN frag_ids st st' /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (frag_ids st st')
      [(d,LENGTH (enc at av))] initial actual /\
    alloca_inv actual /\ alloca_room ctx func actual /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  drule_all registered_window_geometry >> strip_tac >>
  irule compile_abi_encode_to_buf_window_run >> asm_rewrite_tac[] >>
  qexistsl_tac [`dst`, `ei`, `sb`, `source_cap`, `src`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `source_id <> inst.inst_id /\ output_id <> inst.inst_id` by metis_tac[] >>
  `sz = 32` by metis_tac[] >> asm_rewrite_tac[] >>
  conj_tac >-
    (irule (cj 3 registered_window_geometry) >>
     qexistsl_tac [`initial`, `inst.inst_id`, `sz`, `source_id`, `source_size`] >> simp[]) >>
  irule (cj 3 registered_window_geometry) >>
  qexistsl_tac [`initial`, `inst.inst_id`, `sz`, `output_id`, `output_size`] >> simp[]
QED

Theorem compile_alloc_buffer_registered_encoder_run:
  compile_alloc_buffer n sa = (buf,sb) /\
  compile_abi_encode_to_buf buf.buf_operand (Var src) ei sb = (len,sd) /\
  fn_has_code sa sd func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword(:256) /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  p+cap <= s.vs_alloca_next /\ val_wf tv v /\ val_footprint tv v <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = n /\ (p+cap <= b \/ b+n <= p)) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av p source_cap s.vs_memory /\
  FLOOKUP s.vs_allocas source_id = SOME (p,source_size) /\
  source_cap <= source_size /\ LENGTH (enc at av) <= n /\
  source_id <> sa.cs_next_id /\ source_id NOTIN frag_ids sb sd /\
  sa.cs_next_id NOTIN frag_ids sb sd /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids sb sd /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out b G1 tn1 sf actual.
    buf.buf_operand = Var out /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g = G /\ t = tn /\ w = s)
      (\g t w. g = G1 /\ t = tn1 /\ w = sf) R /\
    eval_operand (Var out) sf = SOME (n2w b) /\ ptr_covers G1 tn1 out sf n /\
    (p+cap <= b \/ b+n <= p) /\ eval_operand (Var src) sf = SOME (n2w p) /\
    (!mem. mem_agree_outside tn1.t_mem sf.vs_memory mem ==> val_in_memory tv v p mem) /\
    (!q k. not_fresh_at sa q /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q sf k) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
    alloca_inv sf /\ alloca_room ctx func sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (b,n) /\
    b+n <= sf.vs_alloca_next /\ s.vs_alloca_next <= sf.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (q,sz)) /\
    sf.vs_memory = s.vs_memory /\
    (!aid. aid <> sa.cs_next_id ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_bytes_at b (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (frag_ids sb sd)
      [(b,LENGTH (enc at av))] sf actual /\
    alloca_inv actual /\ alloca_room ctx func actual /\
    (!x w. not_fresh_at sb x /\ lookup_var x sf = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sd.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sd.cs_current_insts /\
    abi_decode_sim ctx func sf actual
Proof
  strip_tac >>
  `cs_extends sa sb` by (drule loweringHaltTheory.compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends sb sd` by (drule loweringHaltTheory.compile_abi_encode_to_buf_extends >> simp[]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  drule_all protectedAllocCorePtrTheory.compile_alloc_buffer_protected_source_core_ptr >>
  disch_then (qspecl_then [`cx`, `R`, `PG`, `G`] strip_assume_tac) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids sb sd /\
    FLOOKUP sf.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32` by
    (rpt strip_tac >>
     `inst.inst_id <> sa.cs_next_id` by metis_tac[] >>
     qpat_x_assum `!aid. aid <> _ ==> _` (qspec_then `inst.inst_id` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_then SUBST_ALL_TAC >>
     qpat_x_assum `!inst b sz. _` irule >>
     qexistsl_tac [`b'`, `inst`] >> asm_rewrite_tac[]) >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  `not_fresh_at sb src` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) []) >>
  `!x. Var src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sb x` by
    (asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM] >>
     asm_rewrite_tac[]) >>
  `~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (asm_rewrite_tac[] >> simp_tac (srw_ss()) [listTheory.LENGTH_APPEND] >> decide_tac) >>
  `abi_encoder_window_input ei at av p source_cap sf.vs_memory` by asm_rewrite_tac[] >>
  `FLOOKUP sf.vs_allocas source_id = SOME (p,source_size)` by
    (qpat_x_assum `!aid q sz. _` (qspecl_then [`source_id`, `p`, `source_size`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `eval_operand buf.buf_operand sf = SOME (n2w b)` by
    (qpat_x_assum `buf.buf_operand = Var p'` mp_tac >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
     disch_then SUBST_ALL_TAC >> asm_rewrite_tac[]) >>
  drule_all compile_abi_encode_to_buf_registered_window_run >> strip_tac >>
  qexistsl_tac [`out`, `b`, `G1`, `tn1`, `sf`, `actual`] >> asm_rewrite_tac[] >>
  qpat_x_assum `buf.buf_operand = Var p'` mp_tac >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [boolTheory.EQ_SYM_EQ]
QED
