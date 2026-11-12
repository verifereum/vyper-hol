Theory ctorDeployLoweringEntryResourceRegister
Ancestors
  ctorDeployLoweringEntryRegisterSizes ctorDeployLoweringEntrySeparation
  abiDecoderCode actualDecoderSites fragExec vyperCompiler venomWf
  compileEnv emitHelper venomInst actualDecoderPackaging abiEncoder context moduleLowering localPtrsProps abiEncoderProps ctorAbiActualSites

(* The code certificate and fragment containment do not supply reverse
   membership: a containing function can have an extra instruction in an
   unused identifier slot. This probes the proposed static interface only,
   not the constructor-entry statement. *)
Theorem deploy_ctor_decoder_certificate_membership_gap:
  ?st last func inst.
    abi_decoder_code st last /\ abi_decoder_code_ids_below st /\
    fn_has_code st last func /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    st.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id /\
    ~abi_decoder_code_member inst last
Proof
  qexistsl [`initial_compile_state "entry"`,
    `(initial_compile_state "entry") with cs_next_id := 1`,
    `mk_raw_function "entry"
      [<|bb_label := "entry";
         bb_instructions := [mk_inst 0 ALLOCA [Lit 64w] ["p"]]|>]`,
    `mk_inst 0 ALLOCA [Lit 64w] ["p"]`] >>
  EVAL_TAC >> simp[] >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Theorem deploy_ctor_emit_op_id_coverage:
  !opc ops st aid.
    st.cs_next_id <= aid /\ aid < (SND (emit_op opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_op opc ops st))
Proof
  rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, abi_decoder_code_member_def] >>
  strip_tac >> `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` >> simp[mk_inst_def]
QED

Theorem deploy_ctor_new_block_members_preserved:
  !inst label st.
    abi_decoder_code_member inst (SND (new_block label st)) <=>
    abi_decoder_code_member inst st
Proof
  simp[new_block_def, abi_decoder_code_member_def, EXISTS_OR_THM,
    RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR]
QED

Theorem deploy_ctor_code_member_extends:
  cs_extends st last /\ abi_decoder_code_member inst st ==>
  abi_decoder_code_member inst last
Proof
  metis_tac[decoder_code_member_prefix, decoder_code_member_state_insts]
QED

Theorem deploy_ctor_coverage_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id) /\
  (!v st. cs_extends st (SND (g v st)) /\
    st.cs_next_id <= (SND (g v st)).cs_next_id) /\
  (!st func aid. fn_has_code st (SND (f st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
      MEM inst (fn_insts func)) /\
  (!v st func aid. fn_has_code st (SND (g v st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (g v st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g v st)) /\
      MEM inst (fn_insts func)) ==>
  !st func aid. fn_has_code st (SND (comp_bind f g st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_bind f g st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_bind f g st)) /\
      MEM inst (fn_insts func)
Proof
  strip_tac >> rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >>
  rename1 `f st = (v,mid)` >>
  `cs_extends st mid /\ st.cs_next_id <= mid.cs_next_id` by metis_tac[pairTheory.SND] >>
  `cs_extends mid (SND (g v mid))` by metis_tac[] >>
  `fn_has_code st mid func /\ fn_has_code mid (SND (g v mid)) func` by
    metis_tac[fn_has_code_split] >>
  Cases_on `aid < mid.cs_next_id`
  >- (qpat_x_assum `!st func aid. fn_has_code st (SND (f st)) func /\ _ ==> _`
        (qspecl_then [`st`, `func`, `aid`] mp_tac) >>
      asm_simp_tac (srw_ss()) [] >> strip_tac >>
      qexists `inst` >> metis_tac[deploy_ctor_code_member_extends]) >>
  `mid.cs_next_id <= aid` by decide_tac >> metis_tac[]
QED

Theorem deploy_ctor_current_member_in_function:
  fn_has_code st last func /\ MEM inst last.cs_current_insts ==>
  MEM inst (fn_insts func)
Proof
  simp[fn_has_code_def] >> strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

Theorem deploy_ctor_coverage_emit_op:
  !opc ops st func aid.
    fn_has_code st (SND (emit_op opc ops st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_op opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_op opc ops st)) /\
      MEM inst (fn_insts func)
Proof
  rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` >>
  simp[mk_inst_def, abi_decoder_code_member_def] >>
  irule deploy_ctor_current_member_in_function >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem deploy_ctor_coverage_emit_void:
  !opc ops st func aid.
    fn_has_code st (SND (emit_void opc ops st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_void opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_void opc ops st)) /\
      MEM inst (fn_insts func)
Proof
  rpt gen_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops []` >>
  simp[mk_inst_def, abi_decoder_code_member_def] >>
  irule deploy_ctor_current_member_in_function >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem deploy_ctor_coverage_emit_inst:
  !opc ops outs st func aid.
    fn_has_code st (SND (emit_inst opc ops outs st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_inst opc ops outs st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_inst opc ops outs st)) /\
      MEM inst (fn_insts func)
Proof
  rpt gen_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops outs` >>
  simp[mk_inst_def, abi_decoder_code_member_def] >>
  irule deploy_ctor_current_member_in_function >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem deploy_ctor_coverage_return:
  !v st func aid.
    fn_has_code st (SND (comp_return v st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_return v st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_return v st)) /\ MEM inst (fn_insts func)
Proof
  simp[comp_return_def]
QED

Theorem deploy_ctor_coverage_fresh_label:
  !name st func aid.
    fn_has_code st (SND (fresh_label name st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (fresh_label name st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (fresh_label name st)) /\ MEM inst (fn_insts func)
Proof
  simp[fresh_label_def]
QED

Theorem deploy_ctor_coverage_new_block:
  !name st func aid.
    fn_has_code st (SND (new_block name st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (new_block name st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (new_block name st)) /\ MEM inst (fn_insts func)
Proof
  simp[new_block_def]
QED

Theorem deploy_ctor_coverage_ignore_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id) /\
  (!st. cs_extends st (SND (g st)) /\
    st.cs_next_id <= (SND (g st)).cs_next_id) /\
  (!st func aid. fn_has_code st (SND (f st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
      MEM inst (fn_insts func)) /\
  (!st func aid. fn_has_code st (SND (g st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (g st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g st)) /\
      MEM inst (fn_insts func)) ==>
  !st func aid. fn_has_code st (SND (comp_ignore_bind f g st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_ignore_bind f g st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_ignore_bind f g st)) /\
      MEM inst (fn_insts func)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac deploy_ctor_coverage_bind >> simp[]
QED

Theorem deploy_ctor_emission_extends_ids:
  (!st. cs_extends st (SND (emit_op opc ops st)) /\
    st.cs_next_id <= (SND (emit_op opc ops st)).cs_next_id) /\
  (!st. cs_extends st (SND (emit_void opc ops st)) /\
    st.cs_next_id <= (SND (emit_void opc ops st)).cs_next_id) /\
  (!st. cs_extends st (SND (emit_inst opc ops outs st)) /\
    st.cs_next_id <= (SND (emit_inst opc ops outs st)).cs_next_id)
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
    emit_def, cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem deploy_ctor_no_id_extends:
  (!st. cs_extends st (SND (comp_return v st)) /\
    st.cs_next_id <= (SND (comp_return v st)).cs_next_id) /\
  (!st. cs_extends st (SND (fresh_label name st)) /\
    st.cs_next_id <= (SND (fresh_label name st)).cs_next_id) /\
  (!st. cs_extends st (SND (new_block name st)) /\
    st.cs_next_id <= (SND (new_block name st)).cs_next_id)
Proof
  simp[comp_return_def, fresh_label_def, new_block_def, cs_extends_def,
    rich_listTheory.IS_PREFIX_APPEND] >>
  gen_tac >> qexists `[<|bb_label := st.cs_current_bb;
    bb_instructions := st.cs_current_insts|>]` >> simp[]
QED

(* Internal composition interface: extension and monotonicity travel with
   coverage, so syntax induction has just one premise per child action. *)
Theorem deploy_ctor_covered_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id /\
    !func aid. fn_has_code st (SND (f st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
        MEM inst (fn_insts func)) /\
  (!v st. cs_extends st (SND (g v st)) /\
    st.cs_next_id <= (SND (g v st)).cs_next_id /\
    !func aid. fn_has_code st (SND (g v st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (g v st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g v st)) /\
        MEM inst (fn_insts func)) ==>
  !st. cs_extends st (SND (comp_bind f g st)) /\
    st.cs_next_id <= (SND (comp_bind f g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (comp_bind f g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (comp_bind f g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (comp_bind f g st)) /\ MEM inst (fn_insts func)
Proof
  strip_tac >> gen_tac >> reverse conj_tac
  >- (reverse conj_tac
      >- (qid_spec_tac `st` >> ho_match_mp_tac deploy_ctor_coverage_bind >> metis_tac[]) >>
      simp[comp_bind_def] >> pairarg_tac >> simp[] >>
      metis_tac[pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND, cs_extends_trans]
QED

Theorem deploy_ctor_covered_ignore_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id /\
    !func aid. fn_has_code st (SND (f st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
        MEM inst (fn_insts func)) /\
  (!st. cs_extends st (SND (g st)) /\
    st.cs_next_id <= (SND (g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g st)) /\
        MEM inst (fn_insts func)) ==>
  !st. cs_extends st (SND (comp_ignore_bind f g st)) /\
    st.cs_next_id <= (SND (comp_ignore_bind f g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (comp_ignore_bind f g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (comp_ignore_bind f g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (comp_ignore_bind f g st)) /\ MEM inst (fn_insts func)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac deploy_ctor_covered_bind >> simp[]
QED

val covered_simps = [deploy_ctor_emission_extends_ids,
  deploy_ctor_no_id_extends, deploy_ctor_coverage_emit_op,
  deploy_ctor_coverage_emit_void, deploy_ctor_coverage_emit_inst,
  deploy_ctor_coverage_return, deploy_ctor_coverage_fresh_label,
  deploy_ctor_coverage_new_block];
val covered_db = fn t => ho_match_mp_tac deploy_ctor_covered_bind >>
  conj_tac >- simp (t::covered_simps) >> gen_tac;
val covered_dib = fn t => ho_match_mp_tac deploy_ctor_covered_ignore_bind >>
  conj_tac >- simp (t::covered_simps);

Theorem deploy_ctor_covered_alloc_buffer:
  !sz st. cs_extends st (SND (compile_alloc_buffer sz st)) /\
    st.cs_next_id <= (SND (compile_alloc_buffer sz st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_alloc_buffer sz st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_alloc_buffer sz st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_alloc_buffer sz st)) /\
        MEM inst (fn_insts func)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  covered_db deploy_ctor_coverage_emit_op >> simp covered_simps
QED

Theorem deploy_ctor_covered_clamp:
  !c v st. cs_extends st (SND (compile_abi_clamp_basetype v c st)) /\
    st.cs_next_id <= (SND (compile_abi_clamp_basetype v c st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_clamp_basetype v c st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_clamp_basetype v c st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_clamp_basetype v c st)) /\
        MEM inst (fn_insts func)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def]
  >- simp covered_simps
  >- (gen_tac >> IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
      ntac 2 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps)
  >- (gen_tac >> ntac 2 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
  gen_tac >> ntac 2 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps
QED

Theorem deploy_ctor_covered_static:
  (!v st. cs_extends st (SND (clamp v st)) /\
    st.cs_next_id <= (SND (clamp v st)).cs_next_id /\
    !func aid. fn_has_code st (SND (clamp v st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (clamp v st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (clamp v st)) /\
        MEM inst (fn_insts func)) ==>
  !st. cs_extends st (SND (compile_abi_decode_static src dst opc clamp st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_static src dst opc clamp st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_static src dst opc clamp st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_static src dst opc clamp st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_static src dst opc clamp st)) /\
        MEM inst (fn_insts func)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  covered_db deploy_ctor_coverage_emit_op >>
  covered_dib deploy_ctor_coverage_return >> simp covered_simps
QED

Theorem deploy_ctor_covered_getelemptr:
  !src dyn off opc hi st.
    cs_extends st (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)) /\
    st.cs_next_id <= (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)) /\
        MEM inst (fn_insts func)
Proof
  ntac 5 gen_tac >> rewrite_tac[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  covered_db deploy_ctor_coverage_emit_op >> Cases_on `dyn` >>
  simp covered_simps >> ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp covered_simps >>
      ntac 2 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
  simp covered_simps
QED

Theorem deploy_ctor_covered_dyn_elem_ptr:
  !opc src data hi sz st.
    cs_extends st (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)) /\
        MEM inst (fn_insts func)
Proof
  ntac 5 gen_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp covered_simps >>
      ntac 2 (covered_db deploy_ctor_coverage_emit_op) >>
      covered_dib deploy_ctor_coverage_emit_void >>
      ntac 6 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
  simp covered_simps
QED

(* The bytestring decoder's copy is one emit_void whichever source it
   reads; stating it so avoids splitting on every opcode under coverage. *)
Theorem decode_bytes_copy_emit_void[local]:
  !opc args.
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY args
     | DLOAD => emit_void DLOADBYTES args
     | _ => emit_void MCOPY args) =
    emit_void (case opc of
                 CALLDATALOAD => CALLDATACOPY
               | DLOAD => DLOADBYTES
               | _ => MCOPY) args
Proof
  Cases >> simp[]
QED

Theorem resource_register_covered_decoder_zero_base_mutual[local]:
  (!dst src opc base_op hi info. base_op = Lit 0w /\ opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)) /\
        MEM inst (fn_insts func)) /\
  (!dst src opc base_op hi elems ao vo. base_op = Lit 0w /\ opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)) /\
        MEM inst (fn_insts func)) /\
  (!dst src opc base_op hi ei asz msz ip cnt. base_op = Lit 0w /\ opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)) /\
        MEM inst (fn_insts func))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >> gvs[]
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume resource_register_covered_decoder_zero_base_mutual[word]:
  once_rewrite_tac[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  simp[compile_abi_dec_addr_def, comp_bind_def, comp_return_def] >>
  irule deploy_ctor_covered_static >> simp[deploy_ctor_covered_clamp]
QED
Resume resource_register_covered_decoder_zero_base_mutual[bytes]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac (srw_ss()) [compile_abi_dec_addr_def, LET_THM,
    decode_bytes_copy_emit_void] >>
  ho_match_mp_tac deploy_ctor_covered_bind >> conj_tac
  >- (IF_CASES_TAC >> simp covered_simps >>
      covered_db deploy_ctor_coverage_emit_op >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
      >- (ntac 5 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
      simp covered_simps) >>
  gen_tac >> covered_db deploy_ctor_coverage_return >>
  ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
  covered_dib deploy_ctor_coverage_emit_void >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp covered_simps >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ntac 6 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
  simp (decode_bytes_copy_emit_void :: covered_simps)
QED
Resume resource_register_covered_decoder_zero_base_mutual[array]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac (srw_ss()) [compile_abi_dec_addr_def, LET_THM,
    decode_bytes_copy_emit_void] >>
  ho_match_mp_tac deploy_ctor_covered_bind >> conj_tac
  >- (IF_CASES_TAC >> simp covered_simps >>
      covered_db deploy_ctor_coverage_emit_op >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
      >- (ntac 5 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
      simp covered_simps) >>
  gen_tac >> covered_db deploy_ctor_coverage_return >>
  ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
  covered_dib deploy_ctor_coverage_emit_void >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp covered_simps >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ntac 7 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
  covered_db deploy_ctor_coverage_emit_op >>
  covered_dib deploy_ctor_coverage_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (covered_db deploy_ctor_coverage_emit_op) >>
      covered_db deploy_ctor_coverage_return >>
      covered_db deploy_ctor_coverage_emit_op >> simp covered_simps) >>
  covered_db deploy_ctor_covered_alloc_buffer >> covered_dib deploy_ctor_coverage_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume resource_register_covered_decoder_zero_base_mutual[complex]:
  once_rewrite_tac[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- simp[] >>
  covered_db deploy_ctor_coverage_emit_op >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (rewrite_tac[compile_abi_decode_range_check_def] >>
      ntac 5 (covered_db deploy_ctor_coverage_emit_op) >> simp covered_simps) >>
  simp[]
QED
Resume resource_register_covered_decoder_zero_base_mutual[nil]:
  once_rewrite_tac[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >> simp covered_simps
QED
Resume resource_register_covered_decoder_zero_base_mutual[cons]:
  once_rewrite_tac[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  covered_db deploy_ctor_covered_getelemptr >> covered_db deploy_ctor_coverage_emit_op >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  simp[]
QED
Resume resource_register_covered_decoder_zero_base_mutual[loop]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [compile_abi_dec_addr_def, LET_THM] >> BETA_TAC >>
  ntac 3 (covered_db deploy_ctor_coverage_fresh_label) >>
  covered_dib deploy_ctor_coverage_emit_inst >> covered_dib deploy_ctor_coverage_new_block >>
  covered_db deploy_ctor_coverage_emit_op >>
  covered_db deploy_ctor_coverage_return >>
  ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
  covered_dib deploy_ctor_coverage_emit_inst >> covered_dib deploy_ctor_coverage_new_block >>
  ntac 4 (covered_db deploy_ctor_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_covered_bind >> conj_tac
  >- (IF_CASES_TAC >> simp (deploy_ctor_covered_dyn_elem_ptr::covered_simps)) >>
  gen_tac >> ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  covered_db deploy_ctor_coverage_emit_op >>
  covered_dib deploy_ctor_coverage_emit_void >> covered_dib deploy_ctor_coverage_emit_inst >>
  covered_dib deploy_ctor_coverage_new_block >> simp covered_simps
QED
Finalise resource_register_covered_decoder_zero_base_mutual

Theorem deploy_ctor_covered_decoder_mutual:
  (!dst src opc hi info. opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)) /\
        MEM inst (fn_insts func)) /\
  (!dst src opc hi elems ao vo. opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)) /\
        MEM inst (fn_insts func)) /\
  (!dst src opc hi ei asz msz ip cnt. opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)) /\
        MEM inst (fn_insts func))
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (cj 1 resource_register_covered_decoder_zero_base_mutual) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (cj 2 resource_register_covered_decoder_zero_base_mutual) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule (cj 3 resource_register_covered_decoder_zero_base_mutual) >> simp[]
QED

Theorem deploy_ctor_covered_decode_args:
  !args off. opc <> ALLOCA ==>
  !st. cs_extends st (SND (compile_decode_args ce args off opc hi adj st)) /\
    st.cs_next_id <= (SND (compile_decode_args ce args off opc hi adj st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_decode_args ce args off opc hi adj st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_decode_args ce args off opc hi adj st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_decode_args ce args off opc hi adj st)) /\
        MEM inst (fn_insts func)
Proof
  Induct >> simp[compile_decode_args_def]
  >- simp covered_simps >>
  gen_tac >> PairCases_on `h` >> gen_tac >> strip_tac >>
  once_rewrite_tac[compile_decode_args_def] >>
  Cases_on `h1` >> simp_tac pure_ss [COND_CLAUSES, LET_THM] >> BETA_TAC
  >- suspend "prim"
  >> suspend "compound"
QED
Resume deploy_ctor_covered_decode_args[prim]:
  ntac 2 (covered_db deploy_ctor_coverage_emit_op) >>
  covered_dib deploy_ctor_covered_clamp >>
  ho_match_mp_tac deploy_ctor_covered_ignore_bind >> conj_tac
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp covered_simps >>
      Cases_on `var_location_decode_operand x` >> simp covered_simps) >>
  first_x_assum irule >> simp[]
QED
Resume deploy_ctor_covered_decode_args[compound]:
  Cases_on `h2` >> simp_tac pure_ss [COND_CLAUSES] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[]
  >- (ntac 3 (covered_db deploy_ctor_coverage_emit_op) >>
      covered_dib (cj 1 deploy_ctor_covered_decoder_mutual) >>
      first_x_assum irule >> simp[]) >>
  covered_db deploy_ctor_coverage_emit_op >>
  covered_dib (cj 1 deploy_ctor_covered_decoder_mutual) >>
  first_x_assum irule >> simp[]
QED
Finalise deploy_ctor_covered_decode_args

Theorem deploy_ctor_decode_args_alloca_shape:
  compile_decode_args ce args off opc hi adj st = ((),last) /\
  opc <> ALLOCA /\ abi_decoder_code st last /\ abi_decoder_code_ids_below st /\
  fn_has_code st last func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  st.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id ==>
  inst.inst_operands = [Lit 32w]
Proof
  strip_tac >>
  drule_all (SRULE [] deploy_ctor_covered_decode_args) >> strip_tac >>
  `?site. site.inst_id = inst.inst_id /\ abi_decoder_code_member site last /\
    MEM site (fn_insts func)` by metis_tac[pairTheory.SND] >>
  `site = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[] >>
  drule_all abi_decoder_code_interval_instruction >>
  simp[abi_decoder_alloc_shape_def]
QED

val list_code_simps = [abi_decoder_code_emit_op, abi_decoder_code_emit_void,
  abi_decoder_code_return, abi_decoder_code_clamp, cj 1 abi_decoder_code_mutual];
val list_code_db = fn t => rpt gen_tac >> ho_match_mp_tac abi_decoder_code_bind >>
  conj_tac >- simp (t::list_code_simps) >> rpt strip_tac;
val list_code_dib = fn t => ho_match_mp_tac abi_decoder_code_ignore_bind >>
  conj_tac >- simp (t::list_code_simps) >> rpt strip_tac;

Theorem deploy_ctor_decode_args_code:
  !args off. opc <> ALLOCA ==>
  !st. abi_decoder_code st (SND (compile_decode_args ce args off opc hi adj st))
Proof
  Induct >> simp[compile_decode_args_def, abi_decoder_code_return] >>
  gen_tac >> PairCases_on `h` >> gen_tac >> strip_tac >>
  once_rewrite_tac[compile_decode_args_def] >>
  Cases_on `h1` >> simp_tac pure_ss [COND_CLAUSES, LET_THM] >> BETA_TAC
  >- (ntac 2 (list_code_db abi_decoder_code_emit_op) >>
      list_code_dib abi_decoder_code_clamp >>
      ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
      >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp list_code_simps >>
          Cases_on `var_location_decode_operand x` >> simp list_code_simps) >>
      simp[]) >>
  Cases_on `h2` >> simp_tac pure_ss [COND_CLAUSES] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[]
  >- (ntac 3 (list_code_db abi_decoder_code_emit_op) >>
      list_code_dib (cj 1 abi_decoder_code_mutual) >> simp[]) >>
  list_code_db abi_decoder_code_emit_op >>
  list_code_dib (cj 1 abi_decoder_code_mutual) >> simp[]
QED

Theorem deploy_ctor_decode_args_literal_sizes:
  compile_decode_args ce args off opc hi adj st = ((),last) /\
  opc <> ALLOCA /\ abi_decoder_code st last /\ abi_decoder_code_ids_below st /\
  fn_has_code st last func /\ fn_inst_ids_distinct func /\
  ctor_actual_scratch func (frag_ids st last) 0 s.vs_alloca_next t /\
  abi_encoder_registered_effect (frag_ids st last) outs s t /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  !inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n
Proof
  strip_tac >>
  `!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st last /\ inst.inst_operands = [Lit n] ==>
    w2n n = 32` by
    (rpt strip_tac >>
     `inst.inst_operands = [Lit 32w]` by
       (irule deploy_ctor_decode_args_alloca_shape >>
        gvs[frag_ids_def] >> metis_tac[]) >> gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  drule deploy_ctor_alloca_literal_sizes_frame >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem deploy_ctor_decode_args_actual_literal_sizes:
  compile_decode_args ce args off opc hi adj st = ((),last) /\
  opc <> ALLOCA /\ abi_decoder_code st last /\ abi_decoder_code_ids_below st /\
  fn_has_code st last func /\ fn_inst_ids_distinct func /\
  ctor_actual_scratch func (ctor_actual_sites func (frag_ids st last))
    0 s.vs_alloca_next t /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last)) outs s t /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  !inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n
Proof
  strip_tac >>
  `!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN ctor_actual_sites func (frag_ids st last) /\
    inst.inst_operands = [Lit n] ==> w2n n = 32` by
    (rpt strip_tac >>
     `inst.inst_operands = [Lit 32w]` by
       (irule deploy_ctor_decode_args_alloca_shape >>
        gvs[ctor_actual_sites_def, frag_ids_def] >> metis_tac[]) >> gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  drule deploy_ctor_alloca_literal_sizes_frame >>
  disch_then drule >> simp[] >> metis_tac[]
QED

(* Generated witnesses carry their allocation shape at emission.  Unlike the
   difference certificate, this interface does not inspect initial membership. *)
Theorem deploy_ctor_shape_coverage_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id) /\
  (!v st. cs_extends st (SND (g v st))) /\
  (!st func aid. fn_has_code st (SND (f st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!v st func aid. fn_has_code st (SND (g v st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (g v st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g v st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st func aid. fn_has_code st (SND (comp_bind f g st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_bind f g st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_bind f g st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >> rename1 `f st = (v,mid)` >>
  `cs_extends st mid /\ st.cs_next_id <= mid.cs_next_id` by metis_tac[pairTheory.SND] >>
  `cs_extends mid (SND (g v mid))` by metis_tac[] >>
  `fn_has_code st mid func /\ fn_has_code mid (SND (g v mid)) func` by
    metis_tac[fn_has_code_split] >>
  Cases_on `aid < mid.cs_next_id`
  >- (qpat_x_assum `!st func aid. fn_has_code st (SND (f st)) func /\ _ ==> _`
        (qspecl_then [`st`, `func`, `aid`] mp_tac) >>
      asm_simp_tac (srw_ss()) [] >> strip_tac >>
      qexists `inst` >> metis_tac[deploy_ctor_code_member_extends]) >>
  `mid.cs_next_id <= aid` by decide_tac >> metis_tac[]
QED

Theorem deploy_ctor_shape_coverage_emit_op:
  !opc ops. (opc = ALLOCA ==> ops = [Lit 32w]) ==>
  !st func aid.
    fn_has_code st (SND (emit_op opc ops st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_op opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_op opc ops st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` >>
  simp[mk_inst_def, abi_decoder_code_member_def, abi_decoder_alloc_shape_def] >>
  irule deploy_ctor_current_member_in_function >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem deploy_ctor_shape_coverage_emit_void:
  !opc ops. opc <> ALLOCA ==>
  !st func aid.
    fn_has_code st (SND (emit_void opc ops st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_void opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_void opc ops st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops []` >>
  simp[mk_inst_def, abi_decoder_code_member_def, abi_decoder_alloc_shape_def] >>
  irule deploy_ctor_current_member_in_function >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem deploy_ctor_shape_coverage_emit_inst:
  !opc ops outs. (opc = ALLOCA ==> ops = [Lit 32w] /\ ?out. outs = [out]) ==>
  !st func aid.
    fn_has_code st (SND (emit_inst opc ops outs st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_inst opc ops outs st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_inst opc ops outs st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops outs` >>
  simp[mk_inst_def, abi_decoder_code_member_def, abi_decoder_alloc_shape_def] >>
  irule deploy_ctor_current_member_in_function >>
  goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem deploy_ctor_shape_coverage_return:
  !v st func aid.
    fn_has_code st (SND (comp_return v st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_return v st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_return v st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  simp[comp_return_def]
QED

Theorem deploy_ctor_shape_coverage_fresh_label:
  !name st func aid.
    fn_has_code st (SND (fresh_label name st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (fresh_label name st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (fresh_label name st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  simp[fresh_label_def]
QED

Theorem deploy_ctor_shape_coverage_new_block:
  !name st func aid.
    fn_has_code st (SND (new_block name st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (new_block name st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (new_block name st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  simp[new_block_def]
QED

Theorem deploy_ctor_shape_covered_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id /\
    !func aid. fn_has_code st (SND (f st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!v st. cs_extends st (SND (g v st)) /\
    st.cs_next_id <= (SND (g v st)).cs_next_id /\
    !func aid. fn_has_code st (SND (g v st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (g v st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g v st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st. cs_extends st (SND (comp_bind f g st)) /\
    st.cs_next_id <= (SND (comp_bind f g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (comp_bind f g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (comp_bind f g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (comp_bind f g st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> gen_tac >> reverse conj_tac
  >- (reverse conj_tac
      >- (qid_spec_tac `st` >> ho_match_mp_tac deploy_ctor_shape_coverage_bind >> metis_tac[]) >>
      simp[comp_bind_def] >> pairarg_tac >> simp[] >>
      metis_tac[pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND, cs_extends_trans]
QED

Theorem deploy_ctor_shape_covered_ignore_bind:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id /\
    !func aid. fn_has_code st (SND (f st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!st. cs_extends st (SND (g st)) /\
    st.cs_next_id <= (SND (g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st. cs_extends st (SND (comp_ignore_bind f g st)) /\
    st.cs_next_id <= (SND (comp_ignore_bind f g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (comp_ignore_bind f g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (comp_ignore_bind f g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (comp_ignore_bind f g st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac deploy_ctor_shape_covered_bind >> simp[]
QED

val shape_simps = [deploy_ctor_emission_extends_ids,
  deploy_ctor_no_id_extends, deploy_ctor_shape_coverage_emit_op,
  deploy_ctor_shape_coverage_emit_void, deploy_ctor_shape_coverage_emit_inst,
  deploy_ctor_shape_coverage_return, deploy_ctor_shape_coverage_fresh_label,
  deploy_ctor_shape_coverage_new_block];
val shape_db = fn t => ho_match_mp_tac deploy_ctor_shape_covered_bind >>
  conj_tac >- simp (t::shape_simps) >> gen_tac;
val shape_dib = fn t => ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >>
  conj_tac >- simp (t::shape_simps);

Theorem deploy_ctor_shape_covered_alloc_buffer:
  !st. cs_extends st (SND (compile_alloc_buffer 32 st)) /\
    st.cs_next_id <= (SND (compile_alloc_buffer 32 st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_alloc_buffer 32 st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_alloc_buffer 32 st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_alloc_buffer 32 st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  shape_db deploy_ctor_shape_coverage_emit_op >> simp shape_simps
QED

Theorem deploy_ctor_shape_covered_clamp:
  !c v st. cs_extends st (SND (compile_abi_clamp_basetype v c st)) /\
    st.cs_next_id <= (SND (compile_abi_clamp_basetype v c st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_clamp_basetype v c st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_clamp_basetype v c st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_clamp_basetype v c st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def]
  >- simp shape_simps
  >- (gen_tac >> IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
      ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps)
  >- (gen_tac >> ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
  gen_tac >> ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps
QED

Theorem deploy_ctor_shape_covered_static:
  opc <> ALLOCA /\
  (!v st. cs_extends st (SND (clamp v st)) /\
    st.cs_next_id <= (SND (clamp v st)).cs_next_id /\
    !func aid. fn_has_code st (SND (clamp v st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (clamp v st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (clamp v st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st. cs_extends st (SND (compile_abi_decode_static src dst opc clamp st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_static src dst opc clamp st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_static src dst opc clamp st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_static src dst opc clamp st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_static src dst opc clamp st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  shape_db deploy_ctor_shape_coverage_emit_op >>
  shape_dib deploy_ctor_shape_coverage_return >> simp shape_simps
QED

Theorem deploy_ctor_shape_covered_getelemptr:
  !src dyn off opc hi. opc <> ALLOCA ==> !st.
    cs_extends st (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)) /\
    st.cs_next_id <= (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_getelemptr_abi src dyn off opc (Lit 0w) hi st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  ntac 5 gen_tac >> strip_tac >> rewrite_tac[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  shape_db deploy_ctor_shape_coverage_emit_op >> Cases_on `dyn` >>
  simp shape_simps >> ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
  simp shape_simps
QED

Theorem deploy_ctor_shape_covered_dyn_elem_ptr:
  !opc src data hi sz. opc <> ALLOCA ==> !st.
    cs_extends st (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_elem_ptr opc (Lit 0w) src data hi sz st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  ntac 5 gen_tac >> strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >>
  ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >>
      shape_dib deploy_ctor_shape_coverage_emit_void >>
      ntac 6 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
  simp shape_simps
QED

Theorem resource_register_shape_covered_decoder_zero_base_mutual[local]:
  (!dst src opc base_op hi info. base_op = Lit 0w /\ opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_to_buf dst src opc base_op hi info st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!dst src opc base_op hi elems ao vo. base_op = Lit 0w /\ opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!dst src opc base_op hi ei asz msz ip cnt. base_op = Lit 0w /\ opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst)
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >> gvs[]
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume resource_register_shape_covered_decoder_zero_base_mutual[word]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compile_abi_dec_addr_def, comp_bind_def, comp_return_def] >>
  irule deploy_ctor_shape_covered_static >> simp[deploy_ctor_shape_covered_clamp]
QED
Resume resource_register_shape_covered_decoder_zero_base_mutual[bytes]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac (srw_ss()) [compile_abi_dec_addr_def, LET_THM,
    decode_bytes_copy_emit_void] >>
  ho_match_mp_tac deploy_ctor_shape_covered_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      shape_db deploy_ctor_shape_coverage_emit_op >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
      >- (ntac 5 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
      simp shape_simps) >>
  gen_tac >> shape_db deploy_ctor_shape_coverage_return >>
  ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  shape_dib deploy_ctor_shape_coverage_emit_void >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ntac 6 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
  Cases_on `opc` >> simp (decode_bytes_copy_emit_void :: shape_simps)
QED
Resume resource_register_shape_covered_decoder_zero_base_mutual[array]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac (srw_ss()) [compile_abi_dec_addr_def, LET_THM,
    decode_bytes_copy_emit_void] >>
  ho_match_mp_tac deploy_ctor_shape_covered_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      shape_db deploy_ctor_shape_coverage_emit_op >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
      >- (ntac 5 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
      simp shape_simps) >>
  gen_tac >> shape_db deploy_ctor_shape_coverage_return >>
  ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  shape_dib deploy_ctor_shape_coverage_emit_void >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      rewrite_tac[compile_abi_decode_range_check_def] >>
      ntac 7 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
  shape_db deploy_ctor_shape_coverage_emit_op >>
  shape_dib deploy_ctor_shape_coverage_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >>
      shape_db deploy_ctor_shape_coverage_return >>
      shape_db deploy_ctor_shape_coverage_emit_op >>
      Cases_on `opc` >> simp shape_simps) >>
  shape_db deploy_ctor_shape_covered_alloc_buffer >> shape_dib deploy_ctor_shape_coverage_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume resource_register_shape_covered_decoder_zero_base_mutual[complex]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- simp[] >>
  shape_db deploy_ctor_shape_coverage_emit_op >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (rewrite_tac[compile_abi_decode_range_check_def] >>
      ntac 5 (shape_db deploy_ctor_shape_coverage_emit_op) >> simp shape_simps) >>
  simp[]
QED
Resume resource_register_shape_covered_decoder_zero_base_mutual[nil]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp shape_simps
QED
Resume resource_register_shape_covered_decoder_zero_base_mutual[cons]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  shape_db deploy_ctor_shape_covered_getelemptr >> shape_db deploy_ctor_shape_coverage_emit_op >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  simp[]
QED
Resume resource_register_shape_covered_decoder_zero_base_mutual[loop]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [compile_abi_dec_addr_def, LET_THM] >> BETA_TAC >>
  ntac 3 (shape_db deploy_ctor_shape_coverage_fresh_label) >>
  shape_dib deploy_ctor_shape_coverage_emit_inst >> shape_dib deploy_ctor_shape_coverage_new_block >>
  shape_db deploy_ctor_shape_coverage_emit_op >>
  shape_db deploy_ctor_shape_coverage_return >>
  ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  shape_dib deploy_ctor_shape_coverage_emit_inst >> shape_dib deploy_ctor_shape_coverage_new_block >>
  ntac 4 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_shape_covered_bind >> conj_tac
  >- (IF_CASES_TAC >> simp (deploy_ctor_shape_covered_dyn_elem_ptr::shape_simps)) >>
  gen_tac >> ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  shape_db deploy_ctor_shape_coverage_emit_op >>
  shape_dib deploy_ctor_shape_coverage_emit_void >> shape_dib deploy_ctor_shape_coverage_emit_inst >>
  shape_dib deploy_ctor_shape_coverage_new_block >> simp shape_simps
QED
Finalise resource_register_shape_covered_decoder_zero_base_mutual

Theorem deploy_ctor_shape_covered_decoder_mutual:
  (!dst src opc hi info. opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_to_buf dst src opc (Lit 0w) hi info st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!dst src opc hi elems ao vo. opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!dst src opc hi ei asz msz ip cnt. opc <> ALLOCA ==>
    !st. cs_extends st (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_loop dst src opc (Lit 0w) hi ei asz msz ip cnt st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst)
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (cj 1 resource_register_shape_covered_decoder_zero_base_mutual) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (cj 2 resource_register_shape_covered_decoder_zero_base_mutual) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule (cj 3 resource_register_shape_covered_decoder_zero_base_mutual) >> simp[]
QED

Theorem deploy_ctor_shape_covered_decode_args:
  !args off. opc <> ALLOCA ==>
  !st. cs_extends st (SND (compile_decode_args ce args off opc hi adj st)) /\
    st.cs_next_id <= (SND (compile_decode_args ce args off opc hi adj st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_decode_args ce args off opc hi adj st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_decode_args ce args off opc hi adj st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_decode_args ce args off opc hi adj st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  Induct >> simp[compile_decode_args_def]
  >- simp shape_simps >>
  gen_tac >> PairCases_on `h` >> gen_tac >> strip_tac >>
  once_rewrite_tac[compile_decode_args_def] >>
  Cases_on `h1` >> simp_tac pure_ss [COND_CLAUSES, LET_THM] >> BETA_TAC
  >- suspend "prim"
  >> suspend "compound"
QED
Resume deploy_ctor_shape_covered_decode_args[prim]:
  ntac 2 (shape_db deploy_ctor_shape_coverage_emit_op) >>
  shape_dib deploy_ctor_shape_covered_clamp >>
  ho_match_mp_tac deploy_ctor_shape_covered_ignore_bind >> conj_tac
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp shape_simps >>
      Cases_on `var_location_decode_operand x` >> simp shape_simps) >>
  first_x_assum irule >> simp[]
QED
Resume deploy_ctor_shape_covered_decode_args[compound]:
  Cases_on `h2` >> simp_tac pure_ss [COND_CLAUSES] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[]
  >- (ntac 3 (shape_db deploy_ctor_shape_coverage_emit_op) >>
      shape_dib (cj 1 deploy_ctor_shape_covered_decoder_mutual) >>
      first_x_assum irule >> simp[]) >>
  shape_db deploy_ctor_shape_coverage_emit_op >>
  shape_dib (cj 1 deploy_ctor_shape_covered_decoder_mutual) >>
  first_x_assum irule >> simp[]
QED
Finalise deploy_ctor_shape_covered_decode_args

Theorem deploy_ctor_generated_decode_args_alloca_shape:
  compile_decode_args ce args off opc hi adj st = ((),last) /\
  opc <> ALLOCA /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  st.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id ==>
  inst.inst_operands = [Lit 32w]
Proof
  strip_tac >>
  drule_all (SRULE [] deploy_ctor_shape_covered_decode_args) >> strip_tac >>
  `?site. site.inst_id = inst.inst_id /\ MEM site (fn_insts func) /\
    abi_decoder_alloc_shape site` by metis_tac[pairTheory.SND] >>
  `site = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[abi_decoder_alloc_shape_def]
QED

Theorem deploy_ctor_generated_decode_args_literal_sizes:
  compile_decode_args ce args off opc hi adj st = ((),last) /\
  opc <> ALLOCA /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
  ctor_actual_scratch func (frag_ids st last) 0 s.vs_alloca_next t /\
  abi_encoder_registered_effect (frag_ids st last) outs s t /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  !inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n
Proof
  strip_tac >>
  `!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st last /\ inst.inst_operands = [Lit n] ==>
    w2n n = 32` by
    (rpt strip_tac >>
     `inst.inst_operands = [Lit 32w]` by
       (irule deploy_ctor_generated_decode_args_alloca_shape >>
        gvs[frag_ids_def] >> metis_tac[]) >>
     gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  drule deploy_ctor_alloca_literal_sizes_frame >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem deploy_ctor_generated_decode_args_actual_literal_sizes:
  compile_decode_args ce args off opc hi adj st = ((),last) /\
  opc <> ALLOCA /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
  ctor_actual_scratch func (ctor_actual_sites func (frag_ids st last))
    0 s.vs_alloca_next t /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last)) outs s t /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  !inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n
Proof
  strip_tac >>
  `!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN ctor_actual_sites func (frag_ids st last) /\
    inst.inst_operands = [Lit n] ==> w2n n = 32` by
    (rpt strip_tac >>
     `inst.inst_operands = [Lit 32w]` by
       (irule deploy_ctor_generated_decode_args_alloca_shape >>
        gvs[ctor_actual_sites_def, frag_ids_def] >> metis_tac[]) >>
     gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  drule deploy_ctor_alloca_literal_sizes_frame >>
  disch_then drule >> simp[] >> metis_tac[]
QED
