Theory exprSimAbiDecodeResourcePrims
Ancestors
  exprSimAbiDecodeResource abiEncoder context emitHelper venomInst compileEnv emitHelperProps pred_set exprSimAbiDecodeTrace exprSimAbiDecodeTraceSafe

(* Straight-line contracts retain the entire caller's label pool. *)
Definition decode_straight_def:
  decode_straight ex m post <=>
    !s P. P SUBSET decode_label_range 0 s.cs_next_label ==>
      ?x t. decode_resource_run ex P m s x t P /\ post x
End

Theorem decode_straight_return:
  post x ==> decode_straight ex (comp_return x) post
Proof
  rw[decode_straight_def] >> qexistsl_tac [`x`, `s`] >>
  simp[decode_resource_run_return]
QED

Theorem decode_straight_bind:
  decode_straight ex m mid /\
  (!x. mid x ==> decode_straight ex (f x) post) ==>
  decode_straight ex (comp_bind m f) post
Proof
  rw[decode_straight_def] >>
  first_x_assum drule >> strip_tac >>
  `P SUBSET decode_label_range 0 t.cs_next_label` by
    (drule decode_resource_run_pool >> simp[]) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexistsl_tac [`x'`, `t'`] >> simp[] >>
  irule decode_resource_run_bind >> metis_tac[]
QED

Theorem decode_straight_ignore_bind:
  decode_straight ex m mid /\ decode_straight ex n post ==>
  decode_straight ex (comp_ignore_bind m n) post
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `mid` >> simp[]
QED

Theorem decode_straight_emit_op:
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
  ~MEM (Label ex) ops ==>
  decode_straight ex (emit_op opc ops) (\v. v <> Label ex)
Proof
  rw[decode_straight_def] >>
  irule_at Any decode_resource_emit_op >> simp[]
QED

Theorem decode_straight_emit_void:
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
  ~MEM (Label ex) ops ==>
  decode_straight ex (emit_void opc ops) (\v. T)
Proof
  rw[decode_straight_def] >>
  irule_at Any decode_resource_emit_void >> simp[]
QED

Theorem decode_straight_dec_addr:
  base_op <> Label ex /\ pos <> Label ex ==>
  decode_straight ex (compile_abi_dec_addr base_op pos) (\v. v <> Label ex)
Proof
  rw[compile_abi_dec_addr_def] >>
  simp[decode_straight_return, decode_straight_emit_op]
QED

Theorem decode_straight_alloc_buffer:
  decode_straight ex (compile_alloc_buffer sz) (\b. b.buf_operand <> Label ex)
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >>
  simp[decode_straight_return]
QED

Theorem decode_straight_int_clamp:
  v <> Label ex ==>
  decode_straight ex (compile_abi_int_clamp v bits signed) (\u. T)
Proof
  Cases_on `signed` >> simp[compile_abi_int_clamp_def] >> strip_tac >>
  (match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
   conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
   match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
   conj_tac >- simp[decode_straight_emit_op] >>
   simp[decode_straight_emit_void])
QED

Theorem decode_straight_bytes_clamp:
  v <> Label ex ==>
  decode_straight ex (compile_abi_bytes_clamp v m) (\u. T)
Proof
  rw[compile_abi_bytes_clamp_def] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >>
  simp[decode_straight_emit_void]
QED

Theorem decode_straight_clamp_basetype:
  v <> Label ex ==>
  decode_straight ex (compile_abi_clamp_basetype v c) (\u. T)
Proof
  strip_tac >> Cases_on `c` >> rewrite_tac[compile_abi_clamp_basetype_def]
  >- (irule decode_straight_return >> simp[])
  >- simp[decode_straight_int_clamp]
  >- simp[decode_straight_bytes_clamp] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >>
  simp[decode_straight_emit_void]
QED

Theorem decode_straight_static:
  src <> Label ex /\ dst <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
  (!v. v <> Label ex ==> decode_straight ex (clamp v) (\u. T)) ==>
  decode_straight ex (compile_abi_decode_static src dst opc clamp) (\u. T)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_ignore_bind) >> qexists_tac `\u. T` >>
  simp[decode_straight_emit_void]
QED

Theorem decode_straight_range_check:
  start <> Label ex /\ end_op <> Label ex /\ hi <> Label ex ==>
  decode_straight ex (compile_abi_decode_range_check start end_op hi) (\u. T)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_range_check_def] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >>
  simp[decode_straight_emit_void]
QED

Theorem decode_straight_getelemptr:
  src <> Label ex /\ base_op <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN ==>
  decode_straight ex (compile_getelemptr_abi src dyn off opc base_op hi)
    (\v. v <> Label ex)
Proof
  strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  reverse (Cases_on `dyn`) >> simp[]
  >- simp[decode_straight_return] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_dec_addr] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_ignore_bind) >> qexists_tac `\u. T` >>
  reverse conj_tac >- simp[decode_straight_return] >>
  Cases_on `hi = Lit 0w` >> simp[]
  >- (irule decode_straight_return >> simp[]) >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >>
  simp[decode_straight_emit_void]
QED

Theorem decode_straight_dyn_elem_ptr:
  base_op <> Label ex /\ elem_src <> Label ex /\ src_data <> Label ex /\ hi <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN ==>
  decode_straight ex (compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi sz)
    (\v. v <> Label ex)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_dec_addr] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_ignore_bind) >> qexists_tac `\u. T` >>
  reverse conj_tac >- simp[decode_straight_return] >>
  Cases_on `hi = Lit 0w` >> simp[]
  >- (irule decode_straight_return >> simp[]) >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >> rpt strip_tac >> gvs[] >>
  match_mp_tac (GEN_ALL decode_straight_ignore_bind) >> qexists_tac `\u. T` >>
  conj_tac >- simp[decode_straight_emit_void] >>
  match_mp_tac (GEN_ALL decode_straight_bind) >> qexists_tac `\v. v <> Label ex` >>
  conj_tac >- simp[decode_straight_emit_op] >>
  simp[decode_straight_range_check]
QED

Theorem decode_resource_reserved_switch:
  decode_resource_run ex P m s x u Q /\ P SUBSET Q /\ l IN P ==>
  decode_resource_run ex P
    (comp_ignore_bind m (comp_ignore_bind (new_block l) (comp_return ())))
    s () (decode_step (DecodeSwitch l) u) (Q DELETE l)
Proof
  strip_tac >> irule decode_resource_run_ignore_bind >>
  qexistsl_tac [`Q`, `u`, `x`] >> simp[] >>
  irule decode_resource_switch >>
  drule decode_resource_run_pool >> fs[SUBSET_DEF]
QED

Theorem decode_resource_reserved_terminator:
  decode_resource_run ex P m s x u Q /\ P SUBSET Q /\ l IN P /\
  (opc = JMP \/ opc = JNZ) ==>
  decode_resource_run ex P
    (comp_ignore_bind m (comp_ignore_bind (emit_inst opc ops [])
      (comp_ignore_bind (new_block l) (comp_return ())))) s ()
    (decode_step (DecodeSwitch l)
      (u with <|cs_next_id := u.cs_next_id + 1;
        cs_current_insts := u.cs_current_insts ++ [mk_inst u.cs_next_id opc ops []]|>))
    (Q DELETE l)
Proof
  strip_tac >> irule decode_resource_run_ignore_bind >>
  qexistsl_tac [`Q`, `u`, `x`] >> simp[] >>
  irule decode_resource_terminator_switch >>
  drule decode_resource_run_pool >> fs[SUBSET_DEF]
QED

Theorem decode_resource_no_switch_safe:
  decode_resource_run ex P m s x t Q ==>
  ?es. m s = (x,t) /\ t = decode_history t (decode_replay es s) /\
    decode_trace_safe s.cs_next_id t.cs_next_id (decode_switches es) ex es /\
    (decode_switches es = [] ==>
      EVERY (\i. ~MEM (Label ex) i.inst_operands) (decode_instructions es))
Proof
  strip_tac >> drule decode_resource_run_trace >> strip_tac >>
  qexists_tac `es` >> fs[decode_trace_safe_def]
QED

Theorem decode_resource_two_switches:
  P SUBSET decode_label_range 0 s.cs_next_label /\
  hdr IN P /\ exit IN P /\ hdr <> exit /\ decode_straight ex m post ==>
  ?t. decode_resource_run ex P
    (comp_ignore_bind (comp_ignore_bind (new_block hdr) (comp_return ()))
      (comp_ignore_bind m (comp_ignore_bind (emit_inst JMP [Label hdr] [])
        (comp_ignore_bind (new_block exit) (comp_return ())))))
    s () t ((P DELETE hdr) DELETE exit)
Proof
  strip_tac >>
  `decode_resource_run ex P
    (comp_ignore_bind (new_block hdr) (comp_return ())) s ()
    (decode_step (DecodeSwitch hdr) s) (P DELETE hdr)` by
    (irule decode_resource_switch >> simp[]) >>
  drule decode_resource_run_pool >> strip_tac >>
  qpat_x_assum `decode_straight _ _ _` mp_tac >>
  rewrite_tac[decode_straight_def] >>
  disch_then (qspecl_then [`decode_step (DecodeSwitch hdr) s`, `P DELETE hdr`] mp_tac) >>
  simp[] >> strip_tac >>
  `exit IN P DELETE hdr` by simp[] >>
  drule decode_resource_reserved_terminator >>
  disch_then (qspecl_then [`[Label hdr]`, `JMP`, `exit`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decode_resource_run_ignore_bind >>
  metis_tac[]
QED

(* The three loop labels have all been reserved before the first switch.
   The middle label remains available; the body cannot spend the exit. *)
Theorem decode_resource_reserved_loop_example:
  s.cs_next_label = n + 3 /\ decode_straight ex m post ==>
  ?t. decode_resource_run ex (decode_label_range n (n + 3))
    (comp_ignore_bind
      (comp_ignore_bind (new_block (fresh_label_output "hdr" n)) (comp_return ()))
      (comp_ignore_bind m
        (comp_ignore_bind (emit_inst JMP [Label (fresh_label_output "hdr" n)] [])
          (comp_ignore_bind (new_block (fresh_label_output "exit" (n + 2)))
            (comp_return ()))))) s () t
    ((decode_label_range n (n + 3) DELETE fresh_label_output "hdr" n)
       DELETE fresh_label_output "exit" (n + 2))
Proof
  strip_tac >> match_mp_tac (GEN_ALL decode_resource_two_switches) >>
  qexists_tac `post` >> simp[] >>
  conj_tac
  >- (rw[SUBSET_DEF, decode_label_range_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[decode_label_range_def] >> qexistsl_tac [`"hdr"`, `n`] >> simp[]) >>
  conj_tac
  >- (simp[decode_label_range_def] >> qexistsl_tac [`"exit"`, `n + 2`] >> simp[]) >>
  strip_tac >> drule fresh_label_output_inj >> simp[]
QED
