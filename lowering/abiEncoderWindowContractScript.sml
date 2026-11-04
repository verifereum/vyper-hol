(* Window execution interface. No declared-capacity or instruction-ID budget. *)
Theory abiEncoderWindowContract
Ancestors
  abiEncoderWindow abiEncoderAdmissible abiEncoderRegisteredEffect
  abiEncoderExtendSim allocaSiteResource abiEncoderProps abiDecoderLoop
  fragExec venomState venomExecSemantics venomMemDefs valueEncoding
  valueEncodingProofs finite_map pred_set list words

Definition abi_encoder_window_pre_def:
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s <=>
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    sb + cap <= s.vs_alloca_next /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_window_result_def:
  abi_encoder_window_result ctx func st st' out at av d s t <=>
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (frag_ids st st')
      [(d,LENGTH (enc at av))] s t /\
    alloca_inv t /\ alloca_room ctx func t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func s t
End

Definition abi_encoder_window_contract_def:
  abi_encoder_window_contract ei <=>
    !dst src st out st' ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,st') /\
      abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
      ?t. abi_encoder_window_result ctx func st st' out at av d s t
End

Theorem abi_encoder_window_result_effect:
  abi_encoder_window_result ctx func st st' out at av d s t ==>
  abi_encoder_registered_effect (frag_ids st st') [(d,LENGTH (enc at av))] s t
Proof
  simp[abi_encoder_window_result_def]
QED

Theorem abi_encoder_window_result_resources:
  abi_encoder_window_result ctx func st st' out at av d s t ==>
  alloca_inv t /\ alloca_room ctx func t
Proof
  simp[abi_encoder_window_result_def]
QED

Theorem abi_encoder_window_result_vars:
  abi_encoder_window_result ctx func st st' out at av d s t /\
  not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w
Proof
  simp[abi_encoder_window_result_def] >> metis_tac[]
QED

(* A registered effect has a byte-window frame, independently of how it ran. *)
Theorem abi_encoder_window_effect_bytes:
  abi_encoder_registered_effect ids outs s t /\
  EVERY (\r. venomMemDefs$regions_disjoint (p,n) r) outs /\
  (!id b sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (p,n) (b,sz)) ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  `mem_bytes_at (p + x) 1 t.vs_memory = mem_bytes_at (p + x) 1 s.vs_memory` by
    (qpat_x_assum `!a. _ ==> mem_bytes_at a 1 _ = _`
       (qspec_then `p + x` mp_tac) >>
     (impl_tac >- (conj_tac
     >- (fs[EVERY_MEM] >> rpt strip_tac >>
         rename1 `MEM r outs` >> Cases_on `r` >>
         first_x_assum drule >>
         simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >> first_x_assum drule_all >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)) >> simp[]) >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem abi_encoder_window_effect_parent:
  abi_encoder_registered_effect ids outs s t /\ alloca_inv t /\
  FLOOKUP s.vs_allocas parent = SOME (p,n) /\ parent NOTIN ids /\
  EVERY (\r. venomMemDefs$regions_disjoint (p,n) r) outs ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_effect_bytes >>
  qexistsl_tac [`ids`, `outs`] >> simp[] >> rpt strip_tac >>
  `FLOOKUP t.vs_allocas parent = SOME (p,n)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  irule alloca_site_registered_disjoint >>
  metis_tac[]
QED

Theorem abi_encoder_window_effect_source:
  abi_encoder_registered_effect ids outs s t /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) outs /\
  (!id b sz. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  strip_tac >> drule abi_encoder_window_input_mem_agree >>
  disch_then irule >> irule EQ_SYM >>
  irule abi_encoder_window_effect_bytes >> metis_tac[]
QED

Theorem abi_encoder_window_effect_sequence:
  abi_encoder_registered_effect left left_out s t /\
  abi_encoder_registered_effect right right_out t u /\
  left SUBSET ids /\ right SUBSET ids /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) left_out) /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) right_out) ==>
  abi_encoder_registered_effect ids outs s u
Proof
  strip_tac >> irule abi_encoder_registered_effect_trans >>
  qexists_tac `t` >> conj_tac >>
  irule abi_encoder_registered_effect_enlarge >> metis_tac[]
QED

Theorem abi_encoder_window_effect_suboutput:
  abi_encoder_registered_effect ids [(d + off,len)] s t /\ off + len <= n ==>
  abi_encoder_registered_effect ids [(d,n)] s t
Proof
  strip_tac >> irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`ids`, `[(d + off,len)]`] >> simp[] >>
  rpt strip_tac >> decide_tac
QED

(* A zero-byte child has no output footprint, even at an arbitrary pointer. *)
Theorem abi_encoder_window_effect_empty_output:
  abi_encoder_registered_effect ids [(d,0)] s t ==>
  abi_encoder_registered_effect ids [] s t
Proof
  strip_tac >> irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`ids`, `[(d,0)]`] >> simp[]
QED

Theorem abi_encoder_window_result_control:
  abi_encoder_window_result ctx func st st' out at av d s t ==>
  ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
  t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t
Proof
  simp[abi_encoder_window_result_def]
QED

Theorem abi_encoder_window_result_output:
  abi_encoder_window_result ctx func st st' out at av d s t ==>
  mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av)))
Proof
  simp[abi_encoder_window_result_def]
QED

Theorem abi_encoder_window_pre_resources:
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
  alloca_inv s /\ alloca_room ctx func s /\
  sb + cap <= s.vs_alloca_next /\
  d + LENGTH (enc at av) <= s.vs_alloca_next
Proof
  simp[abi_encoder_window_pre_def]
QED

(* Actual allocation IDs, not every instruction ID in a fragment. *)
Definition window_alloca_sites_def:
  window_alloca_sites func ids =
    {i | i IN ids /\ ?inst. MEM inst (fn_insts func) /\
      inst.inst_opcode = ALLOCA /\ inst.inst_id = i}
End

Definition window_alloca_growth_def:
  window_alloca_growth (s:venom_state) (t:venom_state) <=>
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!i b sz. FLOOKUP s.vs_allocas i = NONE /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> s.vs_alloca_next <= b)
End

Definition window_strong_result_def:
  window_strong_result ctx func st st' out at av d s t <=>
    abi_encoder_window_result ctx func st st' out at av d s t /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
      [(d,LENGTH (enc at av))] s t /\
    window_alloca_growth s t /\
    (!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    abi_encoder_extend_sim ctx func s t /\ t.vs_labels = s.vs_labels
End

Definition window_strong_contract_def:
  window_strong_contract ei <=>
    !dst src st out st' ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,st') /\
      abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
      ?t. window_strong_result ctx func st st' out at av d s t
End

Theorem window_alloca_sites_subset:
  window_alloca_sites func ids SUBSET ids
Proof
  simp[window_alloca_sites_def, SUBSET_DEF]
QED

Theorem window_alloca_sites_mono:
  ids SUBSET more ==> window_alloca_sites func ids SUBSET window_alloca_sites func more
Proof
  simp[window_alloca_sites_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem window_alloca_sites_union:
  window_alloca_sites func (left UNION right) =
    window_alloca_sites func left UNION window_alloca_sites func right
Proof
  simp[window_alloca_sites_def, EXTENSION] >> metis_tac[]
QED

Theorem window_alloca_growth_refl:
  window_alloca_growth s s
Proof
  simp[window_alloca_growth_def] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem window_strong_result_public:
  window_strong_result ctx func st st' out at av d s t ==>
  abi_encoder_window_result ctx func st st' out at av d s t
Proof
  simp[window_strong_result_def]
QED

Theorem window_strong_result_effect:
  window_strong_result ctx func st st' out at av d s t ==>
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,LENGTH (enc at av))] s t
Proof
  simp[window_strong_result_def]
QED

Theorem window_strong_result_growth:
  window_strong_result ctx func st st' out at av d s t ==> window_alloca_growth s t
Proof
  simp[window_strong_result_def]
QED

Theorem window_strong_result_sizes:
  window_strong_result ctx func st st' out at av d s t /\
  i IN window_alloca_sites func (frag_ids st st') /\
  FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32
Proof
  simp[window_strong_result_def] >> metis_tac[]
QED

Theorem window_strong_result_extend:
  window_strong_result ctx func st st' out at av d s t ==>
  abi_encoder_extend_sim ctx func s t
Proof
  simp[window_strong_result_def]
QED

Theorem window_strong_contract_public:
  window_strong_contract ei ==> abi_encoder_window_contract ei
Proof
  simp_tac bool_ss [window_strong_contract_def, abi_encoder_window_contract_def] >>
  metis_tac[window_strong_result_public]
QED

Theorem window_alloca_sites_reuse_iff:
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id IN ids /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,n) (b,sz)) <=>
  (!i b sz. i IN window_alloca_sites func ids /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,n) (b,sz))
Proof
  simp[window_alloca_sites_def] >> metis_tac[]
QED

Theorem window_alloca_growth_trans_counterexample[local]:
  !s:venom_state.
  let a = s with <|vs_alloca_next := 1; vs_allocas := FEMPTY|>;
      b = s with <|vs_alloca_next := 1; vs_allocas := FEMPTY |+ (0,(1,0))|>;
      c = s with <|vs_alloca_next := 1; vs_allocas := FEMPTY |+ (0,(0,0))|>
  in window_alloca_growth a b /\ window_alloca_growth b c /\
     (!i r. FLOOKUP a.vs_allocas i = SOME r ==> FLOOKUP b.vs_allocas i = SOME r) /\
     ~window_alloca_growth a c
Proof
  simp[LET_THM, window_alloca_growth_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> qexistsl_tac [`0`, `0`, `0`] >> simp[]
QED

Theorem window_alloca_growth_trans:
  window_alloca_growth s t /\ window_alloca_growth t u /\
  (!i r. FLOOKUP t.vs_allocas i = SOME r ==> FLOOKUP u.vs_allocas i = SOME r) ==>
  window_alloca_growth s u
Proof
  simp_tac bool_ss [window_alloca_growth_def] >> strip_tac >>
  conj_tac >- decide_tac >> rpt strip_tac >>
  Cases_on `FLOOKUP t.vs_allocas i`
  >- (first_x_assum drule_all >> decide_tac) >>
  rename1 `SOME r` >>
  `FLOOKUP u.vs_allocas i = SOME r` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

Theorem window_alloca_growth_frontier:
  window_alloca_growth s t /\ q + n <= s.vs_alloca_next ==>
  q + n <= t.vs_alloca_next
Proof
  simp[window_alloca_growth_def] >> decide_tac
QED

Theorem window_alloca_growth_protected:
  window_alloca_growth s t /\
  (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r) /\
  q + n <= s.vs_alloca_next /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)) ==>
  (!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz))
Proof
  simp_tac bool_ss [window_alloca_growth_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas i`
  >- (`s.vs_alloca_next <= b` by metis_tac[] >>
      simp[venomMemDefsTheory.regions_disjoint_def]) >>
  rename1 `SOME r` >>
  `FLOOKUP t.vs_allocas i = SOME r` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

Theorem window_alloca_protection_subset:
  small SUBSET ids /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)) ==>
  (!i b sz. i IN small /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz))
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem window_alloca_growth_frame:
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  q + n <= s.vs_alloca_next /\
  EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)) ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_effect_bytes >>
  qexistsl_tac [`ids`, `outs`] >> simp[] >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  rpt strip_tac >> irule window_alloca_growth_protected >>
  qexistsl_tac [`id`, `ids`, `s`, `t`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem window_alloca_growth_source:
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  sb + cap <= s.vs_alloca_next /\
  EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) outs /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  strip_tac >> drule abi_encoder_window_input_mem_agree >>
  disch_then irule >> irule EQ_SYM >>
  irule window_alloca_growth_frame >> metis_tac[]
QED

Theorem window_alloca_growth_sequence:
  abi_encoder_registered_effect left left_out s t /\ window_alloca_growth s t /\
  abi_encoder_registered_effect right right_out t u /\ window_alloca_growth t u /\
  left SUBSET ids /\ right SUBSET ids /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) left_out) /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) right_out) ==>
  abi_encoder_registered_effect ids outs s u /\ window_alloca_growth s u
Proof
  strip_tac >> conj_tac
  >- (irule abi_encoder_window_effect_sequence >> metis_tac[]) >>
  irule window_alloca_growth_trans >> qexists_tac `t` >> simp[] >>
  metis_tac[abi_encoder_registered_effect_allocated]
QED

Theorem window_alloca_growth_fields:
  s.vs_alloca_next = t.vs_alloca_next /\ s.vs_allocas = t.vs_allocas ==>
  window_alloca_growth s t
Proof
  simp[window_alloca_growth_def] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem window_exec_alloca_growth:
  inst.inst_outputs = [out] /\ exec_alloca inst s n = OK t ==>
  window_alloca_growth s t
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (gvs[exec_alloca_def, update_var_def, AllCaseEqs()] >>
      simp[window_alloca_growth_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `i = inst.inst_id` >> gvs[]) >>
  rename1 `SOME r` >> PairCases_on `r` >>
  gvs[exec_alloca_def] >> irule window_alloca_growth_fields >>
  simp[update_var_def]
QED

Theorem window_exec_alloca_effect:
  inst.inst_outputs = [out] /\ exec_alloca inst s n = OK t ==>
  abi_encoder_registered_effect {inst.inst_id} [] s t
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (gvs[exec_alloca_def, update_var_def, AllCaseEqs()] >>
      simp[abi_encoder_registered_effect_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `i = inst.inst_id` >> gvs[]) >>
  rename1 `SOME r` >> PairCases_on `r` >>
  gvs[exec_alloca_def] >>
  simp[abi_encoder_registered_effect_def, update_var_def]
QED

Theorem window_alloca_site32_execute:
  alloca_room ctx func s /\ alloca_inv s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) ==>
  ?t b. exec_alloca inst s (32w:bytes32) = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\ b + 32 <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    window_alloca_growth s t /\
    abi_encoder_registered_effect {inst.inst_id} [] s t
Proof
  strip_tac >> drule_all alloca_site32_execute >> strip_tac >>
  `window_alloca_growth s t` by (drule_all window_exec_alloca_growth >> simp[]) >>
  `abi_encoder_registered_effect {inst.inst_id} [] s t` by
    (drule_all window_exec_alloca_effect >> simp[]) >>
  qexistsl_tac [`t`, `b`] >> simp[]
QED

Theorem window_alloca_site32_protected:
  inst.inst_outputs = [out] /\ exec_alloca inst s (32w:bytes32) = OK t /\
  q + n <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)) ==>
  !b sz. FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)
Proof
  strip_tac >>
  `window_alloca_growth s t` by metis_tac[window_exec_alloca_growth] >>
  `abi_encoder_registered_effect {inst.inst_id} [] s t` by
    metis_tac[window_exec_alloca_effect] >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  rpt strip_tac >> irule window_alloca_growth_protected >>
  qexistsl_tac [`inst.inst_id`, `{inst.inst_id}`, `s`, `t`] >> simp[]
QED

Theorem window_pre_sites:
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s /\
  i IN window_alloca_sites func (frag_ids st st') /\
  FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
  sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
  venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)
Proof
  simp_tac bool_ss [abi_encoder_window_pre_def] >>
  rewrite_tac[window_alloca_sites_reuse_iff] >> metis_tac[]
QED

Theorem window_strong_result_labels:
  window_strong_result ctx func st en out at av d s t ==> t.vs_labels = s.vs_labels
Proof
  simp[window_strong_result_def]
QED
