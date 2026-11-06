Theory placeMemoryCopyEffect
Ancestors
  placeMemoryForwardPath placeMemoryCopyFrames compileEnv emitHelperProps
  venomState fragGasMode freshWrites valueEncoding

(* The shared execution/frame result; value semantics deliberately stay outside. *)
Definition typed_copy_effect_def:
  typed_copy_effect ctx func sa sb s t d n <=>
    gas_marked_path F ctx func s 0 (OK t) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\
    (!a len. a + len <= d \/ d + n <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem typed_copy_effect_path:
  typed_copy_effect ctx func sa sb s t d n ==>
  gas_marked_path F ctx func s 0 (OK t)
Proof
  simp[typed_copy_effect_def]
QED

Theorem typed_copy_effect_record:
  typed_copy_effect ctx func sa sb s t d n ==>
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
            vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  simp[typed_copy_effect_def]
QED

Theorem typed_copy_effect_lookup:
  typed_copy_effect ctx func sa sb s t d n /\ not_fresh_at sa x ==>
  lookup_var x t = lookup_var x s
Proof
  simp[typed_copy_effect_def]
QED

Theorem typed_copy_effect_bytes:
  typed_copy_effect ctx func sa sb s t d n /\
  (a + len <= d \/ d + n <= a) ==>
  mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory
Proof
  simp[typed_copy_effect_def] >> metis_tac[]
QED

Theorem typed_copy_effect_allocas:
  typed_copy_effect ctx func sa sb s t d n ==> t.vs_allocas = s.vs_allocas
Proof
  simp[typed_copy_effect_def]
QED

Theorem typed_copy_effect_length:
  typed_copy_effect ctx func sa sb s t d n ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp[typed_copy_effect_def]
QED

Theorem typed_copy_effect_endpoint:
  typed_copy_effect ctx func sa sb s t d n ==>
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[typed_copy_effect_def]
QED

Theorem typed_copy_effect_identity:
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  typed_copy_effect ctx func sa sa s s d n
Proof
  simp[typed_copy_effect_def, venom_state_component_equality] >>
  strip_tac >> simp[gas_marked_path_def] >>
  irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]
QED

Theorem typed_copy_effect_enlarge:
  typed_copy_effect ctx func sa sb s t d n /\
  b <= d /\ d + n <= b + sz ==>
  typed_copy_effect ctx func sa sb s t b sz
Proof
  simp[typed_copy_effect_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem typed_copy_effect_then:
  typed_copy_effect ctx func sa mid s u d n /\
  typed_copy_effect ctx func frame sb u t d n /\
  (!x. not_fresh_at sa x ==> not_fresh_at frame x) ==>
  typed_copy_effect ctx func sa sb s t d n
Proof
  simp[typed_copy_effect_def] >> rpt strip_tac >>
  gvs[venom_state_component_equality] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES,
            arithmeticTheory.LESS_EQ_TRANS]
QED
