(* Allocation-resource projection of the typed-store endpoint frame. *)
Theory typedStoreAllocationFrame
Ancestors
  exprLoweringProps localPtrsProps venomState

Theorem typed_store_frame_allocations:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := bb; vs_inst_idx := k; vs_prev_bb := prev|>) = s ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  disch_tac >>
  conj_tac
  >- (first_x_assum (mp_tac o AP_TERM ``\u:venom_state. u.vs_allocas``) >> simp[]) >>
  first_x_assum (mp_tac o AP_TERM ``\u:venom_state. u.vs_alloca_next``) >> simp[]
QED

Theorem typed_store_frame_resources:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := bb; vs_inst_idx := k; vs_prev_bb := prev|>) = s /\
  alloca_inv s /\ alloca_room ctx fn s ==>
  alloca_inv t /\ alloca_room ctx fn t
Proof
  strip_tac >> drule typed_store_frame_allocations >> strip_tac >>
  metis_tac[alloca_inv_fields, alloca_room_fields]
QED
