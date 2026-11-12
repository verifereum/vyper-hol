Theory bodyPtrPrecompileBuiltinsPayloadCompose
Ancestors bodyPtrPrecompileBuiltinsPayloadRuns exprLoweringProps venomState

Theorem payload_reset_trans:
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u ==>
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >>
  qpat_x_assum `_ = u`
    (mp_tac o Q.AP_TERM `\z. z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>`) >>
  simp[]
QED

Theorem payload_run_frame_compose:
  run_inst_seq xs s = OK u /\ run_inst_seq ys u = OK t /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
  (!x. P x ==> lookup_var x u = lookup_var x s) /\
  (!x. Q x ==> lookup_var x t = lookup_var x u) /\
  (!x. P x ==> Q x) ==>
  run_inst_seq (xs ++ ys) s = OK t /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. P x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `run_inst_seq xs s = OK u`
        (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  conj_tac >- (irule payload_reset_trans >> metis_tac[]) >>
  metis_tac[]
QED
