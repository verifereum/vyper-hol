(* Residual DSE frames. Variables are compared separately; all control,
   four FMP fields and the alloca bump pointer were already ignored.
   A single-space mask erases ONLY that address space; the combined mask
   erases all three. Allocation maps and all other/future fields are retained.
   TOP-LEVEL: dse_frame, dse_all_frame; reconstruction/update boundaries. *)
Theory deadStoreElimFrame
Ancestors
  venomState venomEffects finite_map

Definition dse_frame_def:
  dse_frame (space:addr_space) (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_current_bb := ""; vs_inst_idx := 0;
    vs_prev_bb := NONE; vs_fmp := 0w; vs_call_entry_fmp := 0w;
    vs_initial_fmp := 0w; vs_return_pc_token := 0w; vs_alloca_next := 0;
    vs_memory := (if space = AddrSp_Memory then [] else s.vs_memory);
    vs_transient := (if space = AddrSp_Transient then K (K 0w) else s.vs_transient);
    vs_accounts := (if space = AddrSp_Storage then K ARB else s.vs_accounts) |>
End

Definition dse_all_frame_def:
  dse_all_frame (s:venom_state) = s with <|
    vs_vars := FEMPTY; vs_current_bb := ""; vs_inst_idx := 0;
    vs_prev_bb := NONE; vs_fmp := 0w; vs_call_entry_fmp := 0w;
    vs_initial_fmp := 0w; vs_return_pc_token := 0w; vs_alloca_next := 0;
    vs_memory := []; vs_transient := K (K 0w); vs_accounts := K ARB |>
End

(* Project fields with a cached, goal-only simpset.  Avoid the standard
   record-update normalizer, including for nested frames and erased updates. *)
val dse_frame_eq_reconstruct_simp = let
  val projection_ss = bool_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM]
  val accessors = map (rator o lhs o concl o SPEC_ALL)
    (CONJUNCTS venom_state_accessors)
  fun projections def = map
    (SIMP_RULE projection_ss [] o (fn acc => AP_TERM acc (SPEC_ALL def)))
    accessors
  val ss = bool_ss ++ rewrites
    (projections dse_frame_def @ projections dse_all_frame_def @
     [update_var_def, venom_state_component_equality, venom_state_accfupds,
      combinTheory.K_THM, TypeBase.distinct_of ``:addr_space``])
in simp_tac ss [] end;

Theorem dse_frame_idempotent[simp]:
  dse_frame space (dse_frame space s) = dse_frame space s /\
  dse_all_frame (dse_all_frame s) = dse_all_frame s /\
  dse_all_frame (dse_frame space s) = dse_all_frame s
Proof
  dse_frame_eq_reconstruct_simp
QED

Theorem dse_frame_erased_updates[simp]:
  dse_frame space (s with vs_vars := vars) = dse_frame space s /\
  dse_frame space (s with vs_current_bb := bb) = dse_frame space s /\
  dse_frame space (s with vs_inst_idx := idx) = dse_frame space s /\
  dse_frame space (s with vs_prev_bb := prev) = dse_frame space s /\
  dse_frame space (s with vs_fmp := fmp) = dse_frame space s /\
  dse_frame space (s with vs_call_entry_fmp := entry) = dse_frame space s /\
  dse_frame space (s with vs_initial_fmp := initial) = dse_frame space s /\
  dse_frame space (s with vs_return_pc_token := pc) = dse_frame space s /\
  dse_frame space (s with vs_alloca_next := next) = dse_frame space s /\
  dse_frame space (update_var x v s) = dse_frame space s /\
  dse_frame AddrSp_Memory (s with vs_memory := mem) = dse_frame AddrSp_Memory s /\
  dse_frame AddrSp_Transient (s with vs_transient := ts) = dse_frame AddrSp_Transient s /\
  dse_frame AddrSp_Storage (s with vs_accounts := ac) = dse_frame AddrSp_Storage s
Proof
  dse_frame_eq_reconstruct_simp
QED

Theorem dse_all_frame_erased_updates[simp]:
  dse_all_frame (s with vs_vars := vars) = dse_all_frame s /\
  dse_all_frame (s with vs_current_bb := bb) = dse_all_frame s /\
  dse_all_frame (s with vs_inst_idx := idx) = dse_all_frame s /\
  dse_all_frame (s with vs_prev_bb := prev) = dse_all_frame s /\
  dse_all_frame (s with vs_fmp := fmp) = dse_all_frame s /\
  dse_all_frame (s with vs_call_entry_fmp := entry) = dse_all_frame s /\
  dse_all_frame (s with vs_initial_fmp := initial) = dse_all_frame s /\
  dse_all_frame (s with vs_return_pc_token := pc) = dse_all_frame s /\
  dse_all_frame (s with vs_alloca_next := next) = dse_all_frame s /\
  dse_all_frame (update_var x v s) = dse_all_frame s /\
  dse_all_frame (s with vs_memory := mem) = dse_all_frame s /\
  dse_all_frame (s with vs_transient := ts) = dse_all_frame s /\
  dse_all_frame (s with vs_accounts := ac) = dse_all_frame s
Proof
  dse_frame_eq_reconstruct_simp
QED

Theorem dse_frame_reconstruct:
  (dse_frame space s with <|
    vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb;
    vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_call_entry_fmp;
    vs_initial_fmp := s.vs_initial_fmp; vs_return_pc_token := s.vs_return_pc_token;
    vs_alloca_next := s.vs_alloca_next;
    vs_memory := s.vs_memory; vs_transient := s.vs_transient;
    vs_accounts := s.vs_accounts |>) = s /\
  (dse_all_frame s with <|
    vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb;
    vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_call_entry_fmp;
    vs_initial_fmp := s.vs_initial_fmp; vs_return_pc_token := s.vs_return_pc_token;
    vs_alloca_next := s.vs_alloca_next;
    vs_memory := s.vs_memory; vs_transient := s.vs_transient;
    vs_accounts := s.vs_accounts |>) = s
Proof
  dse_frame_eq_reconstruct_simp
QED

Theorem dse_frame_eq_reconstruct:
  dse_frame space s1 = dse_frame space s2 <=>
  (s1 with <|
    vs_vars := s2.vs_vars; vs_current_bb := s2.vs_current_bb;
    vs_inst_idx := s2.vs_inst_idx; vs_prev_bb := s2.vs_prev_bb;
    vs_fmp := s2.vs_fmp; vs_call_entry_fmp := s2.vs_call_entry_fmp;
    vs_initial_fmp := s2.vs_initial_fmp; vs_return_pc_token := s2.vs_return_pc_token;
    vs_alloca_next := s2.vs_alloca_next;
    vs_memory := (if space = AddrSp_Memory then s2.vs_memory else s1.vs_memory);
    vs_transient := (if space = AddrSp_Transient then s2.vs_transient else s1.vs_transient);
    vs_accounts := (if space = AddrSp_Storage then s2.vs_accounts else s1.vs_accounts) |>) = s2
Proof
  dse_frame_eq_reconstruct_simp >>
  Cases_on `space` >> dse_frame_eq_reconstruct_simp
QED

Theorem dse_all_frame_eq_reconstruct:
  dse_all_frame s1 = dse_all_frame s2 <=>
  (s1 with <|
    vs_vars := s2.vs_vars; vs_current_bb := s2.vs_current_bb;
    vs_inst_idx := s2.vs_inst_idx; vs_prev_bb := s2.vs_prev_bb;
    vs_fmp := s2.vs_fmp; vs_call_entry_fmp := s2.vs_call_entry_fmp;
    vs_initial_fmp := s2.vs_initial_fmp; vs_return_pc_token := s2.vs_return_pc_token;
    vs_alloca_next := s2.vs_alloca_next;
    vs_memory := s2.vs_memory; vs_transient := s2.vs_transient;
    vs_accounts := s2.vs_accounts |>) = s2
Proof
  dse_frame_eq_reconstruct_simp
QED

Theorem dse_frame_all:
  dse_frame space s1 = dse_frame space s2 <=>
  dse_all_frame s1 = dse_all_frame s2 /\
  (space <> AddrSp_Memory ==> s1.vs_memory = s2.vs_memory) /\
  (space <> AddrSp_Transient ==> s1.vs_transient = s2.vs_transient) /\
  (space <> AddrSp_Storage ==> s1.vs_accounts = s2.vs_accounts)
Proof
  dse_frame_eq_reconstruct_simp >>
  Cases_on `space` >> dse_frame_eq_reconstruct_simp >>
  EQ_TAC >> strip_tac >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem dse_frame_projection:
  (!s. project (dse_frame space s) = project s) /\
  dse_frame space s1 = dse_frame space s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem dse_all_frame_projection:
  (!s. project (dse_all_frame s) = project s) /\
  dse_all_frame s1 = dse_all_frame s2 ==> project s1 = project s2
Proof
  metis_tac[]
QED

Theorem dse_frame_update:
  (!s. dse_frame space (update s) = update_frame (dse_frame space s)) /\
  dse_frame space s1 = dse_frame space s2 ==>
  dse_frame space (update s1) = dse_frame space (update s2)
Proof
  metis_tac[]
QED

Theorem dse_all_frame_update:
  (!s. dse_all_frame (update s) = update_frame (dse_all_frame s)) /\
  dse_all_frame s1 = dse_all_frame s2 ==>
  dse_all_frame (update s1) = dse_all_frame (update s2)
Proof
  metis_tac[]
QED
