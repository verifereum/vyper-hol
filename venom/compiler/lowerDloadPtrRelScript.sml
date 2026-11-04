Theory lowerDloadPtrRel
Ancestors
  lowerDloadPtrBoundary lowerDloadPtrTaint lowerDloadPtrStatic
  ptrDiscipline o1PassContract venomState venomExecSemantics
  list pred_set finite_map words

(* The list is ordered current frame first, followed by suspended callers.
   A site identity is its list index together with its original instruction
   ID.  Numeric provenance is resolved through this list, not used as an
   identity: in particular, empty sites may share a base. *)
Datatype:
  dload_reloc_frame = <|
    dr_source : (num, num # num) fmap;
    dr_target : (num, num # num) fmap;
    dr_scratch : num set |>
End

Definition dload_frame_sites_def:
  dload_frame_sites f <=>
    DISJOINT (FDOM f.dr_source) f.dr_scratch /\
    FDOM f.dr_target = FDOM f.dr_source UNION f.dr_scratch /\
    (!id b n. FLOOKUP f.dr_source id = SOME (b,n) ==>
       ?c. FLOOKUP f.dr_target id = SOME (c,n)) /\
    (!id c n. id IN f.dr_scratch /\
       FLOOKUP f.dr_target id = SOME (c,n) ==> n = 32)
End

Definition dload_live_site_def:
  dload_live_site fs owner id b c n <=>
    owner < LENGTH fs /\
    FLOOKUP (EL owner fs).dr_source id = SOME (b,n) /\
    FLOOKUP (EL owner fs).dr_target id = SOME (c,n)
End

(* Separation includes scratch sites on the target side.  Bounds apply to
   empty sites too, but empty intervals impose no separation requirement. *)
Definition dload_live_layout_def:
  dload_live_layout lo sf tf fs <=>
    EVERY dload_frame_sites fs /\ lo <= sf /\ sf <= tf /\
    tf < dimword (:256) /\
    (!k id b n. k < LENGTH fs /\
       FLOOKUP (EL k fs).dr_source id = SOME (b,n) ==>
       lo <= b /\ b+n <= sf) /\
    (!k id b n. k < LENGTH fs /\
       FLOOKUP (EL k fs).dr_target id = SOME (b,n) ==>
       lo <= b /\ b+n <= tf) /\
    (!k j id jd b n c m. k < LENGTH fs /\ j < LENGTH fs /\
       FLOOKUP (EL k fs).dr_source id = SOME (b,n) /\
       FLOOKUP (EL j fs).dr_source jd = SOME (c,m) /\
       (k <> j \/ id <> jd) /\ 0 < n /\ 0 < m ==>
       b+n <= c \/ c+m <= b) /\
    (!k j id jd b n c m. k < LENGTH fs /\ j < LENGTH fs /\
       FLOOKUP (EL k fs).dr_target id = SOME (b,n) /\
       FLOOKUP (EL j fs).dr_target jd = SOME (c,m) /\
       (k <> j \/ id <> jd) /\ 0 < n /\ 0 < m ==>
       b+n <= c \/ c+m <= b)
End

(* Arithmetic is word arithmetic even when an intermediate pointer has
   left its allocation.  Natural interval bounds are consumers' premises. *)
Definition dload_pointer_word_def:
  dload_pointer_word fs (b,n) (c,m) (x:bytes32) y <=>
    n = m /\
    (?owner id. dload_live_site fs owner id b c n) /\
    y = x - n2w b + n2w c
End

Theorem dload_live_layout_empty:
  lo <= f /\ f < dimword (:256) ==>
  dload_live_layout lo f f []
Proof
  simp[dload_live_layout_def]
QED

Theorem dload_frame_sites_empty:
  dload_frame_sites <|dr_source := FEMPTY; dr_target := FEMPTY;
                     dr_scratch := {}|>
Proof
  simp[dload_frame_sites_def]
QED

Theorem dload_live_site_bounds:
  dload_live_layout lo sf tf fs /\
  dload_live_site fs owner id b c n ==>
  lo <= b /\ b+n <= sf /\ lo <= c /\ c+n <= tf
Proof
  simp[dload_live_layout_def, dload_live_site_def] >>
  metis_tac[]
QED

Theorem dload_live_site_positive_identity:
  dload_live_layout lo sf tf fs /\
  dload_live_site fs owner id b c n /\
  dload_live_site fs owner' id' b c' n /\ 0 < n ==>
  owner = owner' /\ id = id'
Proof
  simp[dload_live_layout_def, dload_live_site_def] >>
  strip_tac >>
  qpat_x_assum `!k j id jd b n c m. _` mp_tac >>
  qpat_x_assum `!k j id jd b n c m. _` mp_tac >>
  rpt (disch_then (qspecl_then [`owner`, `owner'`] assume_tac)) >>
  `~(b+n <= b)` by decide_tac >> metis_tac[]
QED

Theorem dload_live_site_target_unique:
  dload_live_site fs owner id b c n /\
  dload_live_site fs owner id b' c' n' ==>
  b = b' /\ c = c' /\ n = n'
Proof
  simp[dload_live_site_def] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]
QED

Theorem dload_pointer_word_resolves:
  dload_pointer_word fs (b,n) (c,m) x y ==>
  ?owner id. dload_live_site fs owner id b c n /\
             m = n /\ y = x - n2w b + n2w c
Proof
  simp[dload_pointer_word_def] >> metis_tac[]
QED

Theorem dload_pointer_word_interval:
  dload_live_layout lo sf tf fs /\
  dload_pointer_word fs (b,n) (c,n) x y /\
  b <= w2n x /\ w2n x <= b+n ==>
  w2n y = c + (w2n x - b)
Proof
  strip_tac >>
  fs[dload_pointer_word_def] >>
  drule_all dload_live_site_bounds >> strip_tac >>
  `w2n x - b + c < dimword (:256)` by
    (fs[dload_live_layout_def] >> decide_tac) >>
  `b < dimword (:256)` by
    (fs[dload_live_layout_def] >> decide_tac) >>
  `w2n (n2w b:bytes32) = b` by simp[] >>
  `(n2w b:bytes32) <=+ x` by simp[WORD_LS] >>
  `w2n (x - n2w b) = w2n x - b` by metis_tac[word_sub_w2n] >>
  `w2n (n2w (w2n x - b):bytes32) = w2n x - b` by
    (simp[] >> decide_tac) >>
  `x - n2w b = (n2w (w2n x - b):bytes32)` by metis_tac[w2n_11] >>
  simp[word_add_n2w, arithmeticTheory.ADD_COMM]
QED

Definition dload_value_word_def:
  dload_value_word fs mask p q (x:bytes32) y <=>
    case (p,q) of
      (NONE,NONE) => word_agree_except mask x y
    | (SOME a,SOME b) => dload_pointer_word fs a b x y
    | _ => F
End

(* Only original variables are quantified: generated temporaries have their
   own phase-local obligations and may be present in the target map. *)
Definition dload_vars_match_def:
  dload_vars_match fs V G H tn un s t <=>
    (!v. v IN V ==>
       FLOOKUP tn.t_var v = FLOOKUP un.t_var v /\
       (lookup_var v s = NONE <=> lookup_var v t = NONE) /\
       (!x y. lookup_var v s = SOME x /\ lookup_var v t = SOME y ==>
          dload_value_word fs (op_taint tn (Var v))
            (FLOOKUP G v) (FLOOKUP H v) x y))
End

(* Agreement is required only on fixed memory and simultaneously live
   original allocations.  Target scratch and returned-callee garbage are
   deliberately not constrained here. *)
Definition dload_memory_match_def:
  dload_memory_match lo fs tn un s t <=>
    (!i. i < lo ==>
       (i IN tn.t_mem <=> i IN un.t_mem) /\
       (i NOTIN tn.t_mem ==>
          read_byte i s.vs_memory = read_byte i t.vs_memory)) /\
    (!owner id b c n k.
       dload_live_site fs owner id b c n /\ k < n ==>
       (b+k IN tn.t_mem <=> c+k IN un.t_mem) /\
       (b+k NOTIN tn.t_mem ==>
          read_byte (b+k) s.vs_memory = read_byte (c+k) t.vs_memory))
End

Theorem dload_vars_match_empty_provenance:
  dload_vars_match [] V FEMPTY FEMPTY tn tn s s
Proof
  simp[dload_vars_match_def, dload_value_word_def, word_agree_except_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dload_memory_match_empty:
  dload_memory_match lo [] tn tn s s
Proof
  simp[dload_memory_match_def, dload_live_site_def]
QED

Theorem dload_matched_operand:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> v IN V) /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) x y
Proof
  Cases_on `op`
  >- (simp[eval_operand_def, op_prov_def, op_taint_def,
           dload_value_word_def, word_agree_except_def] >>
      rpt strip_tac >> gvs[])
  >- (simp[eval_operand_def, op_prov_def, dload_vars_match_def] >>
      metis_tac[]) >>
  simp[eval_operand_def, op_prov_def, op_taint_def] >>
  rpt strip_tac >> gvs[] >>
  simp[dload_value_word_def, word_agree_except_def]
QED

Theorem dload_matched_operand_defined:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> v IN V) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def, dload_vars_match_def] >>
  metis_tac[]
QED

Theorem dload_live_layout_allocas_from:
  dload_live_layout lo sf tf fs /\ k < LENGTH fs /\
  t.vs_allocas = (EL k fs).dr_target ==>
  allocas_from lo t
Proof
  simp[dload_live_layout_def, allocas_from_def] >> metis_tac[]
QED

(* Entry to a callee retains ancestor scratch displacement even though the
   new frame's allocation tables (and scratch set) are empty.  A global
   frontier budget therefore cannot count only current-frame scratch. *)
Theorem dload_callee_inherits_frontier_gap:
  ~NULL fn.fn_blocks /\
  setup_callee fn [] (s with vs_alloca_next := 0) = SOME cs /\
  setup_callee fn [] (s with vs_alloca_next := 32) = SOME ct ==>
  cs.vs_allocas = FEMPTY /\ ct.vs_allocas = FEMPTY /\
  ct.vs_alloca_next = cs.vs_alloca_next + 32 /\
  ~(ct.vs_alloca_next <= cs.vs_alloca_next + 32 * CARD (FDOM ct.vs_allocas))
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[]
QED
