Theory lowerDloadPtrRel
Ancestors
  lowerDloadPtrBoundary lowerDloadPtrTaint lowerDloadPtrStatic lowerDloadDefs
  ptrDiscipline o1PassContract unitTransformDefs venomState venomExecSemantics
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
  dload_vars_match fs V FEMPTY FEMPTY tn tn s s
Proof
  simp[dload_vars_match_def, dload_value_word_def, word_agree_except_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dload_memory_match_empty:
  (!f. MEM f fs ==> f.dr_source = FEMPTY) ==>
  dload_memory_match lo fs tn tn s s
Proof
  simp[dload_memory_match_def, dload_live_site_def] >>
  rpt strip_tac >>
  `MEM (EL owner fs) fs` by simp[EL_MEM] >>
  first_x_assum drule >> strip_tac >> gvs[]
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

(* Paired state lists are current state followed by suspended callers.
   Each saved caller's frontier gap counts exactly its own suffix: younger
   allocations disappear when that caller resumes. *)
Definition dload_table_stack_def:
  dload_table_stack fs ss ts <=>
    LENGTH fs = LENGTH ss /\ LENGTH fs = LENGTH ts /\
    (!k. k < LENGTH fs ==>
       (EL k fs).dr_source = (EL k ss).vs_allocas /\
       (EL k fs).dr_target = (EL k ts).vs_allocas /\
       (EL k ts).vs_alloca_next = (EL k ss).vs_alloca_next +
         32 * SUM (MAP (\f. CARD f.dr_scratch) (DROP k fs)))
End

Theorem dload_table_stack_initial:
  s.vs_allocas = FEMPTY ==>
  dload_table_stack
    [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
    [s] [s]
Proof
  simp[dload_table_stack_def] >> rpt strip_tac >>
  `k = 0` by decide_tac >> gvs[]
QED

Theorem dload_table_stack_current:
  dload_table_stack (f::fs) (s::ss) (t::ts) ==>
  f.dr_source = s.vs_allocas /\ f.dr_target = t.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next +
    32 * SUM (MAP (\f. CARD f.dr_scratch) (f::fs))
Proof
  simp[dload_table_stack_def] >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem dload_table_stack_saved:
  dload_table_stack fs ss ts /\ k < LENGTH fs ==>
  (EL k fs).dr_source = (EL k ss).vs_allocas /\
  (EL k fs).dr_target = (EL k ts).vs_allocas /\
  (EL k ts).vs_alloca_next = (EL k ss).vs_alloca_next +
    32 * SUM (MAP (\f. CARD f.dr_scratch) (DROP k fs))
Proof
  simp[dload_table_stack_def]
QED

Theorem dload_live_layout_initial:
  lo <= f /\ f < dimword (:256) ==>
  dload_live_layout lo f f
    [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
Proof
  simp[dload_live_layout_def, dload_frame_sites_empty] >>
  rpt strip_tac >>
  `k = 0` by decide_tac >> gvs[]
QED

(* Control is witnessed by the same supply-threaded function transform,
   including the supplies at the beginning of this block and instruction.
   phase=0 is an original boundary; positive phases can occur only inside
   a genuine multi-instruction DLOAD/DLOADBYTES expansion. *)
Definition dload_control_match_def:
  dload_control_match supply fn gn s t inst emitted phase <=>
    (?supply'. lower_dload_function_supply supply fn = (gn,supply')) /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    ?bi bb bs before is after.
      bi < LENGTH fn.fn_blocks /\ bb = EL bi fn.fn_blocks /\
      bb.bb_label = s.vs_current_bb /\
      bs = SND (lower_dload_blocks_supply supply (TAKE bi fn.fn_blocks)) /\
      s.vs_inst_idx < LENGTH bb.bb_instructions /\
      inst = EL s.vs_inst_idx bb.bb_instructions /\
      lower_dload_insts_supply bs (TAKE s.vs_inst_idx bb.bb_instructions) =
        (before,is) /\
      lower_dload_inst_supply is inst = (emitted,after) /\
      phase < LENGTH emitted /\
      t.vs_inst_idx = LENGTH before + phase /\
      active_inst fn inst s /\ active_inst gn (EL phase emitted) t /\
      (phase <> 0 ==>
        (inst.inst_opcode = DLOAD /\ LENGTH emitted = 4) \/
        (inst.inst_opcode = DLOADBYTES /\ LENGTH emitted = 2))
End

Theorem dload_control_match_expansion:
  dload_control_match supply fn gn s t inst emitted phase ==>
  ?is after. lower_dload_inst_supply is inst = (emitted,after) /\
             phase < LENGTH emitted /\
             active_inst gn (EL phase emitted) t
Proof
  simp[dload_control_match_def] >> metis_tac[]
QED

Theorem dload_control_match_boundary:
  dload_control_match supply fn gn s t inst emitted 0 ==>
  active_inst fn inst s /\ active_inst gn (HD emitted) t
Proof
  simp[dload_control_match_def] >> rpt strip_tac >>
  Cases_on `emitted` >> gvs[]
QED

Theorem dload_control_match_phase:
  dload_control_match supply fn gn s t inst emitted phase /\ phase <> 0 ==>
  (inst.inst_opcode = DLOAD /\ phase < 4) \/
  (inst.inst_opcode = DLOADBYTES /\ phase < 2)
Proof
  simp[dload_control_match_def] >> metis_tac[]
QED

Theorem dload_initial_components:
  o1_run_state_ok vs ==>
  dload_table_stack
    [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
    [vs] [vs] /\
  dload_vars_match
    [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
    V FEMPTY FEMPTY entry_taint entry_taint vs vs /\
  dload_memory_match lo
    [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
    entry_taint entry_taint vs vs
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  simp[dload_table_stack_initial, dload_vars_match_empty_provenance,
       dload_memory_match_empty]
QED

Theorem scalar_operand_equal:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> v IN V) /\
  op_prov G op = NONE /\ op_taint tn op = {} /\
  (eval_operand op s = NONE <=> eval_operand op t = NONE) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> Cases_on `eval_operand op s` >- gvs[] >>
  Cases_on `eval_operand op t` >- gvs[] >>
  `dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) x x'` by
    (irule dload_matched_operand >> qexistsl [`V`,`s`,`t`,`un`] >> simp[]) >>
  Cases_on `op_prov H op` >>
  gvs[dload_value_word_def, word_agree_except_bits] >>
  simp[fcpTheory.CART_EQ] >> metis_tac[]
QED

Theorem dload_value_access_containment:
  dload_live_layout lo sf tf fs /\ dload_value_word fs {} p q x y /\ rz <> 0 /\
  ((lo < w2n x + rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n x /\ w2n x + rz <= b+n) ==>
  ((lo < w2n y + rz \/ q <> NONE) ==>
    ?c n. q = SOME (c,n) /\ c <= w2n y /\ w2n y + rz <= c+n)
Proof
  `!a b:bytes32. word_agree_except {} a b <=> a = b` by
    simp[word_agree_except_bits, fcpTheory.CART_EQ] >>
  Cases_on `p` >> Cases_on `q` >>
  simp[dload_value_word_def] >> rpt strip_tac
  >- gvs[] >>
  PairCases_on `x'` >> PairCases_on `x''` >> gvs[] >>
  rename1 `dload_pointer_word fs (b,n) (c,m) x y` >>
  `m = n` by metis_tac[dload_pointer_word_resolves] >> gvs[] >>
  `w2n x <= b+m` by decide_tac >>
  drule_all dload_pointer_word_interval >> strip_tac >>
  decide_tac
QED
