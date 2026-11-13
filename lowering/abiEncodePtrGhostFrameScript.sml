(* Spatial caller framing for the combined setup/body/finish endpoint.
   ids contains the output site and the encoder's scratch sites. *)
Theory abiEncodePtrGhostFrame
Ancestors
  exprSimAbiEncodeStateTransport logFieldGhostPtr bodyPtrDefs
  abiEncoderRegisteredEffect abiBuiltinEncodeSetup loweringStateRelDefs
  compileEnv venomState finite_map pred_set arithmetic
  exprSimAbiEncodeCallerFrame exprLoweringProps venomMemDefs

Theorem abi_encode_phases_ghost_transport:
  stmt_state_rel ctx func cenv cx es initial /\
  ghost_inv rb cenv cx es G tn initial /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  st.cs_next_id IN ids /\ FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
  32+w <= outsz /\ alloca_inv actual /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==> FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i b sz. FLOOKUP actual.vs_allocas i = SOME (b,sz) /\
     FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= b) /\
  (!i. i IN ids ==> st.cs_next_id <= i) /\
  (!name entry ptr sz inst.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) /\
  (!i. (!id b sz. id IN ids /\ FLOOKUP actual.vs_allocas id = SOME (b,sz) ==>
       i < b \/ b+sz <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at st x ==>
    lookup_var x actual = lookup_var x initial /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_accounts = initial.vs_accounts /\
  actual.vs_transient = initial.vs_transient ==>
  ghost_inv rb cenv cx es G' tn' actual /\
  ghost_kept cenv es st G tn initial G' tn'
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes initial` by fs[stmt_state_rel_def, state_rel_def] >>
  qabbrev_tac `writes = {i | ?id b sz. id IN ids /\
    FLOOKUP actual.vs_allocas id = SOME (b,sz) /\ b <= i /\ i < b+sz}` >>
  `!name b sz i. local_region cenv es.scopes initial name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes` by
    (suspend "locals") >>
  `!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (simp[Abbr `writes`] >> rpt strip_tac >> first_x_assum irule >>
     rpt strip_tac >> first_x_assum drule_all >> simp[] >> decide_tac) >>
  conj_tac
  >- (irule ghost_inv_exterior_transport >>
      qexistsl [`G`, `func`, `initial`, `st`, `tn`, `writes`] >> simp[] >>
      conj_tac >- metis_tac[] >> rpt strip_tac >> irule abi_encode_separated_interval_frame >>
      qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `abi_encoder_registered_effect ids [] prepared actual` (irule_at Any) >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `i NOTIN writes` mp_tac >>
      simp[Abbr `writes`] >> disch_then drule_all >> simp[] >> decide_tac) >>
  simp_tac bool_ss [ghost_kept_def] >> conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  suspend "rows"
QED

Resume abi_encode_phases_ghost_transport[locals]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [local_region_def] >> strip_tac >> gvs[] >>
  `!id q k. id IN ids /\ FLOOKUP actual.vs_allocas id = SOME (q,k) ==>
    w2n w' + sz <= q \/ q+k <= w2n w'` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_local_ptr_separation >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[Abbr `writes`] >> rpt gen_tac >> strip_tac >>
  Cases_on `id IN ids` >> simp[] >>
  qpat_x_assum `!id q k. _` drule_all >> decide_tac
QED

Resume abi_encode_phases_ghost_transport[rows]:
  rpt gen_tac >> strip_tac >>
  `i NOTIN writes` by
    (simp[Abbr `writes`] >> rpt gen_tac >> strip_tac >>
     Cases_on `id IN ids` >> simp[] >>
     `st.cs_next_id <= id` by metis_tac[] >>
     `aid <> id` by decide_tac >>
     `FLOOKUP actual.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     qpat_x_assum `alloca_inv actual` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >> strip_tac >>
     first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Finalise abi_encode_phases_ghost_transport
