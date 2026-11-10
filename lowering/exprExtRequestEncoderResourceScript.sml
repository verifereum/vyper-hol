(* Registered source and destination buffers protect the encoder's reused sites. *)
Theory exprExtRequestEncoderResource
Ancestors
  exprExtRequestEncoderWitness allocaSiteResource exprLoweringProps
  compileEnv venomMemDefs words finite_map pred_set abiEncoderProps

Theorem extrequest_encoder_registered_size:
  compile_abi_encode_to_buf dst src ei st = (len,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx ee s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids st en /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  sz = 32
Proof
  strip_tac >>
  drule_all extrequest_encoder_function_alloca_shape >> strip_tac >>
  fs[stmt_state_rel_def] >>
  first_x_assum drule_all >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem extrequest_encoder_registered_window:
  alloca_inv s /\ owner < st.cs_next_id /\
  FLOOKUP s.vs_allocas owner = SOME (p,n) /\
  p <= q /\ q + k <= p + n /\
  id IN frag_ids st en /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (q,k) (b,sz)
Proof
  strip_tac >>
  `owner <> id` by fs[frag_ids_def] >>
  drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extrequest_encoder_reused_resources:
  compile_abi_encode_to_buf dst src ei st = (len,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx ee s /\
  source_id < st.cs_next_id /\ dest_id < st.cs_next_id /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_size) /\
  FLOOKUP s.vs_allocas dest_id = SOME (dest_base,dest_size) /\
  source_base <= sb /\ sb + cap <= source_base + source_size /\
  dest_base <= d /\ d + n <= dest_base + dest_size ==>
  !inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,n) (b,sz)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >- (drule_all extrequest_encoder_registered_size >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  conj_tac >> irule extrequest_encoder_registered_window >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
