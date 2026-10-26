(* Precise ABI scratch frames from the existing live-local invariant.
   Applies to fresh and reused temporary allocations, independently of their
   runtime allocation order. Site/output ownership is supplied by generated code. *)
Theory abiCallerLocalScratch
Ancestors
  abiDecoderFootprint abiDecoderFrame localPtrsProps compileEnv venomMemDefs
  venomState venomInst venomWf finite_map pred_set list arithmetic

Theorem abi_caller_local_end:
  local_ptrs_rel func ce scopes s /\ local_region ce scopes s name lo sz ==>
  lo + sz <= s.vs_alloca_next
Proof
  rw[local_region_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem abi_caller_local_scratch:
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\ local_region ce scopes s name lo sz /\
  FINITE ids /\ s.vs_alloca_next <= b + cap /\
  (!id off len. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q) ==>
  abi_footprint_disjoint lo sz (abi_decoder_child_scratch ids b cap s)
Proof
  strip_tac >> drule_all abi_caller_local_end >> strip_tac >>
  irule abi_decoder_child_scratch_disjoint >> asm_simp_tac (srw_ss()) [] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!id off len. _` drule >> disch_then drule >> strip_tac >> gvs[] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_caller_local_scratch_frame:
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\ local_region ce scopes s name lo sz /\
  FINITE ids /\ s.vs_alloca_next <= b + cap /\
  (!id off len. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q) /\
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t ==>
  mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz s.vs_memory
Proof
  strip_tac >> drule_all abi_caller_local_scratch >> strip_tac >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

Theorem abi_caller_generated_local_scratch:
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\ local_region ce scopes s name lo sz /\
  fresh_vars_wrt st s /\ FINITE ids /\ s.vs_alloca_next <= b + cap /\
  (!id off len. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst k. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [STRING #"%" (toString k)] /\ st.cs_next_var <= k) ==>
  abi_footprint_disjoint lo sz (abi_decoder_child_scratch ids b cap s)
Proof
  strip_tac >>
  `!id off len. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!id off len. _` drule >> disch_then drule >> strip_tac >>
     `not_local_ptr ce scopes (STRING #"%" (toString k))` by
       (mp_tac (Q.SPECL [`func`, `ce`, `scopes`, `st`, `s`, `k`]
         local_ptrs_rel_fresh_not_local_ptr) >> simp[]) >>
     qexistsl_tac [`inst`, `STRING #"%" (toString k)`] >> simp[]) >>
  drule_all abi_caller_local_scratch >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_LOCAL_SCRATCH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller local scratch not kernel closed: " ^ n)
  end) (DB.thms "abiCallerLocalScratch");
