(* Control-only transport of the actual decoder resource boundary. *)
Theory exprSimAbiDecodeBoundary
Ancestors
  exprSimAbiDecodeBuiltin exprSimAbiGasBridge abiBuiltinDecodeSetup
  actualDecoderSites exprLoweringProps venomMemDefs

Theorem abi_decode_site_resources_current_bb:
  abi_builtin_decode_site_resources ctx func st last mn mx sz cnt p d
    (s with vs_current_bb := L) <=>
  abi_builtin_decode_site_resources ctx func st last mn mx sz cnt p d s
Proof
  simp[abi_builtin_decode_site_resources_def, decode_site_resources_def,
       alloca_room_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def, fmp_room_def, pending_alloca_size_def]
QED

Theorem abi_decode_site_resources_relabel:
  abi_builtin_decode_site_resources ctx func (start_relabel L ids st)
    (start_swap st L ids final).cs_next_id mn mx sz cnt p d
    (s with vs_current_bb := L) <=>
  abi_builtin_decode_site_resources ctx func st final.cs_next_id
    mn mx sz cnt p d s
Proof
  simp[abi_decode_site_resources_current_bb, start_relabel_def,
       start_swap_def, abi_builtin_decode_site_resources_def,
       abi_builtin_decode_output_site_def] >>
  Cases_on `NULL (emitted_blocks st final)` >> simp[]
QED

(* Boundary inventory (proposed signatures, NOT admitted theorems).

   State convention: st is the whole expression start; st1 the child end;
   st2 the unwrap end/decoder start; final the decoder end. s0 is the
   original target state; s2 is the state in the child's expr_post after
   unwrap; es is original source state; es1 includes all child effects.

   Resource boundary proposed for exprSimAbiDecodeResources:
     expr_post ctx func ce cx e es st st2 s0 es1 (BytesV bs) data s2 /\
     evaluate_type (get_tenv cx) (expr_type e) =
       SOME (BaseTV (BytesT (Dynamic n))) /\
     ~is_word_type (expr_type e) /\
     lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
       (abi_static_size ce.ce_struct_fields wty)
       (abi_size_bound ce.ce_struct_fields wty)
       (type_memory_bytes ce wty) st2 = (out,final) /\
     fn_has_code st2 final func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved ce final /\
     abi_size_bound ce.ce_struct_fields wty < dimword (:256) /\
     type_memory_bytes ce wty < dimword (:256)
     ==>
     ?p d. eval_operand data s2 = SOME (n2w p) /\
       val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s2.vs_memory /\
       abi_builtin_decode_site_resources ctx func st2 final.cs_next_id
         (abi_static_size ce.ce_struct_fields wty)
         (abi_size_bound ce.ce_struct_fields wty)
         (type_memory_bytes ce wty) (LENGTH bs) p d s2

   Premise sources: expr_post is unwrap_value_marked_read's result, not
   the child's initial vv_post; bytes typing is parent inversion; code,
   distinctness and reservation follow compile/code invariants; numeric
   bounds require the Entry/alloc_limits boundary, still to be proved.
   Footprint supplies actual p+32+LENGTH bs and provenance. alloca_inv
   bounds old allocation footprints by vs_alloca_next; local case needs
   local_region bound. Existing output d must use recorded (d,outsz),
   justified by literal ALLOCA inclusion and decode_site_resources. Absent
   output chooses vs_alloca_next; alloca_room supplies strict room for its
   pending instruction. Old scratch sites are separated by distinct IDs
   and alloca non-overlap, or reserved locals. No allocation executes here.
   Control transport above certifies exactly the relabeled resource use.

   Post boundary proposed for exprSimAbiDecodeSuccess (abbreviations:
   wty as in dispatch, eout = TypeBuiltin ann (AbiDecode unwrap) ty [e],
   outsz = type_memory_bytes ce wty, root = get_tenv cx):
     expr_post ctx func ce cx e es st st2 s0 es1 (BytesV bs) data s2 /\
     expr_body_pre ce cx env eout es /\ expr_type eout = ty /\
     lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
       (abi_static_size ce.ce_struct_fields wty)
       (abi_size_bound ce.ce_struct_fields wty) outsz st2 = (out,final) /\
     fn_has_code st2 final func /\ local_ptrs_reserved ce final /\
     cs_extends st st2 /\
     abi_decoder_coherent ce root ce.ce_struct_fields wty tv /\
     evaluate_abi_decode root wty bs = INL v /\
     eval_operand out t = SOME (n2w d) /\ val_in_memory tv v d t.vs_memory /\
     decode_site_effect ctx func st2.cs_next_var
       ({a | d <= a /\ a < d+outsz} UNION {a | s2.vs_alloca_next <= a} UNION
        {a | ?id b sz. st2.cs_next_id <= id /\ id < final.cs_next_id /\
            FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b+sz}) s2 t /\
     (!id. id < st2.cs_next_id \/ final.cs_next_id <= id ==>
           FLOOKUP t.vs_allocas id = FLOOKUP s2.vs_allocas id)
     ==>
     ?vout. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e]
              [BytesV bs] = INL vout /\
       vv_post ctx func ce cx eout es st final s0 es1 (Value vout)
         (LocatedValue ty (mk_ptr out LocMemory)) t

   The proposed success boundary requires validation of the LocatedValue
   witness and all frame premises before being used; it is not certified by
   this inventory. stmt_state_rel: static frame plus alloca resources and
   protected local memory. vv_holds/vv_at: source success (including tuple
   unwrapping), decoder memory, recorded output allocation and fresh site
   range. Old vars: child frame composed with live operand preservation.
   Old allocations: child frame composed with decode_site_effect. Old
   memory: outside-site equality plus alloca non-overlap and protected
   locals/new-frontier bound. locals_kept: same regions and memory frame.
   No decoder-internal source state is reset to es. No extra output load.

   Outstanding cursor premise: final.cs_current_insts <> [] OR every
   lookup of final.cs_current_bb in each observer has phi_prefix_length 0.
   Need a decoder-end nonempty theorem (or a genuine phi theorem), not an
   assumed arbitrary continuation property. lower_abi_decode_frag_facts
   alone does not advertise this. Both bridges require this accounting;
   lower_abi_decode_outcome's same-block disjunct only relaxes its own use.
   Post closure elimination is applied after this success boundary, using
   abi_decode_post_closure_vv_post; rejection is independent of target
   fields via abi_decode_rejection_expr_exit.
*)
