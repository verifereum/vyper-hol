(* Fixed origin packets and current observations for linked Array rounds. *)
Theory bodyForArrayOriginMods
Ancestors
  bodyForArrayEntryMods bodyFullPredsMods bodyFullForArrayRound
  vyperStorageTrace vyperStorageFootprint vyperStoragePlaceObserved
  vyperValueOperation vyperState loweringPosts ptrDiscipline
  words list finite_map alist arithmetic

(* The origin packet is exactly the packet used by the existing Entry/Header:
   the capture constructor is retained in the final component of saved. *)
val _ = Parse.hide "body";
Definition for_array_origin_mods_def[nocompute]:
  for_array_origin_mods c cx lo (sty,bd,loc)
    (em,sbExpr,u,Gu,tu) (op,bw) vs (saved,sel) <=>
    ?dw capture. saved = (em,u,Gu,tu,dw,bw,capture) /\
      ?tv. evaluate_type (get_tenv cx) sty = SOME tv /\
      case capture of
        ForArraySlot tr off root path delta =>
          sel = NONE /\ loc = slot_loc tr /\
          bw = n2w off + n2w delta /\
          vs = GENLIST (\i. PlaceR (StoragePlace tr
            ((case bd of Fixed _ => bw | Dynamic _ => bw + 1w) +
             n2w (i * type_slot_size tv)) tv)) (LENGTH vs) /\
          compatible_bound bd (LENGTH vs) /\
          MEM (StorageRoot tr off root) em.storage_trace /\
          storage_subregion root path delta (ArrayTV tv bd)
      | ForArrayOwned av =>
          sel = SOME av /\ loc = LocMemory /\
          value_has_type (ArrayTV tv bd) (ArrayV av) /\
          vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
          ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) op Gu tu u /\
          (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
             val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem) /\
          (0 < type_memory_size (ArrayTV tv bd) ==>
             ?aid b sz. aid < sbExpr.cs_next_id /\
               FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
               b <= w2n bw /\
               w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz /\
               (!nm lb lsz. local_region c em.scopes u nm lb lsz ==>
                  b + sz <= lb \/ lb + lsz <= b))
      | ForArrayHeld name path av =>
          sel = SOME av /\ loc = LocMemory /\
          value_has_type (ArrayTV tv bd) (ArrayV av) /\
          vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
          read_result cx (PlaceR (MemoryPlace name path)) em =
            (INL (ArrayV av),em) /\
          ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) op Gu tu u
      | ForArrayImmutable src name path off itv delta av =>
          loc = LocCode /\
          ?tops. ALOOKUP c.ce_modules src = SOME tops /\
          FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
          ?attrs tail old cap.
            path = MAP AttrSubscript attrs ++ tail /\
            lookup_immutable cx em src name = SOME (itv,old) /\
            evaluate_subscripts itv old (MAP AttrSubscript attrs) =
              INL (ArrayV cap) /\
            evaluate_subscripts itv old path = INL (ArrayV av) /\
            sel = SOME cap /\
          bw = n2w (off + delta) /\
          mem_path_offset itv path = SOME (delta,ArrayTV tv bd) /\
          value_has_type (ArrayTV tv bd) (ArrayV av) /\
          vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
          op_prov Gu op = NONE /\
          w2n bw + type_memory_size (ArrayTV tv bd) < dimword (:256)
End

(* Route is reused verbatim; only the current selected value is observed. *)
Definition for_array_observation_mods_def[nocompute]:
  for_array_observation_mods c cx lo (sty,bd,loc)
    (em,sbExpr,u,Gu,tu) (op,bw) vs (saved,sel) K rs ee G tn t <=>
    ?dw capture. saved = (em,u,Gu,tu,dw,bw,capture) /\
      for_array_entry_route_mods c cx lo (sty,bd,loc)
        (em,sbExpr,u,Gu,tu) (op,bw) vs capture K rs ee G tn t /\
      case capture of
        ForArraySlot _ _ _ _ _ => sel = NONE
      | ForArrayOwned av => sel = SOME av
      | ForArrayHeld name path av =>
          sel = SOME av /\
          ?old entry. lookup_scopes name em.scopes = SOME old /\
            lookup_scopes name ee.scopes = SOME entry /\
            entry.type = old.type
      | ForArrayImmutable src name path off itv delta av =>
          ?attrs tail now cap.
            path = MAP AttrSubscript attrs ++ tail /\
            sel = SOME cap /\
            lookup_immutable cx ee src name = SOME (itv,now) /\
            evaluate_subscripts itv now (MAP AttrSubscript attrs) =
              INL (ArrayV cap) /\
            evaluate_subscripts itv now path = INL (ArrayV av)
End

(* The old Header is retained componentwise; only its Route conjunct is
   replaced by the current observation packet. *)
Definition for_array_origin_header_mods_def[nocompute]:
  for_array_origin_header_mods mods exps
    (DF,lo,d,ctx,func,shadow_func) cx env st0
    (es0,sa0,s0,G0,tn0)
    ((c,id,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     addr_cut,body_cut)
    (em,u,Gu,tu,dw,bw,capture) sel K vs rs ee G tn t <=>
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body)
      (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      addr_cut body_cut /\
    copy_old_operand saL (vv_operand vv) /\
    (!lbl. vv_operand vv <> Label lbl) /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu)
      (xd,dw,capacity,aidItem) vs (vv_operand vv,bw,len_op,idx) cond
      (\K' rs' ee' G' tn' t'.
        for_array_observation_mods c cx lo (sty,bd,loc)
          (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs
          ((em,u,Gu,tu,dw,bw,capture),sel) K' rs' ee' G' tn' t')
      K rs ee G tn t /\
    (rs = vs \/ body_stmts_full_ok_mods mods exps cx loop_body)
End

(* Entry chooses the origin bundle before quantifying over horizons. *)
Definition for_array_origin_entry_mods_def[nocompute]:
  for_array_origin_entry_mods mods exps cx env st0 tyv id body
    (DF,lo,d,ctx,func,shadow_func)
    (es0,sa0,s0,G0,tn0)
    ((c,id0,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     addr_cut,body_cut) h vs ee G tn t <=>
    valid_horizon cx st0 h ee.storage_trace /\
    ?saved sel em u Gu tu dw bw capture.
      saved = (em,u,Gu,tu,dw,bw,capture) /\
      for_array_origin_mods c cx lo (sty,bd,loc)
        (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs (saved,sel) /\
      body_for_full_ok_mods mods exps cx tyv id body vs /\
      (!K. valid_horizon cx st0 K ee.storage_trace ==>
        for_array_origin_header_mods mods exps
          (DF,lo,d,ctx,func,shadow_func) cx env st0
          (es0,sa0,s0,G0,tn0)
          ((c,id0,fty,e,sty,bd,ret_ty,loop_body),
           (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
           (bc,saD,saA,xd,capacity,aidItem),
           (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
           addr_cut,body_cut)
          saved sel K vs vs ee G tn t)
End

Theorem for_array_origin_header_intro_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body)
      (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      addr_cut body_cut /\
  copy_old_operand saL (vv_operand vv) /\
  (!lbl. vv_operand vv <> Label lbl) /\
  for_array_header_mods mods DF lo d ctx func c cx env id st0
    (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu)
    (xd,dw,capacity,aidItem) vs (vv_operand vv,bw,len_op,idx) cond
    (\H rs0 ee0 G0' tn0' t0'.
      for_array_observation_mods c cx lo (sty,bd,loc)
        (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs
        ((em,u,Gu,tu,dw,bw,capture),sel) H rs0 ee0 G0' tn0' t0')
    H0 rs ee G tn t /\
  (rs = vs \/ body_stmts_full_ok_mods mods exps cx loop_body) ==>
  for_array_origin_header_mods mods exps
    (DF,lo,d,ctx,func,shadow_func) cx env st0
    (es0,sa0,s0,G0,tn0)
    ((c,id,fty,e,sty,bd,ret_ty,loop_body),
     (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     addr_cut,body_cut)
    (em,u,Gu,tu,dw,bw,capture) sel H0 vs rs ee G tn t
Proof
  simp[for_array_origin_header_mods_def]
QED
Theorem for_array_origin_entry_elim_mods[local]:
  for_array_origin_entry_mods mods exps cx env st0 tyv id body
    (DF,lo,d,ctx,func,shadow_func)
    (es0,sa0,s0,G0,tn0) layout h vs ee G tn t ==>
  ?saved sel. !K. valid_horizon cx st0 K ee.storage_trace ==>
    for_array_origin_header_mods mods exps
      (DF,lo,d,ctx,func,shadow_func) cx env st0
      (es0,sa0,s0,G0,tn0) layout saved sel K vs vs ee G tn t
Proof
  PairCases_on `layout` >>
  rw[for_array_origin_entry_mods_def] >>
  qexistsl_tac [`(em,u,Gu,tu,dw,bw,capture)`,`sel`] >>
  first_assum ACCEPT_TAC
QED

Theorem for_array_origin_entry_extract_mods:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!h. valid_horizon cx st0 h ee.storage_trace ==>
    for_array_origin_entry_mods mods exps cx env st0 tyv id body
      (DF,lo,d,ctx,func,shadow_func)
      (es0,sa0,s0,G0,tn0) layout h vs ee G tn t) ==>
  ?saved sel. !K. valid_horizon cx st0 K ee.storage_trace ==>
    for_array_origin_header_mods mods exps
      (DF,lo,d,ctx,func,shadow_func) cx env st0
      (es0,sa0,s0,G0,tn0) layout saved sel K vs vs ee G tn t
Proof
  strip_tac >>
  qpat_x_assum `!h. _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  fs[storage_trace_domain_def] >>
  disch_tac >>
  PairCases_on `layout` >>
  qhdtm_x_assum `for_array_origin_entry_mods` mp_tac >>
  rw[for_array_origin_entry_mods_def] >>
  qexistsl_tac [`(em,u,Gu,tu,dw,bw,capture)`,`sel`] >>
  first_assum ACCEPT_TAC
QED
