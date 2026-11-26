(* A single capture descriptor feeds both header installation and the
   rounds invariant. Only the observation of its backing may change. *)
Theory bodyForArrayEntryMods
Ancestors
  bodyForArrayHeaderMods bodyFullForArrayRound exprSimCopy bodyPtrDefs
  vyperStorageTrace vyperStorageFootprint vyperStoragePlaceRegion
  vyperStoragePlaceObserved vyperValueOperation vyperState loweringPosts
  ptrDiscipline words list finite_map alist

Datatype:
  for_array_capture = ForArraySlot bool num type_value (subscript list) num
                    | ForArrayOwned array_value
                    | ForArrayHeld identifier (subscript list) array_value
                    | ForArrayImmutable (num option) identifier
                         (subscript list) num type_value num array_value
End

(* The memory copy consumes robust bytes now, and the pointer certificate
   at the original length endpoint. The header below connects provenance. *)
Definition for_array_memory_backing_mods_def[nocompute]:
  for_array_memory_backing_mods cx sty bd tv av op bw (u,Gu,tu) (t,tn) <=>
    ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) op Gu tu u /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem)
End

Definition for_array_entry_route_mods_def[nocompute]:
  for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
      (op,bw) vs capture H (rs : eval_result list) ee G tn t <=>
    eval_operand op u = SOME bw /\ op_prov G op = op_prov Gu op /\
    ?tv. evaluate_type (get_tenv cx) sty = SOME tv /\
      case capture of
        ForArraySlot tr off root path delta =>
          loc = slot_loc tr /\ bw = n2w off + n2w delta /\
          vs = GENLIST (\i. PlaceR (StoragePlace tr
            ((case bd of Fixed _ => bw | Dynamic _ => bw + 1w) +
             n2w (i * type_slot_size tv)) tv)) (LENGTH vs) /\
          compatible_bound bd (LENGTH vs) /\
          MEM (StorageRoot tr off root) em.storage_trace /\
          storage_subregion root path delta (ArrayTV tv bd) /\
          (?extra. ee.storage_trace = em.storage_trace ++ extra) /\
          storage_place_observed H (StoragePlace tr bw (ArrayTV tv bd))
      | ForArrayOwned av =>
          loc = LocMemory /\ value_has_type (ArrayTV tv bd) (ArrayV av) /\
          vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
          for_array_memory_backing_mods cx sty bd tv av op bw (u,Gu,tu) (t,tn) /\
          (0 < type_memory_size (ArrayTV tv bd) ==>
            ?aid b sz. aid < sbExpr.cs_next_id /\
              FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
              FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
              b <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= b+sz /\
              (!nm lb lsz. local_region c em.scopes u nm lb lsz ==>
                b+sz <= lb \/ lb+lsz <= b) /\
              (!nm lb lsz. local_region c ee.scopes t nm lb lsz ==>
                b+sz <= lb \/ lb+lsz <= b))
      | ForArrayHeld name path av =>
          loc = LocMemory /\ value_has_type (ArrayTV tv bd) (ArrayV av) /\
          vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
          read_result cx (PlaceR (MemoryPlace name path)) em = (INL (ArrayV av),em) /\
          read_result cx (PlaceR (MemoryPlace name path)) ee = (INL (ArrayV av),ee) /\
          for_array_memory_backing_mods cx sty bd tv av op bw (u,Gu,tu) (t,tn) /\
          (0 < type_memory_size (ArrayTV tv bd) ==>
            ?b sz. local_region c ee.scopes t name b sz /\
              b <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= b+sz)
      | ForArrayImmutable src name path off itv delta av =>
          loc = LocCode /\ (?tops. ALOOKUP c.ce_modules src = SOME tops) /\
          FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
          bw = n2w (off + delta) /\ mem_path_offset itv path = SOME (delta,ArrayTV tv bd) /\
          (?old. lookup_immutable cx em src name = SOME (itv,old) /\
                 evaluate_subscripts itv old path = INL (ArrayV av)) /\
          (?now. lookup_immutable cx ee src name = SOME (itv,now) /\
                 evaluate_subscripts itv now path = INL (ArrayV av)) /\
          value_has_type (ArrayTV tv bd) (ArrayV av) /\
          vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
          op_prov Gu op = NONE /\ op_prov G op = NONE /\
          w2n bw + type_memory_size (ArrayTV tv bd) < dimword (:256) /\
          (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo /\
            !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                  val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem) /\
          (~c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= LENGTH t.vs_data_section /\
            val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) t.vs_data_section)
End

(* The compiler arguments are exactly the cuts of for_nonslot_layout.
   u/Gu/tu are taken at saL, i.e. after length acquisition, not at the
   raw expression endpoint. This same packet is used as rs shrinks. *)
Definition for_array_entry_header_mods_def[nocompute]:
  for_array_entry_header_mods mods (DF,lo,d,ctx,func,shadow_func) cx env st0
      (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       (bc,saD,saA,xd,capacity,aidItem),
       (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
       addr_cut,body_cut)
      (em,u,Gu,tu,dw,bw,capture) H vs rs ee G tn t <=>
    for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
      (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
      (bc,saD,saA,xd,capacity,aidItem)
      (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
      addr_cut body_cut /\
    copy_old_operand saL (vv_operand vv) /\ (!lbl. vv_operand vv <> Label lbl) /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,aidItem)
      vs (vv_operand vv,bw,len_op,idx) cond
      (for_array_entry_route_mods c cx lo (sty,bd,loc) (em,sbExpr,u,Gu,tu)
         (vv_operand vv,bw) vs capture) H rs ee G tn t
End

Definition for_array_entry_mods_def[nocompute]:
  for_array_entry_mods mods machine cx env st0 outer layout H vs ee G tn t <=>
    valid_horizon cx st0 H ee.storage_trace /\
    for_array_saved_entry_mods cx st0
      (\saved K vs. for_array_entry_header_mods mods machine cx env st0 outer layout
                     saved K vs vs) vs ee G tn t
End

Theorem for_array_header_route_mods:
  for_array_header_mods mods DF lo d ctx func c cx env id st0
    outer capture item vs operands cond Route H rs ee G tn t ==>
  Route H rs ee G tn t
Proof
  PairCases_on `outer` >> PairCases_on `capture` >> PairCases_on `operands` >>
  simp[for_array_header_mods_def]
QED

Theorem for_array_entry_saved_mods:
  valid_horizon cx st0 H ee.storage_trace /\
  (!K. valid_horizon cx st0 K ee.storage_trace ==>
       for_array_entry_header_mods mods machine cx env st0 outer layout
         saved K vs vs ee G tn t) ==>
  for_array_entry_mods mods machine cx env st0 outer layout H vs ee G tn t
Proof
  simp[for_array_entry_mods_def, for_array_saved_entry_mods_def] >>
  rpt strip_tac >> qexists_tac `saved` >> first_assum ACCEPT_TAC
QED

Theorem for_array_entry_extract_mods:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       for_array_entry_mods mods machine cx env st0 outer layout H vs ee G tn t) ==>
  ?saved. !K. valid_horizon cx st0 K ee.storage_trace ==>
    for_array_entry_header_mods mods machine cx env st0 outer layout
      saved K vs vs ee G tn t
Proof
  simp[for_array_entry_mods_def] >> strip_tac >>
  drule_all for_array_saved_entry_extract_mods >> simp[]
QED
