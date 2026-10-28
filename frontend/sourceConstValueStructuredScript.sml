Theory sourceConstValueStructured
Ancestors
  sourceConstValue sourceConstAST list pair

(* Structured opt-in API. The primitive sourceConstValue$source_const_reify
   and all its existing context-free certificates remain unchanged. *)

(* Independent of the generated expression. A fixed array's source length is
   its logical length, NOT the number of non-default sparse entries. *)
Definition source_const_structured_represents_def:
  source_const_structured_represents nominal (SCV_List ss) v =
    (?tv bd vs. LIST_REL (source_const_structured_represents nominal) ss vs /\
       compatible_bound bd (LENGTH vs) /\
       v = ArrayV (make_array_value tv bd vs)) /\
  source_const_structured_represents nominal (SCV_Tuple ss) v =
    (?vs. LIST_REL (source_const_structured_represents nominal) ss vs /\
       v = ArrayV (TupleV vs)) /\
  source_const_structured_represents nominal (SCV_Struct path fields) v =
    (?(sid:nsid) vs. FLOOKUP nominal path = SOME sid /\
       LIST_REL (source_const_structured_represents nominal) (MAP SND fields) vs /\
       v = StructV (ZIP (MAP FST fields,vs))) /\
  source_const_structured_represents nominal sv v = source_const_represents sv v
Termination
  WF_REL_TAC `measure (\(_,sv,_). source_const_value_size sv)` >>
  rpt strip_tac >> simp[] >>
  gvs[MEM_MAP] >>
  TRY (Induct_on `ss` >> simp[] >> rpt strip_tac >> gvs[] >> res_tac >> simp[] >> NO_TAC) >>
  Induct_on `fields` >> simp[] >> Cases_on `h` >>
  simp[basicSizeTheory.pair_size_def] >> rpt strip_tac >> gvs[] >> res_tac >> simp[]
End

Definition source_const_reify_many_def:
  source_const_reify_many f ts ss =
    if LENGTH ts = LENGTH ss then
      OPT_MMAP (\(t,s). f t s) (ZIP (ts,ss))
    else NONE
End

(* Nominal identities come from resolution, never guessed from source paths.
   Carrying the value is internal bookkeeping, not the representation relation. *)
Definition source_const_reify_step_def:
  source_const_reify_step f nominal tenv ty sv =
    if ~well_formed_type tenv ty \/ ~source_const_value_ok sv then NONE else
    case sv of
    | SCV_List ss =>
        (case ty of
         | ArrayT et bd =>
           if compatible_bound bd (LENGTH ss) then
             (case (evaluate_type tenv et,
                    source_const_reify_many f (REPLICATE (LENGTH ss) et) ss) of
              | (SOME tv,SOME ps) =>
                  SOME (Builtin ty (MakeArray (SOME et) bd) (MAP FST ps),
                        ArrayV (make_array_value tv bd (MAP SND ps)))
              | _ => NONE)
           else NONE
         | _ => NONE)
    | SCV_Tuple ss =>
        (case ty of
         | TupleT ts =>
             (case source_const_reify_many f ts ss of
              | SOME ps =>
                  SOME (Builtin ty (MakeArray NONE (Fixed (LENGTH ss)))
                          (MAP FST ps), ArrayV (TupleV (MAP SND ps)))
              | NONE => NONE)
         | _ => NONE)
    | SCV_Struct path fields =>
        (case (FLOOKUP nominal path,ty) of
         | (SOME sid,StructT expected) =>
           if sid = expected then
             (case FLOOKUP tenv sid of
              | SOME (StructArgs args) =>
                if MAP FST fields = MAP FST args then
                  (case source_const_reify_many f (MAP SND args) (MAP SND fields) of
                   | SOME ps =>
                       SOME (StructLit ty sid (ZIP (MAP FST fields,MAP FST ps)),
                             StructV (ZIP (MAP FST fields,MAP SND ps)))
                   | NONE => NONE)
                else NONE
              | _ => NONE)
           else NONE
         | _ => NONE)
    | _ =>
        (case sourceConstValue$source_const_reify tenv ty sv of
         | SOME e =>
             (case source_const_value_literal sv of
              | SOME lit => SOME (e,evaluate_literal lit)
              | NONE => NONE)
         | NONE => NONE)
End

Definition source_const_reify_fuel_def:
  source_const_reify_fuel 0 nominal tenv ty sv = NONE /\
  source_const_reify_fuel (SUC n) nominal tenv ty sv =
    source_const_reify_step (source_const_reify_fuel n nominal tenv)
      nominal tenv ty sv
End

Definition source_const_reify_def:
  source_const_reify nominal tenv ty sv =
    OPTION_MAP FST
      (source_const_reify_fuel (SUC (source_const_value_size sv)) nominal tenv ty sv)
End
