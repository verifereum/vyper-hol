(*
 * Memory Allocator
 *
 * Port of venom/memory_allocator.py for compiler passes.
 *)

Theory memoryAllocator
Ancestors
  list finite_map sorting
  orderedSet basePtrTypes
  venomState

Datatype:
  mem_allocator = <|
    ma_allocated : (allocation, num) fmap;
    ma_mems_used : (string, allocation list) fmap;
    ma_fn_eom : (string, num) fmap;
    ma_allocated_fn : allocation list;
    ma_reserved : (num # num) list;
    ma_current_fn : string option
  |>
End

Definition mem_allocator_init_def:
  mem_allocator_init =
    <| ma_allocated := FEMPTY;
       ma_mems_used := FEMPTY;
       ma_fn_eom := FEMPTY;
       ma_allocated_fn := [];
       ma_reserved := [];
       ma_current_fn := NONE |>
End

Definition mem_allocator_is_allocated_def:
  mem_allocator_is_allocated alloc st <=>
    IS_SOME (FLOOKUP st.ma_allocated alloc)
End

Definition mem_allocator_set_position_def:
  mem_allocator_set_position alloc pos st =
    st with ma_allocated := st.ma_allocated |+ (alloc, pos)
End

Definition sort_reserved_def:
  sort_reserved (resv:(num # num) list) = QSORT (λa b. FST a < FST b) resv
End

Definition find_allocation_ptr_def:
  find_allocation_ptr (alloc_sz:num) (ptr_val:num) [] = ptr_val /\
  find_allocation_ptr alloc_sz ptr_val ((resv_ptr,resv_size)::rest) =
    let resv_end = resv_ptr + resv_size in
    if resv_end <= ptr_val then find_allocation_ptr alloc_sz ptr_val rest
    else if resv_ptr >= ptr_val + alloc_sz then ptr_val
    else find_allocation_ptr alloc_sz resv_end rest
End

Definition mem_allocator_allocate_def:
  mem_allocator_allocate alloc st =
    let alloc_sz = alloc.alloc_size in
    let resv = sort_reserved st.ma_reserved in
    let ptr_val = find_allocation_ptr alloc_sz 0 resv in
    let st' = st with <|
        ma_allocated := st.ma_allocated |+ (alloc, ptr_val);
        ma_allocated_fn := ordset_add alloc st.ma_allocated_fn |>
    in (ptr_val, st')
End

Definition mem_allocator_get_concrete_def:
  mem_allocator_get_concrete st p =
    case (FLOOKUP st.ma_allocated p.ptr_alloca, p.ptr_offset) of
      (SOME base, SOME off) => Lit (n2w (base + off))
    | _ => Lit 0w
End

Definition mem_allocator_start_fn_allocation_def:
  mem_allocator_start_fn_allocation fn st =
    st with <| ma_reserved := []; ma_current_fn := SOME fn; ma_allocated_fn := [] |>
End

Definition mem_allocator_add_allocated_def:
  mem_allocator_add_allocated allocs st =
    st with ma_allocated_fn := ordset_addmany st.ma_allocated_fn allocs
End

Definition mem_allocator_compute_fn_eom_def:
  mem_allocator_compute_fn_eom st =
    FOLDL (λacc alloc.
      case FLOOKUP st.ma_allocated alloc of
        NONE => acc
      | SOME off => MAX acc (off + alloc.alloc_size)) 0 st.ma_allocated_fn
End

Definition mem_allocator_end_fn_allocation_def:
  mem_allocator_end_fn_allocation st =
    case st.ma_current_fn of
      NONE => st
    | SOME fn =>
        let eom = mem_allocator_compute_fn_eom st in
        st with <|
          ma_mems_used := st.ma_mems_used |+ (fn, st.ma_allocated_fn);
          ma_fn_eom := st.ma_fn_eom |+ (fn, eom) |>
End

Definition mem_allocator_reset_def:
  mem_allocator_reset st = st with ma_reserved := []
End

Definition mem_allocator_reserve_def:
  mem_allocator_reserve alloc st =
    case FLOOKUP st.ma_allocated alloc of
      NONE => st
    | SOME ptr_val =>
        st with ma_reserved := ordset_add (ptr_val, alloc.alloc_size) st.ma_reserved
End

Definition mem_allocator_reserve_all_def:
  mem_allocator_reserve_all st =
    FOLDL (λacc alloc. mem_allocator_reserve alloc acc) st st.ma_allocated_fn
End

val _ = export_theory();
