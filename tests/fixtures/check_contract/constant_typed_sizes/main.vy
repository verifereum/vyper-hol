# pragma enable-decimals
import lib

static_size: uint256[2 + 1]
bytes_size: Bytes[max_value(uint8) - 252]
string_size: String[floor(2.5) + 1]
dynamic_size: DynArray[uint256, as_wei_value(0.000000002, "gwei") + 1]
selected_size: uint256[[2, 3][1]]
forward_size: uint256[N + 1]
imported_size: uint256[lib.N + 1]
rounded_size: String[ceil(-2.5) + 3]
minmax_size: uint256[min(2, 3) + 1]
named_array_size: uint256[XS[0]]
closed_shift_size: uint256[shift(2, 1)]
imported_struct: lib.Sized

N: constant(uint8) = 2
XS: constant(uint256[1]) = [3]
