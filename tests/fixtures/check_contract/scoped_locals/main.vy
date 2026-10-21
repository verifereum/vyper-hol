import lib as alias

@external
@pure
def f() -> uint256:
    s: uint256 = 0
    for i: int128 in range(2):
        s += 1
    for i: uint256 in range(3):
        s += i
    return s

@external
@pure
def branches(flag: bool) -> uint256:
    if flag:
        value: int128 = -1
        assert value < 0
    else:
        value: uint256 = 2
        assert value > 0
    return 3

@external
@pure
def nested(flag: bool) -> uint256:
    total: uint256 = 0
    if flag:
        value: int128 = -1
        for i: uint256 in range(2):
            assert value < 0
            total += i
    else:
        for value: uint256 in range(3):
            if value > 0:
                total += value
    value: uint256 = 4
    return total + value

@external
@pure
def nominal(flag: bool, point: alias.Point, role: alias.Roles) -> uint256:
    if flag:
        value: alias.Point = point
        assert value.x == point.x
    else:
        value: alias.Roles = role
        assert value == role
    value: alias.Point = point
    for i: uint256 in range(2):
        other: alias.Point = value
        assert other.x == value.x
    other: alias.Roles = role
    assert other == role
    return value.x
