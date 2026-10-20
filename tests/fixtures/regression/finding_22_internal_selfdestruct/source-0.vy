
marker: public(uint256)

@internal
def destroy():
    selfdestruct(0x0000000000000000000000000000000000001234)

@external
def run():
    self.destroy()
    self.marker = 7
