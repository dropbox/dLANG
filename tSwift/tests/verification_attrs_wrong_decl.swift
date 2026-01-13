// Test file for verification attributes on wrong declaration types

// @_requires is only for functions - test on var
@_requires("x > 0")
var globalVar = 42

// @_ensures is only for functions - test on struct
@_ensures("self != nil")
struct MyStruct {
    var value: Int
}

// @_invariant is for types/vars - test on function
@_invariant("count >= 0")
func testFunction() -> Int {
    return 1
}
