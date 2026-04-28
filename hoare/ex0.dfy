method Triple(x: int) returns (r: int)
  requires true
  ensures r == 3*x
{
    assert x+2*x == 3*x;
    var y := 2*x;
    assert x+y == 3*x;
    r := x + y;
    assert r == 3*x;
}
